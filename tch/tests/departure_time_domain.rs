// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Integration test checking that queries departing before the start of the TTFs' domain are
//! rejected with an error.
//!
//! Evaluating a TTF before its `start_x` extrapolates it backward, which produces negative travel
//! times. The unpacking time then decreases along the path and eventually falls before the first
//! entry of a `PackedShortcut`, which used to panic in `unpack_edge` (in release mode only: in
//! debug mode a `debug_assert!` in `PwlXYF::eval` catches the backward extrapolation first).
use petgraph::graph::{node_index, DiGraph};
use priority_queue::PriorityQueue;
use tch::hash::HashMap;
use tch::*;
use ttf::{PwlTTF, TTF};

/// The `x` value at which all the TTFs of the test network start.
const START: f64 = 1000.0;

fn get_grid_network(n: usize) -> DiGraph<(), ()> {
    let mut graph = DiGraph::with_capacity(n * n, n * n * 4);
    for _ in 0..n * n {
        graph.add_node(());
    }
    // Add vertical edges.
    for x in 0..n {
        for y in 0..n - 1 {
            let (i, j) = (x + y * n, x + (y + 1) * n);
            graph.add_edge(node_index(i), node_index(j), ());
            graph.add_edge(node_index(j), node_index(i), ());
        }
    }
    // Add horizontal edges.
    for x in 0..n - 1 {
        for y in 0..n {
            let (i, j) = (x + y * n, x + 1 + y * n);
            graph.add_edge(node_index(i), node_index(j), ());
            graph.add_edge(node_index(j), node_index(i), ());
        }
    }
    graph
}

/// Builds the allocation required by `earliest_arrival_query`.
///
/// This is a macro rather than a function because the concrete types of the priority queues and
/// of the node data are not nameable from outside the crate.
macro_rules! new_alloc {
    () => {{
        let forw_search = DijkstraSearch::new(HashMap::default(), PriorityQueue::new());
        let back_search = DijkstraSearch::new(HashMap::default(), PriorityQueue::new());
        let ea_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        let downward_search = DijkstraSearch::new(HashMap::default(), PriorityQueue::new());
        algo::EarliestArrivalAllocation::new(ea_search, downward_search)
    }};
}

/// Builds a hierarchy over a grid network whose edges have time-dependent travel times crossing
/// each other, so that the contraction produces `PackedShortcut` edges.
fn get_time_dependent_overlay(n: usize) -> HierarchyOverlay<f64> {
    let graph = get_grid_network(n);
    // Deterministic pseudo-random profiles that cross each other a lot, so that the shortcuts are
    // packed rather than going through a single middle node.
    let mut seed: u64 = 12345;
    let mut next = move || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((seed >> 33) % 1000) as f64 / 1000.0
    };
    let ttfs: Vec<TTF<f64>> = (0..graph.edge_count())
        .map(|_| {
            let values: Vec<f64> = (0..9).map(|_| 5.0 + 40.0 * next()).collect();
            TTF::Piecewise(PwlTTF::from_values(values, START, 50.))
        })
        .collect();
    HierarchyOverlay::order(
        &graph,
        |e| ttfs[e.index()].clone(),
        ContractionParameters::default(),
    )
}

#[test]
fn min_start_x_is_the_start_of_the_ttfs() {
    let overlay = get_time_dependent_overlay(12);
    assert_eq!(overlay.min_start_x(), Some(START));
}

#[test]
fn departure_time_before_start_x_is_rejected() {
    let n = 12;
    let overlay = get_time_dependent_overlay(n);
    let mut alloc = new_alloc!();
    let mut candidate_map = HashMap::default();

    // A query departing within the domain of the TTFs is answered normally.
    let result = overlay
        .earliest_arrival_query(
            node_index(0),
            node_index(n * n - 1),
            START,
            &mut alloc,
            &mut candidate_map,
        )
        .expect("A query departing at `start_x` must be valid");
    let (arrival_time, route) = result.expect("The destination must be reachable");
    assert!(
        arrival_time > START,
        "The arrival time ({arrival_time}) must be later than the departure time ({START})"
    );
    assert!(!route.is_empty());

    // The same query, departing before the start of the TTFs, is rejected.
    // This used to panic in `unpack_edge` or to return a negative arrival time.
    let error = overlay
        .earliest_arrival_query(
            node_index(0),
            node_index(n * n - 1),
            START - 500.0,
            &mut alloc,
            &mut candidate_map,
        )
        .expect_err("A query departing before `start_x` must be rejected");
    let message = format!("{error:#}");
    assert!(
        message.contains("500") && message.contains("1000"),
        "The error message must report the departure time and the start of the TTFs, got: {message}"
    );

    // Every node pair is rejected, not only the one above.
    for target in 1..n * n {
        assert!(
            overlay
                .earliest_arrival_query(
                    node_index(0),
                    node_index(target),
                    START - 500.0,
                    &mut alloc,
                    &mut candidate_map,
                )
                .is_err(),
            "The query to node {target} must be rejected"
        );
    }
}

#[test]
fn cached_min_start_x_is_not_serialized() {
    // The overlay is written as an output artifact by `routing_cli`, so the cache must not leak
    // into the JSON. It is recomputed after deserialization.
    let overlay = get_time_dependent_overlay(4);
    let json = serde_json::to_string(&overlay).expect("The overlay must be serializable");
    assert!(
        !json.contains("min_start_x"),
        "The cached `min_start_x` must not appear in the serialized overlay"
    );

    let overlay: HierarchyOverlay<f64> =
        serde_json::from_str(&json).expect("The overlay must be deserializable");
    assert_eq!(overlay.min_start_x(), Some(START));
}

#[test]
fn constant_ttfs_have_no_departure_time_constraint() {
    // With constant travel times the `x`-domain is unbounded, so any departure time is valid.
    let n = 6;
    let graph = get_grid_network(n);
    let cst_tt = TTF::Constant(1.0f64);
    let overlay =
        HierarchyOverlay::order(&graph, |_| cst_tt.clone(), ContractionParameters::default());
    assert_eq!(overlay.min_start_x(), None);

    let mut alloc = new_alloc!();
    let mut candidate_map = HashMap::default();
    let (arrival_time, _route) = overlay
        .earliest_arrival_query(
            node_index(0),
            node_index(n * n - 1),
            -1000.0,
            &mut alloc,
            &mut candidate_map,
        )
        .expect("A query on constant TTFs must be valid")
        .expect("The destination must be reachable");
    assert_eq!(arrival_time, -1000.0 + 2.0 * (n - 1) as f64);
}
