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

//! Integration test checking that the arrival time returned by an earliest-arrival query is the
//! arrival time achieved by the returned route.
//!
//! When a shortcut is merged with an original edge, the edge becomes a `PackedShortcut` whose TTF
//! is the minimum of both. Unpacking an original edge of such a pack used to advance the clock
//! with that merged TTF instead of the TTF of the original edge, so the returned arrival time
//! could be earlier than the arrival time of the route.
use petgraph::graph::{node_index, DiGraph};
use priority_queue::PriorityQueue;
use tch::hash::HashMap;
use tch::*;
use ttf::{PwlTTF, TTF};

fn get_grid_network(n: usize) -> DiGraph<(), ()> {
    let mut graph = DiGraph::with_capacity(n * n, n * n * 4);
    for _ in 0..n * n {
        graph.add_node(());
    }
    for x in 0..n {
        for y in 0..n - 1 {
            let (i, j) = (x + y * n, x + (y + 1) * n);
            graph.add_edge(node_index(i), node_index(j), ());
            graph.add_edge(node_index(j), node_index(i), ());
        }
    }
    for x in 0..n - 1 {
        for y in 0..n {
            let (i, j) = (x + y * n, x + 1 + y * n);
            graph.add_edge(node_index(i), node_index(j), ());
            graph.add_edge(node_index(j), node_index(i), ());
        }
    }
    graph
}

/// Deterministic pseudo-random TTFs that cross each other a lot, so that the contraction merges
/// shortcuts with original edges into `PackedShortcut` edges.
fn get_ttfs(nb_edges: usize, seed: u64) -> Vec<TTF<f64>> {
    let mut seed = seed;
    let mut next = move || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((seed >> 33) % 1000) as f64 / 1000.0
    };
    (0..nb_edges)
        .map(|_| {
            let values: Vec<f64> = (0..9).map(|_| 5.0 + 40.0 * next()).collect();
            TTF::Piecewise(PwlTTF::from_values(values, 0.0, 50.))
        })
        .collect()
}

#[test]
fn returned_arrival_time_is_the_arrival_time_of_the_route() {
    let n = 8;
    let graph = get_grid_network(n);
    let mut nb_checked = 0;
    for seed in 0..3 {
        let ttfs = get_ttfs(graph.edge_count(), seed);
        let overlay = HierarchyOverlay::order(
            &graph,
            |e| ttfs[e.index()].clone(),
            ContractionParameters::default(),
        );
        let forw_search = DijkstraSearch::new(HashMap::default(), PriorityQueue::new());
        let back_search = DijkstraSearch::new(HashMap::default(), PriorityQueue::new());
        let ea_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        let downward_search = DijkstraSearch::new(HashMap::default(), PriorityQueue::new());
        let mut alloc = algo::EarliestArrivalAllocation::new(ea_search, downward_search);
        let mut candidate_map = HashMap::default();
        for source in 0..n * n {
            for target in 0..n * n {
                if source == target {
                    continue;
                }
                for k in 0..4 {
                    let departure_time = 7.0 + 86.0 * k as f64;
                    let (arrival_time, route) = overlay
                        .earliest_arrival_query(
                            node_index(source),
                            node_index(target),
                            departure_time,
                            &mut alloc,
                            &mut candidate_map,
                        )
                        .unwrap()
                        .expect("The grid is strongly connected");
                    let route_arrival_time = route
                        .iter()
                        .fold(departure_time, |t, e| t + ttfs[e.index()].eval(t));
                    assert!(
                        (arrival_time - route_arrival_time).abs() < 1e-9,
                        "Seed {seed}, from {source} to {target} at {departure_time}: returned \
                        arrival time {arrival_time}, arrival time of the route \
                        {route_arrival_time}"
                    );
                    nb_checked += 1;
                }
            }
        }
    }
    assert!(nb_checked > 0);
}
