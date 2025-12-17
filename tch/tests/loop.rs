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

//! Integration test for network loops.
use hashbrown::{HashMap, HashSet};
use petgraph::graph::{node_index, DiGraph};
use petgraph::prelude::{EdgeIndex, NodeIndex};
use priority_queue::PriorityQueue;
use tch::*;
use ttf::{PwlTTF, TTF};

/// 0---1---2---4
///  \   \ /
///   ----3
///
/// Edges:
/// 0 -> 1 (0) 5'
/// 1 -> 2 (1) 5', 5', 35', 35'
/// 0 -> 3 (2) 13'
/// 3 -> 1 (3) 1'
/// 2 -> 3 (4) 10'
/// 3 -> 2 (5) 10'
/// 2 -> 4 (6) 1'
fn get_network() -> DiGraph<(), ()> {
    let mut graph = DiGraph::new();
    for _ in 0..5 {
        graph.add_node(());
    }
    graph.add_edge(node_index(0), node_index(1), ());
    graph.add_edge(node_index(1), node_index(2), ());
    graph.add_edge(node_index(0), node_index(3), ());
    graph.add_edge(node_index(3), node_index(1), ());
    graph.add_edge(node_index(2), node_index(3), ());
    graph.add_edge(node_index(3), node_index(2), ());
    graph.add_edge(node_index(2), node_index(4), ());
    graph
}

fn weight_fn(edge_id: EdgeIndex) -> TTF<f64> {
    match edge_id.index() {
        0 => TTF::Constant(5.),
        1 => TTF::Piecewise(PwlTTF::from_values(vec![20., 5., 5., 5.], 0., 30.)),
        2 => TTF::Constant(15.),
        _ => TTF::Constant(1.),
    }
}

fn node_order_fn(node_id: NodeIndex) -> usize {
    match node_id.index() {
        0 => 2,
        1 => 1,
        2 => 0,
        3 => 4,
        4 => 3,
        _ => unreachable!(),
    }
}

#[test]
fn no_loop_test() {
    let graph = get_network();

    let parameters = ContractionParameters::default();

    let ch = HierarchyOverlay::construct(&graph, weight_fn, node_order_fn, parameters);

    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let ea_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let downward_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut ea_alloc = algo::EarliestArrivalAllocation::new(ea_search, downward_search);
    let mut candidate_map = HashMap::new();

    let (_arr_time, path) = ch
        .earliest_arrival_query(
            node_index(0),
            node_index(4),
            21.,
            &mut ea_alloc,
            &mut candidate_map,
        )
        .unwrap()
        .unwrap();

    let nodes: Vec<_> = path
        .into_iter()
        .map(|e| graph.edge_endpoints(e).unwrap().1)
        .collect();
    let unique_nodes: HashSet<_> = nodes.iter().copied().collect();
    assert_eq!(nodes.len(), unique_nodes.len());
}
