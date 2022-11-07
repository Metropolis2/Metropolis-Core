use hashbrown::HashMap;
use petgraph::graph::{edge_index, node_index, DiGraph, EdgeReference};
use petgraph::visit::EdgeRef;
use priority_queue::PriorityQueue;
use tch::ops::ScalarDijkstra;
use tch::*;
use ttf::{PwlTTF, TTF};

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

#[test]
fn profile_interval_test() {
    // Create a grid network with 10 ** 2 = 100 nodes.
    let n = 10;
    let graph = get_grid_network(n);

    let profile_tt: TTF<f64> = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
        (0., 10.),
        (45., 20.),
        (90., 10.),
    ]));
    let cst_tt = TTF::Constant(15.);
    let mut ops = ops::ProfileIntervalDijkstra::new_forward(&graph, |e: EdgeReference<()>| {
        if e.source() == node_index(0) && e.target() == node_index(1) {
            // First vertical edge from top-left corner node.
            &profile_tt
        } else {
            &cst_tt
        }
    });
    let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let query = query::SingleSourceQuery::from_default(node_index(0));
    search.solve_query(&query, &mut ops);
    let label = search.get_label(&node_index(n + 1));
    // Two paths to go from node (0, 0) to node (1, 1):
    // - Go through node (1, 0), with constant travel time 30 (last departure is 85).
    // - Go through node (0, 1), with travel time profile ([0, 45, 90], [25, 35, 25]).
    assert_eq!(label, Some(&[25., 30.]));
    let p = search.get_predecessor(&node_index(n + 1)).unwrap();
    assert!(
        p.contains(&node_index(1)),
        "Invalid predecessor set: {:?}",
        p
    );
    assert!(
        p.contains(&node_index(n)),
        "Invalid predecessor set: {:?}",
        p
    );
    // 2 * (n - 1) (= 18) edges are needed to reach the node n * n - 1.
    let label = search.get_label(&node_index(n * n - 1));
    let nb_edges = 2. * (n as f64 - 1.);
    assert_eq!(label, Some(&[(nb_edges * 15. - 5.), (nb_edges * 15.)]));

    // The nodes should be settled in this order (values in parenthesis are their key):
    // 0 (0.) -> 1 (10.) -> n (15.) -> 2 (25) -> n + 1 (25) -> 2n (30).
    // The upper bound for node n + 1 is 30 so the query stops when the next key is larger than 30.
    // The node 4 should not have been explored.
    let query = query::PointToPointQuery::from_default(node_index(0), node_index(n + 1));
    search.solve_query(&query, &mut ops);
    let label = search.get_label(&node_index(n + 1));
    assert_eq!(label, Some(&[25., 30.]));
    let label = search.get_label(&node_index(4));
    // This node is not explored because the query stopped before.
    assert_eq!(label, None);
}

#[test]
fn thin_profile_interval_test() {
    // Create a grid network with 10 ** 2 = 100 nodes.
    let n = 10;
    let graph = get_grid_network(n);

    let profile_tt: TTF<f64> = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
        (0., 10.),
        (45., 20.),
        (90., 10.),
    ]));
    let cst_tt = TTF::Piecewise(PwlTTF::from_breakpoints(vec![(0., 15.), (100., 15.)]));
    let mut ops = ops::ThinProfileIntervalDijkstra::new_forward(&graph, |e: EdgeReference<()>| {
        if e.source() == node_index(0) && e.target() == node_index(1) {
            // First vertical edge from top-left corner node.
            &profile_tt
        } else {
            &cst_tt
        }
    });
    let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let query = query::SingleSourceQuery::from_default(node_index(0));
    search.solve_query(&query, &mut ops);
    let label = search.get_label(&node_index(n + 1));
    // Two paths to go from node (0, 0) to node (1, 1):
    // - Go through node (1, 0), with constant travel time 30 (last departure is 85).
    // - Go through node (0, 1), with travel time profile ([0, 45, 90], [25, 35, 25]).
    assert_eq!(label, Some(&[25., 30.]));
    // The lower bound 25 comes from node 1.
    // The upper bound 30 comes from node n.
    let p = search.get_predecessor(&node_index(n + 1)).unwrap();
    assert_eq!(p, &[node_index(1), node_index(n)]);
}

#[test]
fn hop_limit_test() {
    // Create a grid network with 10 ** 2 = 100 nodes.
    let n = 10;
    let graph = get_grid_network(n);

    let scalar_ops = ScalarDijkstra::new_forward(&graph, |_| 1.0f32);
    let mut ops = ops::HopLimitedDijkstra::new(scalar_ops, 2);
    let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let query = query::SingleSourceQuery::new(node_index(0), 0.);
    search.solve_query(&query, &mut ops);
    let label = search.get_label(&node_index(n + 1));
    assert_eq!(label, Some(&2.));
    // Node 3 exceed the hop limit of 2.
    let label = search.get_label(&node_index(3));
    assert_eq!(label, Some(&3.));
    // With unitary weights, the labels never exceed the hop limit (2).
    assert_eq!(
        search
            .node_map()
            .values()
            .map(|v| v.data.0)
            .max_by(|a, b| a.partial_cmp(b).unwrap()),
        Some(3.)
    );
}

#[test]
fn tchea_test() {
    // Create a grid network with 10 ** 2 = 100 nodes.
    let n = 10;
    let graph = get_grid_network(n);

    let profile_tt: TTF<f64> = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
        (0., 10.),
        (45., 20.),
        (90., 10.),
    ]));
    let cst_tt = TTF::Constant(15.);
    let mut ops = bidirectional_ops::BidirectionalTCHEA::new(
        &graph,
        |e: EdgeReference<()>| {
            if e.source() == node_index(0) && e.target() == node_index(1) {
                // First vertical edge from top-left corner node.
                &profile_tt
            } else {
                &cst_tt
            }
        },
        HashMap::new(),
    );
    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let query =
        query::BidirectionalPointToPointQuery::new(node_index(0), node_index(n + 1), 45., [0., 0.]);
    search.solve_query(&query, &mut ops);
    let candidates = ops.get_candidates();
    // The fastest path go through node n so it should definitely be in the map of candidates with
    // lower bound 45 + 15 * 2 = 75 and arrival at 45 + 15 = 60.
    assert_eq!(candidates.get(&node_index(n)), Some(&(75., 60.)));
    // If node 1 is in the candidates map, its lower bound is 45 + 10 + 15 = 70.
    // Its arrival time is 45 + 20 = 65.
    assert!(
        candidates.get(&node_index(1)).is_none()
            || candidates.get(&node_index(1)).unwrap() == &(70., 65.)
    );
    // If node 0 is in the candidates, its lower bound is 45 + 10 + 15 = 70 and its arrival time is
    // 45.
    assert!(
        candidates.get(&node_index(0)).is_none()
            || candidates.get(&node_index(0)).unwrap() == &(70., 45.)
    );
    // If node n + 1 is in the candidates, its lower bound is 45 + 2 * 15 = 75 and its arrival time
    // is also 75.
    assert!(
        candidates.get(&node_index(n + 1)).is_none()
            || candidates.get(&node_index(n + 1)).unwrap() == &(75., 75.)
    );
    assert!(candidates.len() <= 4);
}

#[test]
#[ignore]
fn scalar_contraction_hierarchies_test() {
    // Create a grid network with 10 ** 2 = 100 nodes.
    let n = 10;
    let graph = get_grid_network(n);

    let cst_tt = TTF::Constant(1.0f64);

    let parameters = ContractionParameters::default();

    let ch = HierarchyOverlay::order(&graph, |_| cst_tt.clone(), parameters);
    println!("Order: {:?}", ch.get_order());

    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let ea_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let downward_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut ea_alloc = algo::EarliestArrivalAllocation::new(ea_search, downward_search);
    let mut candidate_map = HashMap::new();

    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut profile_interval_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut profile_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let mut candidate_map2 = HashMap::new();

    for n0 in 0..(n * n - 1) {
        for n1 in 0..(n * n - 1) {
            if n0 == n1 {
                continue;
            }
            println!("n0: {}", n0);
            println!("n1: {}", n1);
            let horiz_tt = if n0 % n > n1 % n {
                n0 % n - n1 % n
            } else {
                n1 % n - n0 % n
            };
            let vert_tt = if n0 > n1 {
                n0 / n - n1 / n
            } else {
                n1 / n - n0 / n
            };
            let tt = horiz_tt + vert_tt;
            let (arr_time, path) = ch
                .earliest_arrival_query(
                    node_index(n0),
                    node_index(n1),
                    0.,
                    &mut ea_alloc,
                    &mut candidate_map,
                )
                .unwrap()
                .unwrap();
            assert_eq!(arr_time, tt as f64);
            assert_eq!(path.len(), tt);
            let ttf = ch
                .profile_query(
                    node_index(n0),
                    node_index(n1),
                    &mut profile_interval_search,
                    &mut profile_search,
                    &mut candidate_map2,
                )
                .unwrap();
            assert_eq!(ttf.get_min(), tt as f64);
            assert_eq!(ttf.get_max(), tt as f64);
        }
    }

    // Test re-using the node order.
    let order = ch.get_order();
    let parameters = ContractionParameters::default();

    let ch2 = HierarchyOverlay::construct(
        &graph,
        |_| cst_tt.clone(),
        |node_id| order[node_id.index()],
        parameters,
    );

    for n0 in 0..(n * n - 1) {
        for n1 in 0..(n * n - 1) {
            if n0 == n1 {
                continue;
            }
            println!("n0: {}", n0);
            println!("n1: {}", n1);
            let horiz_tt = if n0 % n > n1 % n {
                n0 % n - n1 % n
            } else {
                n1 % n - n0 % n
            };
            let vert_tt = if n0 > n1 {
                n0 / n - n1 / n
            } else {
                n1 / n - n0 / n
            };
            let tt = horiz_tt + vert_tt;
            let (arr_time, path) = ch2
                .earliest_arrival_query(
                    node_index(n0),
                    node_index(n1),
                    0.,
                    &mut ea_alloc,
                    &mut candidate_map,
                )
                .unwrap()
                .unwrap();
            assert_eq!(arr_time, tt as f64);
            assert_eq!(path.len(), tt);
            let ttf = ch2
                .profile_query(
                    node_index(n0),
                    node_index(n1),
                    &mut profile_interval_search,
                    &mut profile_search,
                    &mut candidate_map2,
                )
                .unwrap();
            assert_eq!(ttf.get_min(), tt as f64);
            assert_eq!(ttf.get_max(), tt as f64);
        }
    }
}

#[test]
fn contraction_hierarchies_test() {
    // Create a grid network with 10 ** 2 = 100 nodes.
    let n = 10;
    let graph = get_grid_network(n);

    let profile_tt: TTF<f64> = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
        (0., 10.),
        (5000., 20.),
        (10000., 10.),
    ]));
    let cst_tt = TTF::Constant(15.);

    let parameters = ContractionParameters::default();

    let ch = HierarchyOverlay::order(
        &graph,
        |edge_id| {
            if edge_id == edge_index(0) {
                // First vertical edge from top-left corner node.
                profile_tt.clone()
            } else {
                cst_tt.clone()
            }
        },
        parameters,
    );
    println!("Order: {:?}", ch.get_order());
    println!("Nb. nodes: {}", ch.node_count());
    println!("Nb. edges: {}", ch.edge_count());

    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let ea_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let downward_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut ea_alloc = algo::EarliestArrivalAllocation::new(ea_search, downward_search);
    let mut candidate_map = HashMap::new();

    // When leaving at time 0, the best path is to take the time-dependent path, with travel time
    // 10 + 15 = 25.
    let (arr_time, path) = ch
        .earliest_arrival_query(
            node_index(0),
            node_index(n + 1),
            0.,
            &mut ea_alloc,
            &mut candidate_map,
        )
        .unwrap()
        .unwrap();
    assert_eq!(arr_time, 25.);
    assert_eq!(path.len(), 2);
    assert_eq!(
        graph.edge_endpoints(path[0]),
        Some((node_index(0), node_index(n)))
    );
    assert_eq!(
        graph.edge_endpoints(path[1]),
        Some((node_index(n), node_index(n + 1)))
    );

    // When leaving at time 5000, the best path is to take the time-indpendent path, with travel
    // time 15 + 15 = 30.
    let (arr_time, path) = ch
        .earliest_arrival_query(
            node_index(0),
            node_index(n + 1),
            5000.,
            &mut ea_alloc,
            &mut candidate_map,
        )
        .unwrap()
        .unwrap();
    assert_eq!(arr_time, 5000. + 30.);
    assert_eq!(path.len(), 2);
    assert_eq!(
        graph.edge_endpoints(path[0]),
        Some((node_index(0), node_index(1)))
    );
    assert_eq!(
        graph.edge_endpoints(path[1]),
        Some((node_index(1), node_index(n + 1)))
    );

    // To go from node 0 to node n * n - 1 (last node), 2 * (n - 1) edges need to be crossed for a
    // total travel time of 15 * 2 * (n - 1), when leaving at time 5000.
    let (arr_time, path) = ch
        .earliest_arrival_query(
            node_index(0),
            node_index(n * n - 1),
            5000.,
            &mut ea_alloc,
            &mut candidate_map,
        )
        .unwrap()
        .unwrap();
    assert_eq!(arr_time, 5000. + 15. * 2. * (n as f64 - 1.));
    assert_eq!(path.len(), 2 * (n - 1));
    assert_ne!(path[0], edge_index(0));

    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut profile_interval_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
    let mut profile_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
    let mut candidate_map2 = HashMap::new();

    let label = ch.profile_query(
        node_index(0),
        node_index(1),
        &mut profile_interval_search,
        &mut profile_search,
        &mut candidate_map2,
    );
    assert_eq!(label, Some(cst_tt.clone()));

    let label = ch.profile_query(
        node_index(0),
        node_index(n + 1),
        &mut profile_interval_search,
        &mut profile_search,
        &mut candidate_map2,
    );
    // Two paths to go from node (0, 0) to node (1, 1):
    // - Go through node (1, 0), with constant travel time 30.
    // - Go through node (0, 1), with travel time profile ([0, 5000, 10000], [25, 35, 25]).
    let ttf: TTF<f64> = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
        (0., 25.),
        (2500., 30.),
        (7500., 30.),
        (10000., 25.),
    ]));
    assert_eq!(label, Some(ttf));

    // Test re-using the node order.
    let order = ch.get_order();

    let parameters = ContractionParameters::default();

    let ch2 = HierarchyOverlay::construct(
        &graph,
        |edge_id| {
            if edge_id == edge_index(0) {
                // First vertical edge from top-left corner node.
                profile_tt.clone()
            } else {
                cst_tt.clone()
            }
        },
        |node_id| order[node_id.index()],
        parameters,
    );

    // assert_eq!(ch.edge_count(), ch2.edge_count());

    // When leaving at time 0, the best path is to take the time-dependent path, with travel time
    // 10 + 15 = 25.
    let (arr_time, path) = ch2
        .earliest_arrival_query(
            node_index(0),
            node_index(n + 1),
            0.,
            &mut ea_alloc,
            &mut candidate_map,
        )
        .unwrap()
        .unwrap();
    assert_eq!(arr_time, 25.);
    assert_eq!(path.len(), 2);
    assert_eq!(
        graph.edge_endpoints(path[0]),
        Some((node_index(0), node_index(n)))
    );
    assert_eq!(
        graph.edge_endpoints(path[1]),
        Some((node_index(n), node_index(n + 1)))
    );

    // When leaving at time 5000, the best path is to take the time-indpendent path, with travel
    // time 15 + 15 = 30.
    let (arr_time, path) = ch2
        .earliest_arrival_query(
            node_index(0),
            node_index(n + 1),
            5000.,
            &mut ea_alloc,
            &mut candidate_map,
        )
        .unwrap()
        .unwrap();
    assert_eq!(arr_time, 5000. + 30.);
    assert_eq!(path.len(), 2);
    assert_eq!(
        graph.edge_endpoints(path[0]),
        Some((node_index(0), node_index(1)))
    );
    assert_eq!(
        graph.edge_endpoints(path[1]),
        Some((node_index(1), node_index(n + 1)))
    );

    // To go from node 0 to node n * n - 1 (last node), 2 * (n - 1) edges need to be crossed for a
    // total travel time of 15 * 2 * (n - 1), when leaving at time 5000.
    let (arr_time, path) = ch
        .earliest_arrival_query(
            node_index(0),
            node_index(n * n - 1),
            5000.,
            &mut ea_alloc,
            &mut candidate_map,
        )
        .unwrap()
        .unwrap();
    assert_eq!(arr_time, 5000. + 15. * 2. * (n as f64 - 1.));
    assert_eq!(path.len(), 2 * (n - 1));
    assert_ne!(path[0], edge_index(0));

    let label = ch2.profile_query(
        node_index(0),
        node_index(n + 1),
        &mut profile_interval_search,
        &mut profile_search,
        &mut candidate_map2,
    );
    // Two paths to go from node (0, 0) to node (1, 1):
    // - Go through node (1, 0), with constant travel time 30.
    // - Go through node (0, 1), with travel time profile ([0, 5000, 10000], [25, 35, 25]).
    let ttf: TTF<f64> = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
        (0., 25.),
        (2500., 30.),
        (7500., 30.),
        (10000., 25.),
    ]));
    assert_eq!(label, Some(ttf));
}
