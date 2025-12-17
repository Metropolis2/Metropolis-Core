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

//! Trait and structs used to represent bidirectional Dijkstra algorithms.
use std::collections::VecDeque;

use hashbrown::{HashMap, HashSet};
use petgraph::graph::IndexType;
use petgraph::visit::{GraphBase, IntoEdgesDirected};
use ttf::{TTFNum, TTF};

use crate::node_data::{NodeData, NodeDataWithExtra};
use crate::node_map::NodeMap;
use crate::ops::{
    BoundedDijkstra, DijkstraOps, ProfileDijkstra, ProfileIntervalDijkstra, ScalarDijkstra,
    TimeDependentDijkstra,
};
use crate::query::BidirectionalQuery;

/// Trait representing a set of instructions to perform a bidirectional Dijkstra's algorithm.
///
/// A BidirectionalDijkstraOps is composed of the following:
///
/// - A [DijkstraOps] for the forward search.
///
/// - A [DijkstraOps] for the backward search.
///
/// - An (optional) set of instructions that are performed when the two searches meet and that tell
///   when the algorithm can be stopped.
pub trait BidirectionalDijkstraOps {
    /// Type of the nodes.
    type Node;
    /// Type of the forward search [DijkstraOps].
    type FOps: DijkstraOps<Node = Self::Node>;
    /// Type of the backward search [DijkstraOps].
    type BOps: DijkstraOps<Node = Self::Node>;
    /// Returns a mutable reference to the forward search [DijkstraOps].
    fn forward_ops(&mut self) -> &mut Self::FOps;
    /// Returns a mutable reference to the backward search [DijkstraOps].
    fn backward_ops(&mut self) -> &mut Self::BOps;
    /// Function called each time the forward and backward search meet, i.e., when the next node to
    /// be settled in one direction has already been explored in the other direction.
    ///
    /// The function takes as arguments the meeting node, its associated labels in both
    /// direction and the next key in the priority queue for both direction (or None if the
    /// priority queues are empty).
    /// It returns `true` if the search can be stopped immediately.
    fn pre_settle_check(
        &mut self,
        _node: Self::Node,
        _forw_data: &<Self::FOps as DijkstraOps>::Data,
        _back_data: &<Self::BOps as DijkstraOps>::Data,
        _forw_key: Option<<Self::FOps as DijkstraOps>::Key>,
        _back_key: Option<<Self::BOps as DijkstraOps>::Key>,
        _query: impl BidirectionalQuery<
            Node = Self::Node,
            Label = <<Self::FOps as DijkstraOps>::Data as NodeData>::Label,
            RevLabel = <<Self::BOps as DijkstraOps>::Data as NodeData>::Label,
        >,
    ) -> bool {
        false
    }
    /// Returns `true` if the given node can be stalled, i.e., it can be skipped from the Dijkstra
    /// search.
    fn can_be_stalled(
        &mut self,
        _node: Self::Node,
        _forw_key: Option<<Self::FOps as DijkstraOps>::Key>,
        _back_key: Option<<Self::BOps as DijkstraOps>::Key>,
        _forw_data: &mut HashMap<Self::Node, <Self::FOps as DijkstraOps>::Data>,
        _back_data: &mut HashMap<Self::Node, <Self::BOps as DijkstraOps>::Data>,
    ) -> bool {
        false
    }
}

/// Instructions for a bidirectional Dijksta's algorithm where the labels coincide with the keys.
///
/// This means that the labels are [Copy] and thus many simplifications can be done.
///
/// The algorithm stops as soon as the next node to be settled in one direction has already been
/// settled in the other direction.
///
/// The graph should implement [petgraph::visit::IntoEdgesDirected] and should not have
/// negative-weight loops.
///
/// # Example
///
/// ```
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use priority_queue::PriorityQueue;
/// use tch::bidirectional_ops::ScalarBidirectionalDijkstra;
/// use tch::query::BidirectionalPointToPointQuery;
/// use tch::{BidirectionalDijkstraSearch, DijkstraSearch};
///
/// // Run a point-to-point bidirectonal Dijkstra search with scalars on a graph with three edges.
/// let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let mut search = BidirectionalDijkstraSearch::new(forw_search, back_search);
/// let graph = DiGraph::<(), f32>::from_edges(&[(0, 1, 1.), (1, 2, 2.), (0, 2, 4.)]);
/// let mut ops = ScalarBidirectionalDijkstra::new(&graph, |e: EdgeReference<_>| *e.weight());
/// let query = BidirectionalPointToPointQuery::from_default(node_index(0), node_index(2));
/// search.solve_query(&query, &mut ops);
/// assert_eq!(ops.get_score(), Some(3.));
/// assert_eq!(ops.get_meeting_node(), Some(node_index(1)));
/// assert_eq!(
///     search.get_path(node_index(1)).unwrap(),
///     vec![node_index(0), node_index(1), node_index(2)]
/// );
/// ```
#[derive(Clone, Debug)]
pub struct ScalarBidirectionalDijkstra<G1, G2, F1, F2, N, T> {
    forw_ops: ScalarDijkstra<G1, F1>,
    back_ops: ScalarDijkstra<G2, F2>,
    meeting_node: Option<N>,
    score: Option<T>,
}

impl<G1, G2, F1, F2, N, T> ScalarBidirectionalDijkstra<G1, G2, F1, F2, N, T> {
    /// Initializes a new ScalarBidirectionalDijkstra from a graph with labels for the forward
    /// search and a graph with labels for the backward search.
    pub fn new_raw(graph1: G1, edge_label1: F1, graph2: G2, edge_label2: F2) -> Self {
        let forw_ops = ScalarDijkstra::new_forward(graph1, edge_label1);
        let back_ops = ScalarDijkstra::new_backward(graph2, edge_label2);
        ScalarBidirectionalDijkstra {
            forw_ops,
            back_ops,
            meeting_node: None,
            score: None,
        }
    }
}

impl<G: Copy, F: Copy, N, T> ScalarBidirectionalDijkstra<G, G, F, F, N, T> {
    /// Initializes a new ScalarBidirectionalDijkstra from a graph and labels that are used for both
    /// the forward and backward search.
    pub fn new(graph: G, edge_label: F) -> Self {
        ScalarBidirectionalDijkstra::new_raw(graph, edge_label, graph, edge_label)
    }
}

impl<G1, G2, F1, F2, N: Copy, T: Copy> ScalarBidirectionalDijkstra<G1, G2, F1, F2, N, T> {
    /// Returns the meeting node of the forward and backward searches (or `None` if the searches
    /// have not met).
    pub fn get_meeting_node(&self) -> Option<N> {
        self.meeting_node
    }

    /// Returns the minimum score found for the current query (or `None` if no score has been
    /// found).
    pub fn get_score(&self) -> Option<T> {
        self.score
    }
}

impl<G1, G2, F1, F2, N, T> BidirectionalDijkstraOps
    for ScalarBidirectionalDijkstra<G1, G2, F1, F2, N, T>
where
    G1: GraphBase<NodeId = N> + IntoEdgesDirected,
    F1: Fn(G1::EdgeRef) -> T,
    G2: GraphBase<NodeId = N> + IntoEdgesDirected,
    F2: Fn(G2::EdgeRef) -> T,
    T: TTFNum,
    N: Copy + PartialEq,
{
    type Node = N;
    type FOps = ScalarDijkstra<G1, F1>;
    type BOps = ScalarDijkstra<G2, F2>;
    fn forward_ops(&mut self) -> &mut Self::FOps {
        &mut self.forw_ops
    }
    fn backward_ops(&mut self) -> &mut Self::BOps {
        &mut self.back_ops
    }
    fn pre_settle_check(
        &mut self,
        node: N,
        &(forw_label, _): &(T, Option<N>),
        &(back_label, _): &(T, Option<N>),
        forw_key: Option<T>,
        back_key: Option<T>,
        _query: impl BidirectionalQuery<Node = N, Label = T, RevLabel = T>,
    ) -> bool {
        // The two searches met but we need to check that the meeting node has been settled in both
        // direction and thus that no further improvement is possible.
        if (forw_key.is_none() || forw_label <= forw_key.unwrap())
            && (back_key.is_none() || back_label <= back_key.unwrap())
        {
            let score = forw_label + back_label;
            self.meeting_node = Some(node);
            self.score = Some(score);
            return true;
        }
        false
    }
}

/// Instructions for a bidirectional profile query.
///
/// The algorithm executes a [ProfileDijkstra] in both direction.
/// Each time the forward and backward search meet, the meeting node is stored in a set of candidate
/// nodes, together with a lower bound for the travel time between a source and a target when going
/// through this node.
///
/// # Example
///
/// ```
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
/// use tch::bidirectional_ops::BidirectionalProfileDijkstra;
/// use tch::query::BidirectionalPointToPointQuery;
/// use tch::{BidirectionalDijkstraSearch, DijkstraSearch};
/// use ttf::{PwlTTF, TTF};
///
/// let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let mut search = BidirectionalDijkstraSearch::new(forw_search, back_search);
/// let graph = DiGraph::<(), TTF<_>>::from_edges(&[
///     (0, 1, TTF::Constant(1.)),
///     (1, 2, TTF::Constant(2.)),
///     (
///         0,
///         2,
///         TTF::Piecewise(PwlTTF::from_values(vec![4., 0.], 0., 10.)),
///     ),
/// ]);
/// let mut ops = BidirectionalProfileDijkstra::new(
///     &graph,
///     |e: EdgeReference<_>| &graph[e.id()],
///     HashMap::new(),
/// );
/// let query = BidirectionalPointToPointQuery::from_default(node_index(0), node_index(2));
/// search.solve_query(&query, &mut ops);
/// let candidates = ops.get_candidates();
/// assert_eq!(candidates.len(), 3);
/// assert_eq!(candidates.get(&node_index(0)), Some(&0.));
/// assert_eq!(candidates.get(&node_index(1)), Some(&3.));
/// assert_eq!(candidates.get(&node_index(2)), Some(&0.));
/// ```
#[derive(Clone, Debug)]
pub struct BidirectionalProfileDijkstra<G1, G2, F1, F2, B, CM> {
    forw_ops: ProfileDijkstra<G1, F1, B>,
    back_ops: ProfileDijkstra<G2, F2, B>,
    candidates: CM,
}

impl<G: Copy, F: Copy, B, CM> BidirectionalProfileDijkstra<G, G, F, F, B, CM> {
    /// Initializes a new BidirectionalProfileDijkstra, given a graph and weights used for both the
    /// forward and backward searches, and a map used to store the candidates,
    pub fn new(graph: G, edge_label: F, candidates: CM) -> Self {
        BidirectionalProfileDijkstra::new_raw(graph, edge_label, graph, edge_label, candidates)
    }
}

impl<G1, G2, F1, F2, B, CM> BidirectionalProfileDijkstra<G1, G2, F1, F2, B, CM> {
    /// Initializes a new BidirectionalProfileDijkstra, given a graph and weights for the forward
    /// search, another graph and weights for the backward search, and a map used to store the
    /// candidates.
    pub fn new_raw(
        graph1: G1,
        edge_label1: F1,
        graph2: G2,
        edge_label2: F2,
        candidates: CM,
    ) -> Self {
        let forw_ops = ProfileDijkstra::new_forward(graph1, edge_label1);
        let back_ops = ProfileDijkstra::new_backward(graph2, edge_label2);
        BidirectionalProfileDijkstra {
            forw_ops,
            back_ops,
            candidates,
        }
    }

    /// Returns a reference to the map of candidates.
    ///
    /// This is a map `N -> T`, that gives, for each candidate node `n`, a lower bound for the
    /// travel time between a source and a target when going through this node.
    pub fn get_candidates(&self) -> &CM {
        &self.candidates
    }
}

impl<'a, G1, G2, F1, F2, N, T, CM> BidirectionalDijkstraOps
    for BidirectionalProfileDijkstra<G1, G2, F1, F2, T, CM>
where
    G1: GraphBase<NodeId = N> + IntoEdgesDirected,
    F1: Fn(G1::EdgeRef) -> &'a TTF<T>,
    G2: GraphBase<NodeId = N> + IntoEdgesDirected,
    F2: Fn(G2::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
    N: IndexType,
    CM: NodeMap<Node = N, Value = T>,
{
    type Node = N;
    type FOps = ProfileDijkstra<G1, F1, T>;
    type BOps = ProfileDijkstra<G2, F2, T>;
    fn forward_ops(&mut self) -> &mut Self::FOps {
        &mut self.forw_ops
    }
    fn backward_ops(&mut self) -> &mut Self::BOps {
        &mut self.back_ops
    }
    fn pre_settle_check(
        &mut self,
        node: N,
        (forw_label, _): &(TTF<T>, Option<HashSet<N>>),
        (back_label, _): &(TTF<T>, Option<HashSet<N>>),
        _forw_key: Option<T>,
        _back_key: Option<T>,
        _query: impl BidirectionalQuery<Node = N, Label = TTF<T>, RevLabel = TTF<T>>,
    ) -> bool {
        // Update the bound to the minimum travel time found so far in the worse case scenario
        // (i.e., when the travel time for the forward and backward search is equal to their upper
        // bound).
        let upper_bound = forw_label.get_max() + back_label.get_max();
        self.forw_ops.update_bound(upper_bound);
        self.back_ops.update_bound(upper_bound);
        // Add a candidate if its lower bound is better than the best upper bound found so far.
        let lower_bound = forw_label.get_min() + back_label.get_min();
        if !self.forw_ops.get_bound().is_smaller(lower_bound) {
            self.candidates.insert(node, lower_bound);
        }
        false
    }
}

/// Instructions for a bidirectional earliest-arrival query on a TCH structure.
///
/// This corresponds to Algorithm 4 in Batz et al. (2013)[^ref], excluding the downwarch-search
/// part.
///
/// [^ref]: Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013).
///     Minimum time-dependent travel times with contraction hierarchies.
///     _Journal of Experimental Algorithmics (JEA)_, _18_, 1-1.
///
/// A BidirectionalTCHEA executes a forward [TimeDependentDijkstra] and a backward
/// [ProfileIntervalDijkstra].
/// Each time the forward and backward search meet, the meeting node is stored in a set of
/// candidate nodes, together with its label in the forward search and a lower bound for the
/// arrival time at a target when going through this node.
///
/// Stall-on-demand is used, as described in Section 5.4 of Batz et al. (2013)[^ref].
///
/// # Example
///
/// ```
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
/// use tch::bidirectional_ops::BidirectionalTCHEA;
/// use tch::query::BidirectionalPointToPointQuery;
/// use tch::{BidirectionalDijkstraSearch, DijkstraSearch};
/// use ttf::{PwlTTF, TTF};
///
/// let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let mut search = BidirectionalDijkstraSearch::new(forw_search, back_search);
/// let graph = DiGraph::<(), TTF<_>>::from_edges(&[
///     (0, 1, TTF::Constant(1.)),
///     (1, 2, TTF::Constant(2.)),
///     (
///         0,
///         2,
///         TTF::Piecewise(PwlTTF::from_values(vec![4., 0.], 0., 10.)),
///     ),
/// ]);
/// let mut ops =
///     BidirectionalTCHEA::new(&graph, |e: EdgeReference<_>| &graph[e.id()], HashMap::new());
/// let query = BidirectionalPointToPointQuery::new(node_index(0), node_index(2), 0., [0., 0.]);
/// search.solve_query(&query, &mut ops);
/// let candidates = ops.get_candidates();
/// assert_eq!(candidates.len(), 3);
/// assert_eq!(candidates.get(&node_index(0)), Some(&(0., 0.)));
/// assert_eq!(candidates.get(&node_index(1)), Some(&(3., 1.)));
/// assert_eq!(candidates.get(&node_index(2)), Some(&(3., 3.)));
/// ```
#[derive(Clone, Debug)]
pub struct BidirectionalTCHEA<G1, G2, F1, F2, B0, B1, CM> {
    forw_ops: TimeDependentDijkstra<G1, F1, B0>,
    back_ops: ProfileIntervalDijkstra<G2, F2, B1>,
    candidates: CM,
}

impl<G: Copy, F: Copy, B0, B1, CM> BidirectionalTCHEA<G, G, F, F, B0, B1, CM> {
    /// Initializes a new BidirectionalTCHEA, given a graph and weights used for both the forward
    /// and backward searches, and a map used to store the candidates,
    pub fn new(graph: G, edge_label: F, candidates: CM) -> Self {
        BidirectionalTCHEA::new_raw(graph, edge_label, graph, edge_label, candidates)
    }
}

impl<G1, G2, F1, F2, B0, B1, CM> BidirectionalTCHEA<G1, G2, F1, F2, B0, B1, CM> {
    /// Initializes a new BidirectionalTCHEA, given a graph and weights for the forward search,
    /// another graph and weights for the backward search, and a map used to store the candidates.
    pub fn new_raw(
        graph1: G1,
        edge_label1: F1,
        graph2: G2,
        edge_label2: F2,
        candidates: CM,
    ) -> Self {
        let forw_ops = TimeDependentDijkstra::new(graph1, edge_label1);
        let back_ops = ProfileIntervalDijkstra::new_backward(graph2, edge_label2);
        BidirectionalTCHEA {
            forw_ops,
            back_ops,
            candidates,
        }
    }

    /// Returns a reference to the map of candidates.
    ///
    /// This is a map `N -> (T, T)`, that gives, for each candidate node `n`, a tuple `(t0, t1)`
    /// where `t0` is a lower bound for the arrival time to a target when going through node `n`
    /// and `t1` is the earliest arrival time at `n`.
    pub fn get_candidates(&self) -> &CM {
        &self.candidates
    }
}

impl<'a, G1, G2, F1, F2, N, T, CM> BidirectionalDijkstraOps
    for BidirectionalTCHEA<G1, G2, F1, F2, T, T, CM>
where
    G1: GraphBase<NodeId = N> + IntoEdgesDirected,
    F1: Fn(G1::EdgeRef) -> &'a TTF<T>,
    G2: GraphBase<NodeId = N> + IntoEdgesDirected,
    F2: Fn(G2::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
    N: IndexType,
    CM: NodeMap<Node = N, Value = (T, T)>,
{
    type Node = N;
    type FOps = TimeDependentDijkstra<G1, F1, T>;
    type BOps = ProfileIntervalDijkstra<G2, F2, T>;
    fn forward_ops(&mut self) -> &mut Self::FOps {
        &mut self.forw_ops
    }
    fn backward_ops(&mut self) -> &mut Self::BOps {
        &mut self.back_ops
    }
    fn pre_settle_check(
        &mut self,
        node: N,
        forw_data: &<Self::FOps as DijkstraOps>::Data,
        back_data: &<Self::BOps as DijkstraOps>::Data,
        _forw_key: Option<T>,
        _back_key: Option<T>,
        query: impl BidirectionalQuery<Node = Self::Node, Label = T, RevLabel = [T; 2]>,
    ) -> bool {
        // The bound is improved here compared to Algorithm 3 of Batz et al. (2013.
        // The bound for the forward search is the guaranteed earliest arrival time found so far
        // (i.e., using the upper bound).
        // The bound for the backward search is the minimum guaranteed travel time found so far.
        // When a search exceed its bound, its priority queue will be emptied and only the other
        // search will be used until it also exceeds its bound.
        let forw_label = forw_data.label();
        let back_label = back_data.label();
        let earliest_ta = *forw_label + back_label[1];
        self.forw_ops.update_bound(earliest_ta);
        let dep_time = query
            .sources_with_labels()
            .min_by(|t0, t1| t0.partial_cmp(t1).unwrap())
            .unwrap()
            .1;
        self.back_ops.update_bound(earliest_ta - dep_time);
        if !self
            .forw_ops
            .get_bound()
            .is_smaller(*forw_label + back_label[0])
        {
            self.candidates
                .insert(node, (*forw_label + back_label[0], *forw_label));
        }
        false
    }
    fn can_be_stalled(
        &mut self,
        node: N,
        forw_key: Option<T>,
        back_key: Option<T>,
        forw_data: &mut HashMap<N, <Self::FOps as DijkstraOps>::Data>,
        back_data: &mut HashMap<N, <Self::BOps as DijkstraOps>::Data>,
    ) -> bool {
        if let Some(key) = forw_key {
            for edge in self.back_ops.edges_from(node) {
                if let Some(prev_data) = forw_data.get(&self.back_ops.get_next_node(edge)) {
                    let tt = self.back_ops.get_ttf(edge).eval(*prev_data.label());
                    let arrival_time = *prev_data.label() + tt;
                    if arrival_time < key {
                        // The node can be stalled because the arrival time at the current node
                        // can be improved by going through the current edge.
                        return true;
                    }
                }
            }
            false
        } else if let Some(key) = back_key {
            for edge in self.forw_ops.edges_from(node) {
                if let Some(prev_data) = back_data.get(&self.forw_ops.get_next_node(edge)) {
                    let upper_bound = prev_data.label()[1] + self.forw_ops.get_ttf(edge).get_max();
                    if upper_bound < key {
                        // The node can be stalled because the arrival time at the current node
                        // can be improved by going through the current edge.
                        return true;
                    }
                }
            }
            false
        } else {
            panic!("One and only one of `forw_key` and `back_key` must be not `None`")
        }
    }
}

/// Instructions for a bidirectional profile query on a TCH structure.
///
/// This corresponds to Algorithm 5 in Batz et al. (2013)[^ref].
///
/// [^ref]: Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013).
///     Minimum time-dependent travel times with contraction hierarchies.
///     _Journal of Experimental Algorithmics (JEA)_, _18_, 1-1.
///
/// The algorithm executes a [ProfileDijkstra] in both direction.
/// Each time the forward and backward search meet, the meeting node is stored in a set of candidate
/// nodes, together with a lower bound for the travel time between a source and a target when going
/// through this node.
///
/// Stall-on-demand and cones are used, as described in Sections 5.4 and 5.5 of Batz et al.
/// (2013)[^ref].
///
/// # Example
///
/// ```
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
/// use tch::bidirectional_ops::BidirectionalTCHProfile;
/// use tch::query::BidirectionalPointToPointQuery;
/// use tch::{BidirectionalDijkstraSearch, DijkstraSearch};
/// use ttf::{PwlTTF, TTF};
///
/// let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let mut search = BidirectionalDijkstraSearch::new(forw_search, back_search);
/// let graph = DiGraph::<(), TTF<_>>::from_edges(&[
///     (0, 1, TTF::Constant(1.)),
///     (1, 2, TTF::Constant(2.)),
///     (
///         0,
///         2,
///         TTF::Piecewise(PwlTTF::from_values(vec![4., 0.], 0., 10.)),
///     ),
/// ]);
/// let mut ops =
///     BidirectionalTCHProfile::new(&graph, |e: EdgeReference<_>| &graph[e.id()], HashMap::new());
/// let query = BidirectionalPointToPointQuery::from_default(node_index(0), node_index(2));
/// search.solve_query(&query, &mut ops);
/// let candidates = ops.get_candidates();
/// assert_eq!(candidates.len(), 3);
/// assert_eq!(candidates.get(&node_index(0)), Some(&0.));
/// assert_eq!(candidates.get(&node_index(1)), Some(&3.));
/// assert_eq!(candidates.get(&node_index(2)), Some(&0.));
/// ```
#[derive(Clone, Debug)]
pub struct BidirectionalTCHProfile<G1, G2, F1, F2, B, CM> {
    forw_ops: ProfileDijkstra<G1, F1, B>,
    back_ops: ProfileDijkstra<G2, F2, B>,
    candidates: CM,
}

impl<G: Copy, F: Copy, B, CM> BidirectionalTCHProfile<G, G, F, F, B, CM> {
    /// Initializes a new BidirectionalTCHProfile, given a graph and weights used for both the
    /// forward and backward searches, and a map used to store the candidates,
    pub fn new(graph: G, edge_label: F, candidates: CM) -> Self {
        BidirectionalTCHProfile::new_raw(graph, edge_label, graph, edge_label, candidates)
    }
}

impl<G1, G2, F1, F2, B, CM> BidirectionalTCHProfile<G1, G2, F1, F2, B, CM> {
    /// Initializes a new BidirectionalTCHProfile, given a graph and weights for the forward
    /// search, another graph and weights for the backward search, and a map used to store the
    /// candidates.
    pub fn new_raw(
        graph1: G1,
        edge_label1: F1,
        graph2: G2,
        edge_label2: F2,
        candidates: CM,
    ) -> Self {
        let forw_ops = ProfileDijkstra::new_forward(graph1, edge_label1);
        let back_ops = ProfileDijkstra::new_backward(graph2, edge_label2);
        BidirectionalTCHProfile {
            forw_ops,
            back_ops,
            candidates,
        }
    }

    /// Returns a reference to the map of candidates.
    ///
    /// This is a map `N -> T`, that gives, for each candidate node `n`, a lower bound for the
    /// travel time between a source and a target when going through this node.
    pub fn get_candidates(&self) -> &CM {
        &self.candidates
    }
}

impl<'a, G1, G2, F1, F2, N, T, CM> BidirectionalDijkstraOps
    for BidirectionalTCHProfile<G1, G2, F1, F2, T, CM>
where
    G1: GraphBase<NodeId = N> + IntoEdgesDirected,
    F1: Fn(G1::EdgeRef) -> &'a TTF<T>,
    G2: GraphBase<NodeId = N> + IntoEdgesDirected,
    F2: Fn(G2::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
    N: IndexType,
    CM: NodeMap<Node = N, Value = T>,
{
    type Node = N;
    type FOps = ProfileDijkstra<G1, F1, T>;
    type BOps = ProfileDijkstra<G2, F2, T>;
    fn forward_ops(&mut self) -> &mut Self::FOps {
        &mut self.forw_ops
    }
    fn backward_ops(&mut self) -> &mut Self::BOps {
        &mut self.back_ops
    }
    fn pre_settle_check(
        &mut self,
        node: N,
        forw_data: &<Self::FOps as DijkstraOps>::Data,
        back_data: &<Self::BOps as DijkstraOps>::Data,
        _forw_key: Option<T>,
        _back_key: Option<T>,
        _query: impl BidirectionalQuery<Node = N, Label = TTF<T>, RevLabel = TTF<T>>,
    ) -> bool {
        // Update the bound to the minimum travel time found so far in the worse case scenario
        // (i.e., when the travel time for the forward and backward search is equal to their upper
        // bound).
        let upper_bound = forw_data.label().get_max() + back_data.label().get_max();
        self.forw_ops.update_bound(upper_bound);
        self.back_ops.update_bound(upper_bound);
        // Add a candidate if its lower bound is better than the best upper bound found so far.
        let lower_bound = forw_data.label().get_min() + back_data.label().get_min();
        if !self.forw_ops.get_bound().is_smaller(lower_bound) {
            self.candidates.insert(node, lower_bound);
        }
        false
    }
}

/// Instructions for a bidirectional profile interval search on a TCH structure.
///
/// This corresponds to the function `bidirTchProfileIntervalSearch` in Algorithm 7 of Batz et al.
/// (2013)[^ref].
///
/// [^ref]: Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013).
///     Minimum time-dependent travel times with contraction hierarchies.
///     _Journal of Experimental Algorithmics (JEA)_, _18_, 1-1.
///
/// The algorithm executes a [ProfileIntervalDijkstra] in both direction.
///
/// Stall-on-demand is used, as described in Section 5.4 of Batz et al. (2013)[^ref].
#[derive(Clone, Debug)]
pub struct BidirectionalTCHProfileInterval<G1, G2, F1, F2, B, CM> {
    forw_ops: BoundedDijkstra<ProfileIntervalDijkstra<G1, F1, B>>,
    back_ops: BoundedDijkstra<ProfileIntervalDijkstra<G2, F2, B>>,
    candidates: CM,
}

impl<G: Copy, F: Copy, B, CM> BidirectionalTCHProfileInterval<G, G, F, F, B, CM> {
    /// Initializes a new BidirectionalTCHProfile, given a graph and weights used for both the
    /// forward and backward searches, and a map used to store the candidates,
    pub fn new(graph: G, edge_label: F, candidate_map: CM) -> Self {
        BidirectionalTCHProfileInterval::new_raw(
            graph,
            edge_label,
            graph,
            edge_label,
            candidate_map,
        )
    }
}

impl<G1, G2, F1, F2, B, CM> BidirectionalTCHProfileInterval<G1, G2, F1, F2, B, CM> {
    /// Initializes a new BidirectionalTCHProfile, given a graph and weights for the forward search,
    /// another graph and weights for the backward search, and a map used to store the candidates.
    pub fn new_raw(
        graph1: G1,
        edge_label1: F1,
        graph2: G2,
        edge_label2: F2,
        candidate_map: CM,
    ) -> Self {
        let forw_ops = BoundedDijkstra(ProfileIntervalDijkstra::new_forward(graph1, edge_label1));
        let back_ops = BoundedDijkstra(ProfileIntervalDijkstra::new_backward(graph2, edge_label2));
        BidirectionalTCHProfileInterval {
            forw_ops,
            back_ops,
            candidates: candidate_map,
        }
    }

    /// Returns a reference to the map of candidates.
    ///
    /// This is a map `N -> T`, that gives, for each candidate node `n`, a lower bound for the
    /// travel time between a source and a target when going through this node.
    pub fn get_candidates(&self) -> &CM {
        &self.candidates
    }
}

type TCHProfileIntervalData<G, F, T> =
    NodeDataWithExtra<<ProfileIntervalDijkstra<G, F, T> as DijkstraOps>::Data, Option<T>>;

impl<'a, G1, G2, F1, F2, N, T, CM> BidirectionalTCHProfileInterval<G1, G2, F1, F2, T, CM>
where
    G1: GraphBase<NodeId = N> + IntoEdgesDirected,
    F1: Fn(G1::EdgeRef) -> &'a TTF<T>,
    G2: GraphBase<NodeId = N> + IntoEdgesDirected,
    F2: Fn(G2::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
    N: IndexType,
    CM: NodeMap<Node = N, Value = T>,
{
    fn propagate_stalling_forward(
        &mut self,
        node: N,
        value: T,
        data: &mut HashMap<N, TCHProfileIntervalData<G1, F1, T>>,
    ) {
        let mut queue = VecDeque::new();
        queue.push_front((node, value));
        while let Some((current, current_stalled)) = queue.pop_front() {
            for edge in self.forw_ops.edges_from(current) {
                let next = self.forw_ops.get_next_node(edge);
                if let Some(next_data) = data.get_mut(&next) {
                    let next_stalled = current_stalled + self.forw_ops.0.get_ttf(edge).get_max();
                    if next_data.label()[1] <= next_stalled {
                        continue;
                    }
                    match next_data.extra {
                        Some(ref mut old_stalled) => {
                            if next_stalled < *old_stalled {
                                *old_stalled = next_stalled;
                            } else {
                                continue;
                            }
                        }
                        None => {
                            next_data.extra = Some(next_stalled);
                        }
                    }
                    queue.push_back((next, next_stalled));
                }
            }
        }
    }

    fn propagate_stalling_backward(
        &mut self,
        node: N,
        value: T,
        data: &mut HashMap<N, TCHProfileIntervalData<G2, F2, T>>,
    ) {
        let mut queue = VecDeque::new();
        queue.push_front((node, value));
        while let Some((current, current_stalled)) = queue.pop_front() {
            for edge in self.back_ops.edges_from(current) {
                let next = self.back_ops.get_next_node(edge);
                if let Some(next_data) = data.get_mut(&next) {
                    let next_stalled = current_stalled + self.back_ops.0.get_ttf(edge).get_max();
                    if next_data.label()[1] <= next_stalled {
                        continue;
                    }
                    match next_data.extra {
                        Some(ref mut old_stalled) => {
                            if next_stalled < *old_stalled {
                                *old_stalled = next_stalled;
                            } else {
                                continue;
                            }
                        }
                        None => {
                            next_data.extra = Some(next_stalled);
                        }
                    }
                    queue.push_back((next, next_stalled));
                }
            }
        }
    }
}

impl<'a, G1, G2, F1, F2, N, T, CM> BidirectionalDijkstraOps
    for BidirectionalTCHProfileInterval<G1, G2, F1, F2, T, CM>
where
    G1: GraphBase<NodeId = N> + IntoEdgesDirected,
    F1: Fn(G1::EdgeRef) -> &'a TTF<T>,
    G2: GraphBase<NodeId = N> + IntoEdgesDirected,
    F2: Fn(G2::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
    N: IndexType,
    CM: NodeMap<Node = N, Value = T>,
{
    type Node = N;
    type FOps = BoundedDijkstra<ProfileIntervalDijkstra<G1, F1, T>>;
    type BOps = BoundedDijkstra<ProfileIntervalDijkstra<G2, F2, T>>;
    fn forward_ops(&mut self) -> &mut Self::FOps {
        &mut self.forw_ops
    }
    fn backward_ops(&mut self) -> &mut Self::BOps {
        &mut self.back_ops
    }
    fn pre_settle_check(
        &mut self,
        node: N,
        forw_data: &<Self::FOps as DijkstraOps>::Data,
        back_data: &<Self::BOps as DijkstraOps>::Data,
        _forw_key: Option<T>,
        _back_key: Option<T>,
        _query: impl BidirectionalQuery<Node = N, Label = [T; 2], RevLabel = [T; 2]>,
    ) -> bool {
        // Update the bound to the minimum travel time found so far in the worse case scenario
        // (i.e., when the travel time for the forward and backward search is equal to their upper
        // bound).
        let upper_bound = forw_data.label()[1] + back_data.label()[1];
        self.forw_ops.0.update_bound(upper_bound);
        self.back_ops.0.update_bound(upper_bound);
        // Add a candidate if its lower bound is better than the best upper bound found so far.
        let lower_bound = forw_data.label()[0] + back_data.label()[0];
        if !self.forw_ops.0.get_bound().is_smaller(lower_bound) {
            self.candidates.insert(node, lower_bound);
        }
        false
    }
    fn can_be_stalled(
        &mut self,
        node: N,
        forw_key: Option<T>,
        back_key: Option<T>,
        forw_data: &mut HashMap<N, <Self::FOps as DijkstraOps>::Data>,
        back_data: &mut HashMap<N, <Self::BOps as DijkstraOps>::Data>,
    ) -> bool {
        if let Some(key) = forw_key {
            let node_data = forw_data.get(&node).unwrap();
            if node_data
                .extra
                .map(|t| t + T::MARGIN < key)
                .unwrap_or(false)
            {
                // The node is already stalled with a smaller value.
                return true;
            }
            for edge in self.back_ops.edges_from(node) {
                if let Some(next_data) = forw_data.get(&self.back_ops.get_next_node(edge)) {
                    let upper_bound =
                        next_data.label()[1] + self.back_ops.0.get_ttf(edge).get_max();
                    if upper_bound < key {
                        // The node can be stalled because the ttf for the current node is
                        // dominated by the ttf when going through the current edge.
                        forw_data.get_mut(&node).unwrap().extra = Some(upper_bound);
                        self.propagate_stalling_forward(node, upper_bound, forw_data);
                        return true;
                    }
                }
            }
            false
        } else if let Some(key) = back_key {
            let node_data = back_data.get(&node).unwrap();
            if node_data.extra.map(|t| t < key).unwrap_or(false) {
                // The node is already stalled with a smaller value.
                return true;
            }
            for edge in self.forw_ops.edges_from(node) {
                if let Some(next_data) = back_data.get(&self.forw_ops.get_next_node(edge)) {
                    let upper_bound =
                        next_data.label()[1] + self.forw_ops.0.get_ttf(edge).get_max();
                    if upper_bound < key {
                        // The node can be stalled because the ttf for the current node is
                        // dominated by the ttf when going through the current edge.
                        back_data.get_mut(&node).unwrap().extra = Some(upper_bound);
                        self.propagate_stalling_backward(node, upper_bound, back_data);
                        return true;
                    }
                }
            }
            false
        } else {
            panic!("One and only one of `forw_key` and `back_key` must be not `None`")
        }
    }
}

#[cfg(test)]
mod tests {
    use hashbrown::HashMap;
    use petgraph::graph::{node_index, DiGraph};
    use priority_queue::PriorityQueue;

    use super::*;
    use crate::bidirectional_search::BidirectionalDijkstraSearch;
    use crate::query::BidirectionalPointToPointQuery;
    use crate::search::DijkstraSearch;

    #[test]
    fn disconnected_bidir_test() {
        // On a disconnected graph, the forward and backward search should never meet but the
        // bidirectional search should stop gracefully.
        let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let mut search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        // Graph with two disconnected edges.
        let graph = DiGraph::<(), ()>::from_edges(&[(0, 1), (2, 3)]);
        let mut ops = ScalarBidirectionalDijkstra::new(&graph, |_| 1.0f64);
        let query = BidirectionalPointToPointQuery::from_default(node_index(0), node_index(3));
        search.solve_query(&query, &mut ops);
        assert_eq!(ops.get_score(), None);
        assert_eq!(ops.get_meeting_node(), None);
    }
}
