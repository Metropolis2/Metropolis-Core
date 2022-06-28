use crate::algo::{earliest_arrival_query, profile_query, EarliestArrivalAllocation};
use crate::bidirectional_ops::{
    BidirectionalDijkstraOps, BidirectionalProfileDijkstra, BidirectionalTCHEA,
    BidirectionalTCHProfileInterval,
};
use crate::bidirectional_search::BidirectionalDijkstraSearch;
use crate::min_queue::{MinPQ, MinPriorityQueue};
use crate::node_data::{
    NodeData, ProfileData, ProfileIntervalData, ProfileIntervalDataWithExtra, ScalarData,
};
use crate::node_map::NodeMap;
use crate::ops::{ProfileDijkstra, ProfileIntervalDijkstra};
use crate::preprocessing::{
    ContractionGraph, ContractionParameters, ToContractEdge, ToContractNode,
};
use crate::query::{BidirectionalPointToPointQuery, SingleSourceQuery};
use crate::search::DijkstraSearch;

use anyhow::{anyhow, Context, Result};
use fixedbitset::FixedBitSet;
use hashbrown::{HashMap, HashSet};
use object_pool::Pool;
use petgraph::graph::{DiGraph, EdgeIndex, EdgeReference, NodeIndex};
use petgraph::visit::{EdgeFiltered, EdgeRef, NodeFiltered};
use petgraph::Direction;
use rayon::prelude::*;
use std::collections::VecDeque;
use ttf::{TTFNum, TTF};

/// Indicate the direction of an edge in the hierarchy.
///
/// - `Upward`: the target node is higher in the hierarchy than the source node.
/// - `Downward`: the target node is lower in the hierarchy than the source node.
#[derive(Debug, PartialEq, Clone, Copy)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum HierarchyDirection {
    Upward,
    Downward,
}

/// Vector representing the edges packed in a shortcut edge.
///
/// Each tuple `(t, Some(n))` indicates that, starting at time `t`, the fastest path from the
/// source to the target of the shortcut edge goes through node `n`.
///
/// A tuple `(t, None)` indicates that, starting at time `t`, the fastest path from the source to
/// the target of the shortcut edge takes the shortcut edge as an original edge.
pub type EdgePack<T> = Vec<(T, Packed)>;

#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum Packed {
    IntermediateNode(NodeIndex),
    OriginalEdge(EdgeIndex),
}

/// Indicate the type of a [HierarchyEdge].
///
/// - `Original`: an edge that exists in the original graph.
/// - `Shortcut`: a virtual edge that represents a shortcut.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum HierarchyEdgeClass<T> {
    Original(EdgeIndex),
    ShortcutThrough(NodeIndex),
    PackedShortcut(EdgePack<T>),
}

/// Structure for edges in a [HierarchyOverlay].
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct HierarchyEdge<T> {
    ttf: TTF<T>,
    direction: HierarchyDirection,
    class: HierarchyEdgeClass<T>,
}

impl<T> HierarchyEdge<T> {
    pub fn new_original(ttf: TTF<T>, direction: HierarchyDirection, id: EdgeIndex) -> Self {
        HierarchyEdge {
            ttf,
            direction,
            class: HierarchyEdgeClass::Original(id),
        }
    }

    pub fn new_shortcut(
        ttf: TTF<T>,
        direction: HierarchyDirection,
        intermediate_node: NodeIndex,
    ) -> Self {
        HierarchyEdge {
            ttf,
            direction,
            class: HierarchyEdgeClass::ShortcutThrough(intermediate_node),
        }
    }

    pub fn new_packed(ttf: TTF<T>, direction: HierarchyDirection, pack: EdgePack<T>) -> Self {
        HierarchyEdge {
            ttf,
            direction,
            class: HierarchyEdgeClass::PackedShortcut(pack),
        }
    }
}

/// Structure representing a graph with a hierarchy of nodes.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct HierarchyOverlay<T> {
    graph: DiGraph<(), HierarchyEdge<T>>,
    order: Vec<usize>,
}

impl<T> HierarchyOverlay<T> {
    /// Create a HierarchyOverlay from a graph of [HierarchyEdge] and a node order.
    ///
    /// The graph edges and the node order must be compatible.
    /// In particular, the [HierarchyDirection] of the edges must match the order of the source and
    /// target in the hierarchy.
    pub fn new_raw(graph: DiGraph<(), HierarchyEdge<T>>, order: Vec<usize>) -> Self {
        HierarchyOverlay { graph, order }
    }

    /// Return the order of the nodes in the hierarchy.
    ///
    /// The order of a node correspond to the value in the returned slice at the index of the node.
    ///
    /// Nodes with higher values are higher in the hierarchy.
    pub fn get_order(&self) -> &[usize] {
        &self.order
    }

    pub fn get_graph(&self) -> &DiGraph<(), HierarchyEdge<T>> {
        &self.graph
    }

    /// Return the upward graph of the [HierarchyOverlay], i.e., the graph with all edges that go
    /// upward in the hierarchy.
    fn get_upward_graph<'a>(
        &'a self,
    ) -> EdgeFiltered<
        &'a DiGraph<(), HierarchyEdge<T>>,
        impl Fn(EdgeReference<'a, HierarchyEdge<T>>) -> bool,
    > {
        EdgeFiltered::from_fn(&self.graph, |e: EdgeReference<'a, HierarchyEdge<T>>| {
            e.weight().direction == HierarchyDirection::Upward
        })
    }

    /// Return the downward graph of the [HierarchyOverlay], i.e., the graph with all edges that go
    /// downward in the hierarchy.
    fn get_downward_graph<'a>(
        &'a self,
    ) -> EdgeFiltered<
        &'a DiGraph<(), HierarchyEdge<T>>,
        impl Fn(EdgeReference<'a, HierarchyEdge<T>>) -> bool,
    > {
        EdgeFiltered::from_fn(&self.graph, |e: EdgeReference<'a, HierarchyEdge<T>>| {
            e.weight().direction == HierarchyDirection::Downward
        })
    }

    /// Return the number of nodes in the overlay graph.
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Return the number of edges in the overlay graph, including shortcut edges.
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }
}

impl<T: TTFNum> HierarchyOverlay<T> {
    /// Construct a HierarchyOverlay from a weighted graph and a hierarchy of nodes.
    ///
    /// The hierarchy of nodes is a function that returns, for each node, its order in the
    /// hierarchy (higher values imply an higher order).
    pub fn construct<N, E, F, G>(
        graph: &DiGraph<N, E>,
        mut edge_cost: F,
        node_order: G,
        parameters: ContractionParameters,
    ) -> HierarchyOverlay<T>
    where
        F: FnMut(EdgeIndex) -> TTF<T>,
        G: Fn(NodeIndex) -> usize,
    {
        let construct_graph = graph.map(
            |node_id, _| ToContractNode::from_order(node_id, node_order(node_id)),
            |edge_id, _| ToContractEdge::new_original(edge_cost(edge_id), edge_id),
        );
        let contraction = ContractionGraph::new(construct_graph, parameters);
        contraction.construct()
    }

    /// Order the nodes and construct a HierarchyOverlay from a weighted graph.
    pub fn order<N, E, F>(
        graph: &DiGraph<N, E>,
        mut edge_cost: F,
        parameters: ContractionParameters,
    ) -> HierarchyOverlay<T>
    where
        F: FnMut(EdgeIndex) -> TTF<T>,
    {
        let construct_graph = graph.map(
            |node_id, _| ToContractNode::new(node_id),
            |edge_id, _| ToContractEdge::new_original(edge_cost(edge_id), edge_id),
        );
        let contraction = ContractionGraph::new(construct_graph, parameters);
        contraction.order()
    }

    pub fn complexity(&self) -> usize {
        self.graph.edge_weights().map(|e| e.ttf.complexity()).sum()
    }

    pub fn approximate(&mut self, error: T) {
        self.graph
            .edge_weights_mut()
            .for_each(|e| e.ttf.approximate(error));
    }

    /// Return the unpacked version of a path, i.e., return the path as a vector of *original*
    /// edges.
    fn unpack_path(&self, path: &[NodeIndex], departure_time: T) -> Result<Vec<EdgeIndex>> {
        let mut unpacked_path = Vec::new();
        let mut current_time = departure_time;
        for (&source, &target) in path.iter().zip(path[1..].iter()) {
            self.unpack_edge(source, target, &mut current_time, &mut unpacked_path)
                .with_context(|| {
                    format!(
                        "Failed to unpack edge from {:?} to {:?} at time {:?}",
                        source, target, current_time
                    )
                })?;
        }
        Ok(unpacked_path)
    }

    /// Unpack recusively an edge in a path, i.e., unpack shortcut edges until a original edge is
    /// found.
    fn unpack_edge(
        &self,
        source: NodeIndex,
        target: NodeIndex,
        current_time: &mut T,
        path: &mut Vec<EdgeIndex>,
    ) -> Result<()> {
        if let Some(edge) = self.graph.find_edge(source, target) {
            match &self.graph[edge].class {
                &HierarchyEdgeClass::Original(id) => {
                    path.push(id);
                    *current_time = *current_time + self.graph[edge].ttf.eval(*current_time);
                }
                &HierarchyEdgeClass::ShortcutThrough(inter_node) => {
                    self.unpack_edge(source, inter_node, current_time, path)?;
                    self.unpack_edge(inter_node, target, current_time, path)?;
                }
                HierarchyEdgeClass::PackedShortcut(pack) => {
                    assert!(*current_time >= pack[0].0);
                    let pack_id = match pack
                        .binary_search_by(|(t, _)| t.partial_cmp(current_time).unwrap())
                    {
                        Ok(i) => i,
                        Err(i) => i - 1,
                    };
                    match pack[pack_id].1 {
                        Packed::IntermediateNode(inter_node) => {
                            self.unpack_edge(source, inter_node, current_time, path)?;
                            self.unpack_edge(inter_node, target, current_time, path)?;
                        }
                        Packed::OriginalEdge(id) => {
                            path.push(id);
                            *current_time =
                                *current_time + self.graph[edge].ttf.eval(*current_time);
                        }
                    }
                }
            }
        } else {
            return Err(anyhow!(
                "Cannot find edge from {:?} to {:?}",
                source,
                target
            ));
        }
        Ok(())
    }

    /// Return the earliest arrival time, and its associated path, when going from `source` to
    /// `target`, starting at time `deparure_time`.
    pub fn earliest_arrival_query<PQ1, PQ2, PQ3, CM>(
        &self,
        source: NodeIndex,
        target: NodeIndex,
        departure_time: T,
        alloc: &mut EarliestArrivalAllocation<
            ScalarData<T>,
            ProfileIntervalData<T>,
            ScalarData<T>,
            PQ1,
            PQ2,
            PQ3,
        >,
        candidate_map: &mut CM,
    ) -> Result<Option<(T, Vec<EdgeIndex>)>>
    where
        PQ1: MinPriorityQueue<Key = NodeIndex, Value = T>,
        PQ2: MinPriorityQueue<Key = NodeIndex, Value = T>,
        PQ3: MinPriorityQueue<Key = NodeIndex, Value = T>,
        CM: NodeMap<Node = NodeIndex, Value = (T, T)>,
    {
        alloc.reset();
        candidate_map.reset();
        let zero = T::zero();
        let query =
            BidirectionalPointToPointQuery::new(source, target, departure_time, [zero, zero]);
        let edge_label = |e: EdgeReference<_>| &self.graph[e.id()].ttf;
        let upward_graph = &self.get_upward_graph();
        let downward_graph = &self.get_downward_graph();
        let mut ops = BidirectionalTCHEA::new_raw(
            upward_graph,
            edge_label,
            downward_graph,
            edge_label,
            candidate_map,
        );
        if let Some((arrival_time, packed_path)) = earliest_arrival_query(
            alloc,
            &query,
            &mut ops,
            &self.get_downward_graph(),
            edge_label,
        )
        .context("Failed to run the TCHEA query")?
        {
            let unpacked_path = self
                .unpack_path(&packed_path, departure_time)
                .with_context(|| {
                    format!(
                        "Failed to unpack path {:?} with departure time {:?}",
                        packed_path, departure_time
                    )
                })?;
            Ok(Some((arrival_time, unpacked_path)))
        } else {
            Ok(None)
        }
    }

    /// Return the travel-time profile from `source` to `target`.
    ///
    /// This uses Algorithm 7 in Batz et al. (2013)[^ref].
    ///
    /// [^ref]: Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013).
    ///     Minimum time-dependent travel times with contraction hierarchies.
    ///     _Journal of Experimental Algorithmics (JEA)_, _18_, 1-1.
    pub fn profile_query<PQ1, PQ2, PQ3, PQ4, CM>(
        &self,
        source: NodeIndex,
        target: NodeIndex,
        interval_search: &mut BidirectionalDijkstraSearch<
            ProfileIntervalDataWithExtra<T>,
            ProfileIntervalDataWithExtra<T>,
            PQ1,
            PQ2,
        >,
        profile_search: &mut BidirectionalDijkstraSearch<ProfileData<T>, ProfileData<T>, PQ3, PQ4>,
        mut candidate_map: &mut CM,
    ) -> Option<TTF<T>>
    where
        PQ1: MinPriorityQueue<Key = NodeIndex, Value = T>,
        PQ2: MinPriorityQueue<Key = NodeIndex, Value = T>,
        PQ3: MinPriorityQueue<Key = NodeIndex, Value = T>,
        PQ4: MinPriorityQueue<Key = NodeIndex, Value = T>,
        CM: NodeMap<Node = NodeIndex, Value = T>,
    {
        if source == target {
            return Some(Default::default());
        }
        interval_search.reset();
        candidate_map.reset();
        let query = BidirectionalPointToPointQuery::from_default(source, target);
        let edge_label = |e: EdgeReference<_>| &self.graph[e.id()].ttf;
        let upward_graph = &self.get_upward_graph();
        let downward_graph = &self.get_downward_graph();
        let mut ops = BidirectionalTCHProfileInterval::new_raw(
            upward_graph,
            edge_label,
            downward_graph,
            edge_label,
            &mut candidate_map,
        );
        interval_search.solve_query(&query, &mut ops);
        let bound = *ops.forward_ops().0.get_bound().get().unwrap();
        let forw_cone = self.get_cone(
            ops.get_candidates(),
            bound,
            interval_search.get_forward_search().node_map(),
        );
        let back_cone = self.get_cone(
            ops.get_candidates(),
            bound,
            interval_search.get_backward_search().node_map(),
        );

        candidate_map.reset();
        let query = BidirectionalPointToPointQuery::from_default(source, target);
        let upward_graph = self.get_upward_graph();
        let upward_cone = NodeFiltered(&upward_graph, forw_cone);
        let downward_graph = self.get_downward_graph();
        let downward_cone = NodeFiltered(&downward_graph, back_cone);
        let mut ops = BidirectionalProfileDijkstra::new_raw(
            &upward_cone,
            edge_label,
            &downward_cone,
            edge_label,
            candidate_map,
        );
        profile_query(profile_search, &query, &mut ops)
    }

    fn get_cone<CM, D>(
        &self,
        candidates: &CM,
        bound: T,
        data: &HashMap<NodeIndex, D>,
    ) -> FixedBitSet
    where
        CM: NodeMap<Node = NodeIndex, Value = T>,
        D: NodeData<Predecessor = HashSet<NodeIndex>>,
    {
        // TODO: The cone returned is too large as it contains edges whose both endpoints are in
        // the fixedbitset, even though the edges do not appear in the predecessor map.
        // We should use a EdgeFiltered instead.
        // Maybe build a hash table of successors?
        let mut bs = FixedBitSet::with_capacity(self.graph.node_count());
        let mut stack = VecDeque::new();
        for (candidate, &lb) in candidates.iter() {
            if lb <= bound {
                stack.push_front(candidate);
            }
        }
        while let Some(node) = stack.pop_front() {
            if !bs.put(node.index()) {
                if let Some(pp) = data.get(&node).unwrap().predecessor() {
                    for &p in pp {
                        stack.push_back(p);
                    }
                }
            }
        }
        bs
    }

    pub fn get_search_spaces<'a>(
        &self,
        sources: impl IntoParallelIterator<Item = &'a NodeIndex>,
        targets: impl IntoParallelIterator<Item = &'a NodeIndex>,
    ) -> SearchSpaces<T> {
        let pool = Pool::new(rayon::current_num_threads(), Default::default);
        let forward = sources
            .into_par_iter()
            .map_init(
                || pool.pull(Default::default),
                |alloc, &node_id| {
                    (
                        node_id,
                        self.get_search_space_from(node_id, Direction::Outgoing, alloc),
                    )
                },
            )
            .collect();
        let backward = targets
            .into_par_iter()
            .map_init(
                || pool.pull(Default::default),
                |alloc, &node_id| {
                    (
                        node_id,
                        self.get_search_space_from(node_id, Direction::Incoming, alloc),
                    )
                },
            )
            .collect();
        SearchSpaces { forward, backward }
    }

    fn get_search_space_from(
        &self,
        node: NodeIndex,
        direction: Direction,
        alloc: &mut AllocatedSearchSpaceData<T>,
    ) -> SearchSpace<T> {
        alloc.interval_search.reset();
        alloc.profile_search.reset();
        let interval_query = SingleSourceQuery::from_default(node);
        let profile_query = SingleSourceQuery::from_default(node);
        let edge_label = |e: EdgeReference<_>| &self.graph[e.id()].ttf;
        match direction {
            Direction::Outgoing => {
                let graph = self.get_upward_graph();
                let mut ops =
                    ProfileIntervalDijkstra::new_forward_with_stall_on_demand(&graph, edge_label);
                alloc.interval_search.solve_query(&interval_query, &mut ops);
                let cone = EdgeFiltered::from_fn(&graph, |edge| {
                    alloc
                        .interval_search
                        .get_predecessor(&edge.target())
                        .map(|p| p.contains(&edge.source()))
                        .unwrap_or(false)
                });
                let mut ops = ProfileDijkstra::new_forward(&cone, edge_label);
                alloc.profile_search.solve_query(&profile_query, &mut ops);
            }
            Direction::Incoming => {
                let graph = self.get_downward_graph();
                let mut ops =
                    ProfileIntervalDijkstra::new_backward_with_stall_on_demand(&graph, edge_label);
                alloc.interval_search.solve_query(&interval_query, &mut ops);
                let cone = EdgeFiltered::from_fn(&graph, |edge| {
                    alloc
                        .interval_search
                        .get_predecessor(&edge.source())
                        .map(|p| p.contains(&edge.target()))
                        .unwrap_or(false)
                });
                let mut ops = ProfileDijkstra::new_backward(&cone, edge_label);
                alloc.profile_search.solve_query(&profile_query, &mut ops);
            }
        }
        let map = std::mem::take(alloc.profile_search.node_map_mut());
        map.into_iter().map(|(k, d)| (k, d.0)).collect()
    }
}

#[derive(Default)]
struct AllocatedSearchSpaceData<T: PartialOrd + TTFNum> {
    interval_search: DijkstraSearch<ProfileIntervalData<T>, MinPQ<NodeIndex, T>>,
    profile_search: DijkstraSearch<ProfileData<T>, MinPQ<NodeIndex, T>>,
}

pub type SearchSpace<T> = HashMap<NodeIndex, TTF<T>>;

pub struct SearchSpaces<T> {
    forward: HashMap<NodeIndex, SearchSpace<T>>,
    backward: HashMap<NodeIndex, SearchSpace<T>>,
}

impl<T> SearchSpaces<T> {
    pub fn get_forward_search_space(&self, node: &NodeIndex) -> Option<&SearchSpace<T>> {
        self.forward.get(node)
    }

    pub fn get_backward_search_space(&self, node: &NodeIndex) -> Option<&SearchSpace<T>> {
        self.backward.get(node)
    }
}

impl<T: TTFNum> SearchSpaces<T> {
    pub fn approximate(&mut self, error: T) {
        self.forward.par_values_mut().for_each(|search_space| {
            search_space
                .values_mut()
                .for_each(|ttf| ttf.approximate(error))
        });
    }
}
