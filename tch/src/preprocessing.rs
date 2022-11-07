// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::cmp::Ordering;
use std::collections::VecDeque;

use either::Either;
use fixedbitset::FixedBitSet;
use hashbrown::hash_map::{Entry, HashMap};
use hashbrown::HashSet;
use indicatif::{ProgressBar, ProgressStyle};
use log::{debug, log_enabled, Level};
use object_pool::Pool;
use ordered_float::OrderedFloat;
use petgraph::graph::{node_index, DiGraph, EdgeIndex, EdgeReference, NodeIndex};
use petgraph::visit::{EdgeRef, IntoNodeReferences, NodeFiltered, VisitMap, Visitable};
use petgraph::Direction;
use rayon::prelude::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::{TTFNum, TTF};

use crate::contraction_hierarchies::{
    EdgePack, HierarchyDirection, HierarchyEdge, HierarchyEdgeClass, HierarchyOverlay, Packed,
};
use crate::min_queue::MinPQ;
use crate::node_data::NodeDataWithExtra;
use crate::ops::{
    HopLimitedDijkstra, ProfileDijkstra, ThinProfileIntervalDijkstra, TimeDependentDijkstra,
};
use crate::query::PointToPointQuery;
use crate::search::DijkstraSearch;

/// Structure that represents a set of parameters used when contracting a graph.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Contraction Parameters")]
#[schemars(
    description = "Set of parameters used when contracting a graph. See Batz, Geisberger, Sanders and Vetter (2013) for a description of the parameters."
)]
pub struct ContractionParameters {
    edge_quotient_weight: f64,
    hierarchy_depth_weight: f64,
    unpacked_edges_quotient_weight: f64,
    complexity_quotient_weight: f64,
    thin_profile_interval_hop_limit: u8,
    /// Number of threads to use for the parallelized parts of the code.
    num_threads: usize,
}

impl Default for ContractionParameters {
    fn default() -> Self {
        ContractionParameters::new(2.0, 1.0, 1.0, 2.0, 16, rayon::current_num_threads())
    }
}

impl ContractionParameters {
    /// Creates a new set of ContractionParameters.
    pub fn new(
        edge_quotient_weight: f64,
        hierarchy_depth_weight: f64,
        unpacked_edges_quotient_weight: f64,
        complexity_quotient_weight: f64,
        thin_profile_interval_hop_limit: u8,
        num_threads: usize,
    ) -> Self {
        ContractionParameters {
            edge_quotient_weight,
            hierarchy_depth_weight,
            unpacked_edges_quotient_weight,
            complexity_quotient_weight,
            thin_profile_interval_hop_limit,
            num_threads,
        }
    }
}

/// Results from a witness search from node contraction.
#[derive(Clone, Copy)]
enum CachedResult {
    /// A witness was found, i.e., there is a witness profile which guarantees that the shortcut is
    /// not needed.
    Witness,
    /// No witness was found.
    /// We store the complexity of the shortcut edge and the number of packed edges, for later use.
    NoWitness(usize, usize),
}

/// A map that stores the result of a witness search for some shortcut edges when simulating the
/// contraction of a node.
type ContractionCacheEntry = HashMap<(NodeIndex, NodeIndex), CachedResult>;

/// A vector that stores the results of the witness searches for nodes whose contraction was
/// previously simulated.
type ContractionCache = Vec<ContractionCacheEntry>;

/// The shortcut edges resulting from a node contraction.
type ContractionResults<T> = (NodeIndex, NodeIndex, ToContractEdge<T>);

/// Structure for nodes in a [ContractionGraph].
#[derive(Clone, Debug, Deserialize, Serialize)]
pub(crate) struct ToContractNode {
    id: NodeIndex,
    /// Order of the node in the hierarchy.
    /// Set to 0 if the order has not been determined yet.
    order: usize,
    /// Depth of the node.
    /// A larger value implies that the node is close to nodes that are already contracted.
    depth: usize,
    /// Tentative cost of the node, that represents how "attractive" the node is to be contracted.
    cost: OrderedFloat<f64>,
}

impl ToContractNode {
    pub(crate) fn new(id: NodeIndex) -> Self {
        ToContractNode {
            id,
            order: 0,
            depth: 1,
            cost: OrderedFloat(0.),
        }
    }

    /// Creates a new node with a known order.
    pub(crate) fn from_order(id: NodeIndex, order: usize) -> Self {
        ToContractNode {
            id,
            order,
            depth: 1,
            cost: OrderedFloat(0.),
        }
    }
}

/// Structure for edges in a [ContractionGraph].
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub(crate) struct ToContractEdge<T> {
    /// Current metric of the edge.
    ttf: TTF<T>,
    /// Number of packed edge that a shortcut edge represents (1 if this is not a shortcut edge).
    nb_packed: usize,
    /// Type of the edge (Original or Shortcut).
    class: HierarchyEdgeClass<T>,
}

impl<T> ToContractEdge<T> {
    fn new(ttf: TTF<T>, nb_packed: usize, class: HierarchyEdgeClass<T>) -> Self {
        ToContractEdge {
            ttf,
            nb_packed,
            class,
        }
    }

    /// Creates a new original edge.
    pub(crate) fn new_original(ttf: TTF<T>, id: EdgeIndex) -> Self {
        ToContractEdge::new(ttf, 1, HierarchyEdgeClass::Original(id))
    }

    /// Creates a new shortcut edge.
    fn new_shortcut(ttf: TTF<T>, nb_packed: usize, node: NodeIndex) -> Self {
        ToContractEdge::new(ttf, nb_packed, HierarchyEdgeClass::ShortcutThrough(node))
    }

    /// Creates a new shortcut edge.
    fn new_packed(ttf: TTF<T>, nb_packed: usize, pack: EdgePack<T>) -> Self {
        ToContractEdge::new(ttf, nb_packed, HierarchyEdgeClass::PackedShortcut(pack))
    }
}

type ThinProfileIntervalDijkstraSearch<T> =
    DijkstraSearch<NodeDataWithExtra<([T; 2], Option<[NodeIndex; 2]>), u8>, MinPQ<NodeIndex, T>>;

type SampleDijkstraSearch<T> = DijkstraSearch<(T, Option<NodeIndex>), MinPQ<NodeIndex, T>>;

type ProfileDijkstraSearch<T> =
    DijkstraSearch<(TTF<T>, Option<HashSet<NodeIndex>>), MinPQ<NodeIndex, T>>;

struct AllocatedDijkstraData<T: PartialOrd> {
    interval_search: ThinProfileIntervalDijkstraSearch<T>,
    sample_search: SampleDijkstraSearch<T>,
    profile_search: ProfileDijkstraSearch<T>,
    hop_map: HashMap<NodeIndex, u8>,
}

impl<T: PartialOrd> Default for AllocatedDijkstraData<T> {
    fn default() -> Self {
        AllocatedDijkstraData {
            interval_search: DijkstraSearch::new(HashMap::new(), MinPQ::with_default_hasher()),
            // NOTE: No predecessor needed here.
            sample_search: DijkstraSearch::new(HashMap::new(), MinPQ::with_default_hasher()),
            // NOTE: No predecessor needed here.
            profile_search: DijkstraSearch::new(HashMap::new(), MinPQ::with_default_hasher()),
            hop_map: HashMap::new(),
        }
    }
}

impl<T> AllocatedDijkstraData<T>
where
    T: Copy + PartialOrd,
{
    fn reset(&mut self) {
        self.interval_search.reset();
        self.sample_search.reset();
        self.profile_search.reset();
        self.hop_map.clear();
    }
}

/// Temporary graph used to construct a [HierarchyOverlay].
pub(crate) struct ContractionGraph<T: PartialOrd> {
    graph: DiGraph<ToContractNode, ToContractEdge<T>>,
    /// Parameters used during the contraction.
    parameters: ContractionParameters,
    /// Pre-allocated structures for the dijkstra runs.
    pool: Pool<AllocatedDijkstraData<T>>,
    new_ids: Vec<Option<NodeIndex>>,
    order: Vec<usize>,
    next_order: usize,
    edges: Vec<(NodeIndex, NodeIndex, HierarchyEdge<T>)>,
}

impl<T: TTFNum> ContractionGraph<T> {
    /// Creates a new ContractionGraph from a graph of [ToContractNode] and [ToContractEdge].
    pub(crate) fn new(
        graph: DiGraph<ToContractNode, ToContractEdge<T>>,
        parameters: ContractionParameters,
    ) -> Self {
        let pool = Pool::new(parameters.num_threads, Default::default);

        let mut order = Vec::new();
        order.resize(graph.node_count(), 0);

        let mut new_ids = Vec::with_capacity(graph.node_count());
        for i in 0..graph.node_count() {
            new_ids.push(Some(node_index(i)));
        }

        ContractionGraph {
            graph,
            parameters,
            pool,
            new_ids,
            order,
            next_order: 1,
            edges: Vec::new(),
        }
    }

    /// Constructs a [HierarchyOverlay] from the ContractionGraph, i.e., contract all the nodes in
    /// the given hierarchy order.
    pub(crate) fn construct(mut self) -> HierarchyOverlay<T> {
        while self.graph.node_count() > 0 {
            // Find the largest set of independent nodes than can be contracted in parallel.
            // A node is contracted if its order is smaller than the order of all its neighbors.
            let nodes_to_contract: HashSet<_> = self
                .graph
                .node_references()
                .filter_map(|(node_id, weight)| {
                    if self
                        .graph
                        .neighbors_undirected(node_id)
                        .all(|n| self.graph[n].order > weight.order)
                    {
                        Some(weight.id)
                    } else {
                        None
                    }
                })
                .collect();
            if nodes_to_contract.is_empty() {
                let order: Vec<_> = self.graph.node_references().map(|(_, n)| n.order).collect();
                panic!(
                    "Invalid node order (it must be a total order): {:.50?}",
                    order
                );
            }
            // Contract the new batch of nodes.
            // We do not need a cache so with use an empty cache.
            self.contract_nodes(&nodes_to_contract, &mut vec![]);
            debug!(
                "{} remaining nodes to be contracted",
                self.graph.node_count()
            );
            debug!("Nb edges: {}", self.edges.len() + self.graph.edge_count());
            self.build_remaining_graph(&nodes_to_contract);
        }
        self.into_hierarchy_overlay()
    }

    /// Orders the nodes and construct a [HierarchyOverlay] from the ContractionGraph.
    pub(crate) fn order(mut self) -> HierarchyOverlay<T> {
        debug!("Starting ordering");
        // Initialize a ContractionCache.
        let mut cache = ContractionCache::new();
        cache.resize_with(self.graph.node_count(), HashMap::new);
        // Compute initial tentative cost for all nodes.
        debug!("Computing initial costs");
        let costs: Vec<(NodeIndex, OrderedFloat<f64>)> = cache
            .par_iter_mut()
            .enumerate()
            .map_init(
                || self.pool.pull(Default::default),
                |alloc, (i, cache)| {
                    let node_id = node_index(i);
                    let cost = self.get_tentative_cost(node_id, cache, alloc);
                    (node_id, cost)
                },
            )
            .collect();
        for (node_id, cost) in costs.into_iter() {
            self.graph[node_id].cost = cost;
        }
        // Main loop.
        debug!("Contracting graph");
        let bp = if log_enabled!(Level::Debug) {
            ProgressBar::new(self.graph.node_count() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        while self.graph.node_count() > 0 {
            // Find the largest set of independent nodes than can be contracted in parallel.
            let nodes_to_contract: HashSet<_> = self
                .graph
                .node_references()
                .filter_map(|(node_id, node_weight)| {
                    let cost = node_weight.cost;
                    let cond = |n: NodeIndex, w: &ToContractNode| {
                        (n <= node_id || w.cost >= cost) && (n >= node_id || w.cost > cost)
                    };
                    if self.check_2_hop_neighborhood(node_id, cond) {
                        Some(node_weight.id)
                    } else {
                        None
                    }
                })
                .collect();
            // `nodes_to_contract` cannot be empty as there is at least one remaining node that
            // should be selected.
            assert!(!nodes_to_contract.is_empty());
            // Contract a new batch of nodes.
            self.contract_nodes(&nodes_to_contract, &mut cache);
            for &node_id in nodes_to_contract.iter() {
                // Clear the cache for this node as it is no longer needed.
                cache[node_id.index()].clear();
            }
            // Update the depth of the neighbors of the contracted nodes.
            let nodes_to_update = self.update_depths(&nodes_to_contract);
            // Update the remaining graph.
            self.build_remaining_graph(&nodes_to_contract);
            // Update the tentative cost of the neighbors of the contracted nodes.
            let new_costs: Vec<(NodeIndex, OrderedFloat<f64>)> = cache
                .par_iter_mut()
                .enumerate()
                .map_init(
                    || self.pool.pull(Default::default),
                    |alloc, (i, cache)| {
                        if nodes_to_update.contains(&node_index(i)) {
                            let new_node_id = self.new_ids[i].unwrap();
                            let cost = self.get_tentative_cost(new_node_id, cache, alloc);
                            Some((new_node_id, cost))
                        } else {
                            None
                        }
                    },
                )
                .flatten()
                .collect();
            for (node_id, cost) in new_costs.into_iter() {
                self.graph[node_id].cost = cost;
            }
            bp.inc(nodes_to_contract.len() as u64);
        }
        bp.finish_and_clear();
        self.into_hierarchy_overlay()
    }

    /// Updates the depth of the neighbor nodes of the given nodes and return a vector with all
    /// neighbor nodes that were updated.
    fn update_depths(&mut self, nodes: &HashSet<NodeIndex>) -> HashSet<NodeIndex> {
        let mut updated = HashSet::with_capacity(nodes.len() * 4);
        for &old_node_id in nodes {
            let new_node_id = self.new_ids[old_node_id.index()].unwrap();
            let depth = self.graph[new_node_id].depth;
            let mut neighbors = self.graph.neighbors_undirected(new_node_id).detach();
            while let Some(neighbor) = neighbors.next_node(&self.graph) {
                self.graph[neighbor].depth = std::cmp::max(depth + 1, self.graph[neighbor].depth);
                updated.insert(self.graph[neighbor].id);
            }
        }
        updated
    }

    /// Converts a successfully contracted [ContractionGraph] into a [HierarchyOverlay].
    fn into_hierarchy_overlay(self) -> HierarchyOverlay<T> {
        // Build the graph.
        let graph = DiGraph::<(), HierarchyEdge<T>>::from_edges(self.edges);
        HierarchyOverlay::new_raw(graph, self.order)
    }

    /// Contracts a batch of nodes in parallel.
    fn contract_nodes(
        &mut self,
        nodes_to_contract: &HashSet<NodeIndex>,
        cache: &mut ContractionCache,
    ) {
        let contraction_results: Vec<_> = nodes_to_contract
            .par_iter()
            .map_init(
                || self.pool.pull(Default::default),
                |alloc, &old_node_id| {
                    self.get_node_contraction(
                        self.new_ids[old_node_id.index()].unwrap(),
                        cache.get(old_node_id.index()),
                        alloc,
                    )
                },
            )
            .flatten()
            .collect();
        self.apply_contraction(contraction_results, cache);
    }

    /// Applies a batch of [ContractionResults], i.e., create new shortcuts and merge existing
    /// shortcuts.
    fn apply_contraction(
        &mut self,
        contractions: Vec<ContractionResults<T>>,
        cache: &mut ContractionCache,
    ) {
        let mut merged_edges = HashSet::with_capacity(contractions.len());
        for (source, target, shortcut) in contractions {
            if let Some(existing_edge) = self.graph.find_edge(source, target) {
                merged_edges.insert((self.graph[source].id, self.graph[target].id));
                merge_edges(shortcut, &mut self.graph[existing_edge]);
            } else {
                self.graph.add_edge(source, target, shortcut);
            }
        }
        // Remove from the cache all entries related to edges that where merged (the entry is no
        // longer valid).
        cache
            .par_iter_mut()
            .enumerate()
            .for_each(|(i, node_cache)| {
                node_cache.retain(|&(u, v), _| {
                    !merged_edges.contains(&(u, node_index(i)))
                        && !merged_edges.contains(&(node_index(i), v))
                })
            });
    }

    fn build_remaining_graph(&mut self, nodes_to_contract: &HashSet<NodeIndex>) {
        let graph = std::mem::take(&mut self.graph);
        let (nodes, edges) = graph.into_nodes_edges();
        self.new_ids.fill(None);
        let mut original_ids = HashMap::with_capacity(nodes_to_contract.len());
        self.graph = DiGraph::with_capacity(nodes.len() - nodes_to_contract.len(), edges.len());
        for (i, node) in nodes.into_iter().enumerate() {
            let old_id = node.weight.id;
            original_ids.insert(node_index(i), old_id);
            if nodes_to_contract.contains(&old_id) {
                self.order[node.weight.id.index()] = self.next_order;
                self.next_order += 1;
            } else {
                let new_id = self.graph.add_node(node.weight);
                self.new_ids[old_id.index()] = Some(new_id);
            }
        }
        for edge in edges {
            let &source_id = original_ids.get(&edge.source()).unwrap();
            let &target_id = original_ids.get(&edge.target()).unwrap();
            if nodes_to_contract.contains(&source_id) || nodes_to_contract.contains(&target_id) {
                debug_assert!(
                    nodes_to_contract.contains(&source_id) ^ nodes_to_contract.contains(&target_id),
                    "Source and target cannot be both contracted"
                );
                let dir = if nodes_to_contract.contains(&source_id) {
                    HierarchyDirection::Upward
                } else {
                    HierarchyDirection::Downward
                };
                let hierarchy_edge = match edge.weight.class {
                    HierarchyEdgeClass::Original(id) => {
                        HierarchyEdge::new_original(edge.weight.ttf, dir, id)
                    }
                    HierarchyEdgeClass::ShortcutThrough(node) => {
                        HierarchyEdge::new_shortcut(edge.weight.ttf, dir, node)
                    }
                    HierarchyEdgeClass::PackedShortcut(pack) => {
                        HierarchyEdge::new_packed(edge.weight.ttf, dir, pack)
                    }
                };
                self.edges.push((source_id, target_id, hierarchy_edge));
            } else {
                self.graph.add_edge(
                    self.new_ids[source_id.index()].unwrap(),
                    self.new_ids[target_id.index()].unwrap(),
                    edge.weight,
                );
            }
        }
    }

    /// Checks if a condition is valid for all 2-hop neighbors of a given node.
    fn check_2_hop_neighborhood<F>(&self, node: NodeIndex, condition: F) -> bool
    where
        F: Fn(NodeIndex, &ToContractNode) -> bool,
    {
        self.graph.neighbors_undirected(node).all(|n1| {
            condition(n1, &self.graph[n1])
                && self
                    .graph
                    .neighbors_undirected(n1)
                    .all(|n2| condition(n2, &self.graph[n2]))
        })
    }

    /// Computes the tentative cost of a node.
    ///
    /// The contraction cache of the node is updated at the same time.
    fn get_tentative_cost(
        &self,
        node: NodeIndex,
        contraction_cache: &mut ContractionCacheEntry,
        alloc: &mut AllocatedDijkstraData<T>,
    ) -> OrderedFloat<f64> {
        let simulated_contraction_results =
            self.get_simulated_node_contraction(node, contraction_cache, alloc);
        let nb_edges_inserted = simulated_contraction_results.len();
        // Count the number breakpoints and original edges that the new edges represent.
        let (nb_breakpoints_inserted, nb_unpacked_inserted) = simulated_contraction_results
            .iter()
            .fold((0, 0), |tot, (complexity, nb_packed)| {
                (tot.0 + complexity, tot.1 + nb_packed)
            });
        let (nb_edges_removed, nb_breakpoints_removed, nb_unpacked_removed) =
            self.get_nb_removed(node);

        // 1. Edge quotient.
        let edge_quotient = nb_edges_inserted as f64 / std::cmp::max(1, nb_edges_removed) as f64;
        // 2. Hierarchy depth.
        let hierarchy_depth = self.graph[node].depth;
        // 3. Unpacked edge quotient.
        let unpacked_edges_quotient =
            nb_unpacked_inserted as f64 / std::cmp::max(1, nb_unpacked_removed) as f64;
        // 4. Complexity quotient.
        let complexity_quotient =
            nb_breakpoints_inserted as f64 / std::cmp::max(1, nb_breakpoints_removed) as f64;

        let cost = OrderedFloat(
            self.parameters.edge_quotient_weight * edge_quotient
                + self.parameters.hierarchy_depth_weight * hierarchy_depth as f64
                + self.parameters.unpacked_edges_quotient_weight * unpacked_edges_quotient
                + self.parameters.complexity_quotient_weight * complexity_quotient,
        );
        debug_assert!(
            cost.is_finite(),
            "Invalid cost (quotient: {:?}, depth: {:?}, unpacked quotient: {:?}, complexity: {:?})",
            edge_quotient,
            hierarchy_depth,
            unpacked_edges_quotient,
            complexity_quotient
        );
        cost
    }

    /// Returns the number of edges, unpacked edges and breakpoints removed when the given node is
    /// contracted.
    fn get_nb_removed(&self, node: NodeIndex) -> (usize, usize, usize) {
        let sum = |tot: (usize, usize, usize), edge: EdgeReference<'_, ToContractEdge<T>>| {
            (
                tot.0 + 1,
                tot.1 + edge.weight().ttf.complexity(),
                tot.2 + edge.weight().nb_packed,
            )
        };
        let nb_out = self
            .graph
            .edges_directed(node, Direction::Outgoing)
            .fold((0, 0, 0), sum);
        let nb_in = self
            .graph
            .edges_directed(node, Direction::Incoming)
            .fold((0, 0, 0), sum);
        (nb_out.0 + nb_in.0, nb_out.1 + nb_in.1, nb_out.2 + nb_in.2)
    }

    /// Returns the results of the simulated contraction of a node as a vector of tuples `(usize,
    /// usize)` that represent the complexity and the number of packed original edges of the new
    /// shortcut edges to insert.
    fn get_simulated_node_contraction(
        &self,
        node: NodeIndex,
        cache: &mut ContractionCacheEntry,
        alloc: &mut AllocatedDijkstraData<T>,
    ) -> Vec<(usize, usize)> {
        self.iter_remaining_edge_pairs(node)
            .filter_map(|(in_edge, out_edge)| {
                match self.get_simulated_edge_contraction(in_edge, out_edge, cache, alloc) {
                    CachedResult::NoWitness(complexity, nb_packed) => Some((complexity, nb_packed)),
                    // Ignore the edge pairs for which a witness was found.
                    _ => None,
                }
            })
            .collect()
    }

    /// Returns the results of a witness search to check whether a shortcut edge that represents
    /// edges `in_edge` and `out_edge` is necessary.
    fn get_simulated_edge_contraction(
        &self,
        in_edge: EdgeReference<'_, ToContractEdge<T>>,
        out_edge: EdgeReference<'_, ToContractEdge<T>>,
        cache: &mut ContractionCacheEntry,
        alloc: &mut AllocatedDijkstraData<T>,
    ) -> CachedResult {
        match cache.entry((
            self.graph[in_edge.source()].id,
            self.graph[out_edge.target()].id,
        )) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let edge_score = in_edge.weight().ttf.link(&out_edge.weight().ttf);
                if self.search_witness(in_edge.source(), out_edge.target(), &edge_score, alloc) {
                    // Witness found.
                    *e.insert(CachedResult::Witness)
                } else {
                    // No witness was found, we add the shortcut edge.
                    *e.insert(CachedResult::NoWitness(
                        edge_score.complexity(),
                        in_edge.weight().nb_packed + out_edge.weight().nb_packed,
                    ))
                }
            }
        }
    }

    /// Returns an iterator over all the pairs (in_edge, out_edge) of a node in the remaining
    /// graph.
    fn iter_remaining_edge_pairs(
        &self,
        node: NodeIndex,
    ) -> impl Iterator<
        Item = (
            EdgeReference<'_, ToContractEdge<T>>,
            EdgeReference<'_, ToContractEdge<T>>,
        ),
    > {
        self.graph
            .edges_directed(node, Direction::Incoming)
            .flat_map(move |in_edge| {
                std::iter::repeat(in_edge)
                    .zip(self.graph.edges_directed(node, Direction::Outgoing))
                    .filter(|(in_edge, out_edge)| in_edge.source() != out_edge.target())
            })
    }

    /// Returns the new shortcut edges resulting from the contraction of a node.
    fn get_node_contraction(
        &self,
        node: NodeIndex,
        cache: Option<&HashMap<(NodeIndex, NodeIndex), CachedResult>>,
        alloc: &mut AllocatedDijkstraData<T>,
    ) -> Vec<ContractionResults<T>> {
        self.iter_remaining_edge_pairs(node)
            .filter_map(|(in_edge, out_edge)| {
                self.get_edge_contraction(in_edge, out_edge, cache, alloc)
            })
            .collect()
    }

    /// Returns the new shortcut edge (if needed) representing edges `in_edge` and `out_edge`.
    fn get_edge_contraction<'b>(
        &self,
        in_edge: EdgeReference<'b, ToContractEdge<T>>,
        out_edge: EdgeReference<'b, ToContractEdge<T>>,
        cache: Option<&HashMap<(NodeIndex, NodeIndex), CachedResult>>,
        alloc: &mut AllocatedDijkstraData<T>,
    ) -> Option<ContractionResults<T>> {
        let mut is_cached = false;
        match cache.and_then(|c| {
            c.get(&(
                self.graph[in_edge.source()].id,
                self.graph[out_edge.target()].id,
            ))
        }) {
            Some(CachedResult::Witness) => {
                // The current contraction was already evaluated and a witness existed.
                return None;
            }
            Some(CachedResult::NoWitness(_, _)) => {
                // The current contraction was already evaluated and no witness was found.
                is_cached = true;
            }
            None => (),
        }
        let edge_score = in_edge.weight().ttf.link(&out_edge.weight().ttf);
        let no_witness = if !is_cached {
            !self.search_witness(in_edge.source(), out_edge.target(), &edge_score, alloc)
        } else {
            false
        };
        if is_cached || no_witness {
            let middle_node_original_id = self.graph[in_edge.target()].id;
            // No witness was found, we add the shortcut edge.
            let shortcut = ToContractEdge::new_shortcut(
                edge_score,
                in_edge.weight().nb_packed + out_edge.weight().nb_packed,
                middle_node_original_id,
            );
            Some((in_edge.source(), out_edge.target(), shortcut))
        } else {
            // A witness was found.
            None
        }
    }

    /// Returns `true` if a witness indicating that the shortcut is not needed was found.
    fn search_witness(
        &self,
        from: NodeIndex,
        to: NodeIndex,
        edge_score: &TTF<T>,
        alloc: &mut AllocatedDijkstraData<T>,
    ) -> bool {
        alloc.reset();
        // Run a thin profile interval query from the source to the target, excluding the node to
        // be contracted.
        self.run_thin_profile_interval_query(from, to, None, alloc);
        if let Some(interval) = alloc.interval_search.get_label(&to) {
            if interval[1].approx_lt(&edge_score.get_min()) {
                // No shortcut edge is needed.
                return true;
            }
            // The two intervals overlap.
            let corridor = self.get_profile_interval_corridor(to, &mut alloc.interval_search);
            // Sample search.
            if let Some(departure_time) = edge_score.middle_departure_time() {
                self.run_sample_search(from, to, departure_time, &corridor, alloc);
                if let Some(alt_arrival_time) = alloc.sample_search.get_label(&to) {
                    if alt_arrival_time
                        .approx_ge(&(departure_time + edge_score.eval(departure_time)))
                    {
                        // For the first departure time, it is faster to take the edge through the
                        // contracted node so a shortcut is necessary.
                        return false;
                    }
                } else {
                    return false;
                }
            }
            // Profile search.
            self.run_profile_query(from, to, &corridor, alloc);
            if let Some(score) = alloc.profile_search.get_label(&to) {
                // There is a witness only if the score of the profile query is not larger than the
                // edge score.
                if score.get_max().approx_lt(&edge_score.get_min()) {
                    return true;
                }
                let (_merged_ttf, descr) = score.add(T::large_margin()).merge(edge_score);
                !descr.g_undercuts_strictly && descr.f_undercuts_strictly
            } else {
                false
            }
        } else {
            // No path joining the two nodes: the shortcut is needed.
            false
        }
    }

    /// Runs a hop-limited thin profile interval search between `source` and `target`, excluding
    /// the given node.
    fn run_thin_profile_interval_query(
        &self,
        source: NodeIndex,
        target: NodeIndex,
        excluded_node: Option<NodeIndex>,
        alloc: &mut AllocatedDijkstraData<T>,
    ) {
        let remaining_graph =
            NodeFiltered::from_fn(&self.graph, |node_id| Some(node_id) != excluded_node);
        let mut ops = HopLimitedDijkstra::new(
            ThinProfileIntervalDijkstra::new_forward(
                &remaining_graph,
                |edge: EdgeReference<'_, _>| &self.graph[edge.id()].ttf,
            ),
            self.parameters.thin_profile_interval_hop_limit,
        );
        let query = PointToPointQuery::from_default(source, target);
        alloc.interval_search.solve_query(&query, &mut ops);
    }

    /// Returns the corridor resulting from a previous thin profile interval search.
    ///
    /// The corridor is represented by a [FixedBitSet] whose ones represent the indices of the
    /// nodes that are part of the corridor.
    fn get_profile_interval_corridor(
        &self,
        start: NodeIndex,
        search: &mut ThinProfileIntervalDijkstraSearch<T>,
    ) -> FixedBitSet {
        let mut bs = self.graph.visit_map();
        let mut stack = VecDeque::new();
        stack.push_front(start);
        while let Some(node) = stack.pop_front() {
            if bs.visit(node) {
                if let Some(p) = search.get_predecessor(&node) {
                    stack.push_back(p[0]);
                    stack.push_back(p[1]);
                }
            }
        }
        bs
    }

    /// Runs a time-dependent search at a given departure time.
    fn run_sample_search(
        &self,
        source: NodeIndex,
        target: NodeIndex,
        departure_time: T,
        corridor: &FixedBitSet,
        alloc: &mut AllocatedDijkstraData<T>,
    ) {
        let corridor_graph = NodeFiltered(&self.graph, corridor);
        let mut ops = TimeDependentDijkstra::new(&corridor_graph, |edge: EdgeReference<'_, _>| {
            &self.graph[edge.id()].ttf
        });
        let query = PointToPointQuery::new(source, target, departure_time);
        alloc.sample_search.solve_query(&query, &mut ops);
    }

    /// Runs a profile search between `source` and `target`, using only the given corridor.
    fn run_profile_query(
        &self,
        source: NodeIndex,
        target: NodeIndex,
        corridor: &FixedBitSet,
        alloc: &mut AllocatedDijkstraData<T>,
    ) {
        let corridor_graph = NodeFiltered(&self.graph, corridor);
        // We do not use a hop-limit for profile search as the search is already limited by the
        // corridor.
        let mut ops =
            ProfileDijkstra::new_forward(&corridor_graph, |edge: EdgeReference<'_, _>| {
                &self.graph[edge.id()].ttf
            });
        let query = PointToPointQuery::from_default(source, target);
        alloc.profile_search.solve_query(&query, &mut ops);
    }
}

/// Merge a new shortcut edge with an existing (original or shortcut) edge.
fn merge_edges<T: TTFNum>(new_edge: ToContractEdge<T>, old_edge: &mut ToContractEdge<T>) {
    debug_assert!(matches!(
        new_edge.class,
        HierarchyEdgeClass::ShortcutThrough(_)
    ));
    let relative_positioning = old_edge.ttf.analyze_relative_position(&new_edge.ttf);

    if let Either::Left(ord) = relative_positioning {
        if ord == Ordering::Greater {
            // The new edge is always below.
            let old_nb_packed = old_edge.nb_packed;
            *old_edge = new_edge;
            old_edge.nb_packed = old_nb_packed;
        }
        return;
    }

    let relative_positioning = relative_positioning.unwrap_right();

    let new_middle_node = match new_edge.class {
        // The new edge is always a shortcut with a single middle node.
        HierarchyEdgeClass::ShortcutThrough(node) => Packed::IntermediateNode(node),
        _ => unreachable!(),
    };

    let merged_pack = match &old_edge.class {
        &HierarchyEdgeClass::Original(id) => {
            let mut merged_pack = Vec::with_capacity(relative_positioning.len());
            for (t, pos) in relative_positioning {
                match pos {
                    Ordering::Less => {
                        merged_pack.push((t, Packed::OriginalEdge(id)));
                    }
                    Ordering::Greater => {
                        merged_pack.push((t, new_middle_node));
                    }
                    Ordering::Equal => {
                        unreachable!()
                    }
                }
            }
            merged_pack
        }
        &HierarchyEdgeClass::ShortcutThrough(node) => {
            let mut merged_pack = Vec::with_capacity(relative_positioning.len());
            for (t, pos) in relative_positioning {
                match pos {
                    Ordering::Less => {
                        merged_pack.push((t, Packed::IntermediateNode(node)));
                    }
                    Ordering::Greater => {
                        merged_pack.push((t, new_middle_node));
                    }
                    Ordering::Equal => {
                        unreachable!()
                    }
                }
            }
            merged_pack
        }
        HierarchyEdgeClass::PackedShortcut(old_pack) => {
            let mut i = 0;
            let mut j = 0;
            let mut merged_pack =
                Vec::with_capacity(old_pack.len() + 2 * relative_positioning.len());
            while i < relative_positioning.len() && j < old_pack.len() {
                let old_pack_t = if j == 0 && old_pack.len() == 1 {
                    relative_positioning[0].0
                } else {
                    old_pack[j].0
                };
                if relative_positioning[i].0.approx_eq(&old_pack_t) {
                    match relative_positioning[i].1 {
                        Ordering::Less => {
                            merged_pack.push((relative_positioning[i].0, old_pack[j].1));
                        }
                        Ordering::Greater => {
                            merged_pack.push((relative_positioning[i].0, new_middle_node));
                        }
                        Ordering::Equal => {
                            unreachable!()
                        }
                    }
                    i += 1;
                    j += 1;
                } else if relative_positioning[i].0 < old_pack_t {
                    debug_assert!(j >= 1);
                    match relative_positioning[i].1 {
                        Ordering::Less => {
                            merged_pack.push((relative_positioning[i].0, old_pack[j - 1].1));
                        }
                        Ordering::Greater => {
                            merged_pack.push((relative_positioning[i].0, new_middle_node));
                        }
                        Ordering::Equal => {
                            unreachable!()
                        }
                    }
                    i += 1;
                } else {
                    debug_assert!(i >= 1);
                    if relative_positioning[i - 1].1 == Ordering::Less {
                        merged_pack.push(old_pack[j]);
                    }
                    j += 1;
                }
            }
            if j < old_pack.len()
                && relative_positioning[relative_positioning.len() - 1].1 == Ordering::Less
            {
                for &(t, middle_node) in old_pack[j..].iter() {
                    merged_pack.push((t, middle_node));
                }
            }
            if i < relative_positioning.len() {
                for &(t, pos) in relative_positioning[i..].iter() {
                    match pos {
                        Ordering::Less => {
                            merged_pack.push((t, old_pack[old_pack.len() - 1].1));
                        }
                        Ordering::Greater => {
                            merged_pack.push((t, new_middle_node));
                        }
                        Ordering::Equal => {
                            unreachable!()
                        }
                    }
                }
            }
            merged_pack.shrink_to_fit();
            merged_pack
        }
    };

    let (merged_ttf, _) = old_edge.ttf.merge(&new_edge.ttf);

    // NOTE: The number of packed edge is not exact, this is a lower bound (the same thing is done
    // in KaTCH.
    *old_edge = ToContractEdge::new_packed(merged_ttf, old_edge.nb_packed, merged_pack);
}

#[cfg(test)]
mod tests {
    use petgraph::graph::edge_index;

    use super::*;

    #[test]
    fn update_depth_test() {
        // Graph is 0 -- 1 -- 2 -- 3.
        // The initial depths are [0, 1, 2, 4].
        let mut graph = DiGraph::<ToContractNode, ToContractEdge<f64>>::new();
        let n0 = graph.add_node(ToContractNode {
            id: node_index(0),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n1 = graph.add_node(ToContractNode {
            id: node_index(1),
            depth: 1,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n2 = graph.add_node(ToContractNode {
            id: node_index(2),
            depth: 2,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n3 = graph.add_node(ToContractNode {
            id: node_index(3),
            depth: 4,
            order: 0,
            cost: OrderedFloat(0.),
        });
        graph.add_edge(
            n0,
            n1,
            ToContractEdge::new_original(TTF::default(), edge_index(0)),
        );
        graph.add_edge(
            n1,
            n2,
            ToContractEdge::new_original(TTF::default(), edge_index(1)),
        );
        graph.add_edge(
            n2,
            n3,
            ToContractEdge::new_original(TTF::default(), edge_index(2)),
        );
        let mut cg = ContractionGraph::new(graph, Default::default());
        // We update the depths from node 2.
        // New depths should be [0, 3, 2, 4],
        let mut set = HashSet::new();
        set.insert(node_index(2));
        cg.update_depths(&set);
        assert_eq!(cg.graph[node_index(0)].depth, 0);
        assert_eq!(cg.graph[node_index(1)].depth, 3);
        assert_eq!(cg.graph[node_index(2)].depth, 2);
        assert_eq!(cg.graph[node_index(3)].depth, 4);
    }

    #[test]
    fn check_2_hop_neighborhood_test() {
        // Graph is 0 -- 1 -- 2 -- 3.
        // The initial costs are [0., 1., 2., 0.].
        let mut graph = DiGraph::<ToContractNode, ToContractEdge<f64>>::new();
        let n0 = graph.add_node(ToContractNode {
            id: node_index(0),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n1 = graph.add_node(ToContractNode {
            id: node_index(1),
            depth: 0,
            order: 0,
            cost: OrderedFloat(1.),
        });
        let n2 = graph.add_node(ToContractNode {
            id: node_index(2),
            depth: 0,
            order: 0,
            cost: OrderedFloat(2.),
        });
        let n3 = graph.add_node(ToContractNode {
            id: node_index(3),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        graph.add_edge(
            n0,
            n1,
            ToContractEdge::new_original(TTF::default(), edge_index(0)),
        );
        graph.add_edge(
            n1,
            n2,
            ToContractEdge::new_original(TTF::default(), edge_index(1)),
        );
        graph.add_edge(
            n2,
            n3,
            ToContractEdge::new_original(TTF::default(), edge_index(2)),
        );
        let cg = ContractionGraph::new(graph, Default::default());
        // Check that all the 2-hop neighboors of node 0 have a cost > 0 (this is supposed to be
        // true).
        let node = node_index(0);
        let cond = |n: NodeIndex, w: &ToContractNode| n == node || w.cost > OrderedFloat(0.);
        assert!(cg.check_2_hop_neighborhood(node, cond));
        // Check that all the 2-hop neighboors of node 0 have a cost < 2 (this is supposed to be
        // false).
        let cond = |_n: NodeIndex, w: &ToContractNode| w.cost < OrderedFloat(2.);
        assert!(!cg.check_2_hop_neighborhood(node, cond));

        // The condition is always true when there is no neighbor.
        let mut graph = DiGraph::<ToContractNode, ToContractEdge<f64>>::new();
        graph.add_node(ToContractNode {
            id: node_index(0),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let cg = ContractionGraph::new(graph, Default::default());
        assert!(cg.check_2_hop_neighborhood(node_index(0), |_, _| false));
    }

    #[test]
    fn search_witness_test() {
        // Graph is a 0 --> 1 --> 2, with weights [1, 2].
        let mut graph = DiGraph::new();
        let n0 = graph.add_node(ToContractNode {
            id: node_index(0),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n1 = graph.add_node(ToContractNode {
            id: node_index(1),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n2 = graph.add_node(ToContractNode {
            id: node_index(2),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        // Graph weights are integers.
        graph.add_edge(
            n0,
            n1,
            ToContractEdge::new_original(TTF::Constant(1.0f64), edge_index(0)),
        );
        graph.add_edge(
            n1,
            n2,
            ToContractEdge::new_original(TTF::Constant(2.), edge_index(1)),
        );
        let cg = ContractionGraph::new(graph, Default::default());
        // The shortest path n0 -> n2 has weight 1 + 2 = 3 so there is a if and only if the cost of
        // the edge to be contracted is smaller than 3.
        assert!(cg.search_witness(n0, n2, &TTF::Constant(4.), &mut Default::default()));
        // Ties do not count as witnesses.
        assert!(!cg.search_witness(n0, n2, &TTF::Constant(3.), &mut Default::default()));
        assert!(!cg.search_witness(n0, n2, &TTF::Constant(2.), &mut Default::default()));
    }

    #[test]
    fn iter_edge_pairs_test() {
        // Graph is a + sign.
        let mut graph = DiGraph::<ToContractNode, ToContractEdge<f64>>::new();
        let n0 = graph.add_node(ToContractNode {
            id: node_index(0),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n1 = graph.add_node(ToContractNode {
            id: node_index(1),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n2 = graph.add_node(ToContractNode {
            id: node_index(2),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n3 = graph.add_node(ToContractNode {
            id: node_index(3),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        let n4 = graph.add_node(ToContractNode {
            id: node_index(4),
            depth: 0,
            order: 0,
            cost: OrderedFloat(0.),
        });
        graph.add_edge(
            n0,
            n1,
            ToContractEdge::new_original(TTF::default(), edge_index(0)),
        );
        graph.add_edge(
            n1,
            n0,
            ToContractEdge::new_original(TTF::default(), edge_index(1)),
        );
        graph.add_edge(
            n0,
            n2,
            ToContractEdge::new_original(TTF::default(), edge_index(2)),
        );
        graph.add_edge(
            n2,
            n0,
            ToContractEdge::new_original(TTF::default(), edge_index(3)),
        );
        graph.add_edge(
            n0,
            n3,
            ToContractEdge::new_original(TTF::default(), edge_index(4)),
        );
        graph.add_edge(
            n3,
            n0,
            ToContractEdge::new_original(TTF::default(), edge_index(5)),
        );
        graph.add_edge(
            n0,
            n4,
            ToContractEdge::new_original(TTF::default(), edge_index(6)),
        );
        graph.add_edge(
            n4,
            n0,
            ToContractEdge::new_original(TTF::default(), edge_index(7)),
        );
        let cg = ContractionGraph::new(graph, Default::default());
        assert_eq!(cg.iter_remaining_edge_pairs(n0).count(), 12);
        let pairs: HashSet<_> = cg
            .iter_remaining_edge_pairs(n0)
            .map(|(in_edge, out_edge)| (in_edge.source(), out_edge.target()))
            .collect();
        assert!(pairs.contains(&(n1, n2)));
        assert!(pairs.contains(&(n1, n3)));
        assert!(pairs.contains(&(n1, n4)));
        assert!(pairs.contains(&(n2, n1)));
        assert!(pairs.contains(&(n2, n3)));
        assert!(pairs.contains(&(n2, n4)));
        assert!(pairs.contains(&(n3, n1)));
        assert!(pairs.contains(&(n3, n2)));
        assert!(pairs.contains(&(n3, n4)));
        assert!(pairs.contains(&(n4, n1)));
        assert!(pairs.contains(&(n4, n2)));
        assert!(pairs.contains(&(n4, n3)));
    }
}
