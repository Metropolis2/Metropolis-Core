// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Set of algorithm to compute time-dependent shortest paths.
use anyhow::{anyhow, Context, Result};
use either::Either;
use hashbrown::hash_map::HashMap;
use petgraph::graph::NodeIndex;
use petgraph::visit::{EdgeFiltered, EdgeRef, IntoEdgesDirected};
use ttf::{TTFNum, TTF};

use crate::bidirectional_ops::{
    BidirectionalDijkstraOps, BidirectionalProfileDijkstra, BidirectionalTCHEA,
};
use crate::bidirectional_search::BidirectionalDijkstraSearch;
use crate::bound::Bound;
use crate::contraction_hierarchies::{SearchSpace, SearchSpaces};
use crate::min_queue::{MinPQ, MinPriorityQueue};
use crate::node_data::{NodeData, ProfileData, ProfileIntervalData, ScalarData};
use crate::node_map::NodeMap;
use crate::ops::TimeDependentDijkstra;
use crate::query::{BidirectionalQueryRef, MultipleSourcesQuery};
use crate::search::DijkstraSearch;

/// Returns the metric resulting from a profile query.
///
/// Returns `None` if no source and target can be linked.
///
/// # Example
///
/// ```
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
/// use tch::algo::profile_query;
/// use tch::bidirectional_ops::BidirectionalProfileDijkstra;
/// use tch::query::BidirectionalPointToPointQuery;
/// use tch::{BidirectionalDijkstraSearch, DijkstraSearch};
/// use ttf::{PwlTTF, TTF};
///
/// let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let mut search = BidirectionalDijkstraSearch::new(forw_search, back_search);
/// let graph = DiGraph::<(), TTF<f32>>::from_edges(&[
///     (0, 1, TTF::Constant(1.)),
///     (1, 2, TTF::Constant(2.)),
///     (
///         0,
///         2,
///         TTF::Piecewise(PwlTTF::from_values(vec![4., 3., 2., 1., 0.], 0., 2.5)),
///     ),
/// ]);
/// let mut ops = BidirectionalProfileDijkstra::new(
///     &graph,
///     |e: EdgeReference<_>| &graph[e.id()],
///     HashMap::new(),
/// );
/// let query = BidirectionalPointToPointQuery::from_default(node_index(0), node_index(2));
/// let label = profile_query(&mut search, &query, &mut ops);
/// assert_eq!(
///     label,
///     Some(TTF::Piecewise(PwlTTF::from_values(
///         vec![3., 3., 2., 1., 0.],
///         0.,
///         2.5
///     )))
/// );
/// ```
pub fn profile_query<'a, PQ1, PQ2, G1, G2, F1, F2, CM, Q, T>(
    search: &mut BidirectionalDijkstraSearch<ProfileData<T>, ProfileData<T>, PQ1, PQ2>,
    query: Q,
    ops: &mut BidirectionalProfileDijkstra<G1, G2, F1, F2, T, CM>,
) -> Option<TTF<T>>
where
    PQ1: MinPriorityQueue<Key = NodeIndex, Value = T>,
    PQ2: MinPriorityQueue<Key = NodeIndex, Value = T>,
    G1: IntoEdgesDirected<NodeId = NodeIndex>,
    F1: Fn(G1::EdgeRef) -> &'a TTF<T>,
    G2: IntoEdgesDirected<NodeId = NodeIndex>,
    F2: Fn(G2::EdgeRef) -> &'a TTF<T>,
    CM: NodeMap<Node = NodeIndex, Value = T>,
    Q: BidirectionalQueryRef<Node = NodeIndex, Label = TTF<T>, RevLabel = TTF<T>>,
    T: TTFNum + 'a,
{
    search.reset();
    // Run the bidirectional profile search.
    search.solve_query(query, ops);
    let candidates = ops.get_candidates();
    if candidates.is_empty() {
        // No candidate node -> the source and target cannot be linked.
        return None;
    }
    // Store the lower bound of the candidate nodes in a priority queue, in increasing order.
    let mut pq: MinPQ<Either<NodeIndex, usize>, T> =
        MinPQ::with_capacity_and_default_hasher(candidates.len());
    for (node, &lower_bound) in candidates.iter() {
        MinPriorityQueue::push(&mut pq, Either::Left(node), lower_bound);
    }
    let mut i = 0;
    // This HashMap is used to store the merged labels.
    let mut labels = HashMap::with_capacity(candidates.len() - 1);
    while pq.len() >= 2 {
        // Merge the two next labels in the priority queue.
        let label1 = match pq.pop().unwrap().0 {
            Either::Left(n) => get_label_through(search, n),
            Either::Right(i) => labels.remove(&i).unwrap(),
        };
        let label2 = match pq.pop().unwrap().0 {
            Either::Left(n) => get_label_through(search, n),
            Either::Right(i) => labels.remove(&i).unwrap(),
        };
        let merged_label = label1.merge(&label2).0;
        // Push the merged label in the priority queue with key `i`.
        MinPriorityQueue::push(&mut pq, Either::Right(i), merged_label.get_min());
        labels.insert(i, merged_label);
        i += 1;
    }
    // There is only one candidate left in the priority queue, we return it.
    debug_assert_eq!(pq.len(), 1);
    match pq.pop().unwrap().0 {
        Either::Left(n) => Some(get_label_through(search, n)),
        Either::Right(i) => Some(labels.remove(&i).unwrap()),
    }
}

fn get_label_through<PQ1, PQ2, T>(
    search: &mut BidirectionalDijkstraSearch<ProfileData<T>, ProfileData<T>, PQ1, PQ2>,
    node: NodeIndex,
) -> TTF<T>
where
    T: TTFNum,
{
    let flabel = search.get_forward_search().get_data(&node).unwrap().label();
    let blabel = search
        .get_backward_search()
        .get_data(&node)
        .unwrap()
        .label();
    flabel.link(blabel)
}

/// Memory allocation that can be used when computing earliest-arrival queries.
#[derive(Clone, Debug, Default)]
pub struct EarliestArrivalAllocation<FData, BData, DData, PQ1, PQ2, PQ3> {
    /// Allocation for the bidirectional search.
    search: BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2>,
    /// Allocation for the downward search.
    downward_search: DijkstraSearch<DData, PQ3>,
}

impl<FData, BData, DData, PQ1, PQ2, PQ3>
    EarliestArrivalAllocation<FData, BData, DData, PQ1, PQ2, PQ3>
{
    /// Creates a new EarliestArrivalAllocation.
    pub fn new(
        search: BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2>,
        downward_search: DijkstraSearch<DData, PQ3>,
    ) -> Self {
        EarliestArrivalAllocation {
            search,
            downward_search,
        }
    }
}

impl<FData, BData, DData, PQ1, PQ2, PQ3>
    EarliestArrivalAllocation<FData, BData, DData, PQ1, PQ2, PQ3>
where
    PQ1: MinPriorityQueue,
    PQ2: MinPriorityQueue,
    PQ3: MinPriorityQueue,
{
    /// Resets the allocation so that it can be used again.
    pub fn reset(&mut self) {
        self.search.reset();
        self.downward_search.reset();
    }
}

/// Returns the arrival time and path resulting from a bidirectional earliest-arrival query.
///
/// Returns `None` if the source and target cannot be linked.
///
/// This corresponds to Algorithm 4 in Batz et al. (2013)[^ref].
///
/// [^ref]: Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013).
///     Minimum time-dependent travel times with contraction hierarchies.
///     _Journal of Experimental Algorithmics (JEA)_, _18_, 1-1.
///
/// # Example
///
/// ```
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
/// use tch::algo::{earliest_arrival_query, EarliestArrivalAllocation};
/// use tch::bidirectional_ops::BidirectionalTCHEA;
/// use tch::query::BidirectionalPointToPointQuery;
/// use tch::{BidirectionalDijkstraSearch, DijkstraSearch};
/// use ttf::{PwlTTF, TTF};
///
/// let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let search = BidirectionalDijkstraSearch::new(forw_search, back_search);
/// let graph = DiGraph::<(), TTF<f32>>::from_edges(&[
///     (0, 1, TTF::Constant(1.)),
///     (1, 2, TTF::Constant(2.)),
///     (
///         0,
///         2,
///         TTF::Piecewise(PwlTTF::from_values(vec![4., 0.], 0., 10.)),
///     ),
/// ]);
/// let edge_label = |e: EdgeReference<_>| &graph[e.id()];
/// let mut ops = BidirectionalTCHEA::new(&graph, edge_label, HashMap::new());
/// let query = BidirectionalPointToPointQuery::new(node_index(0), node_index(2), 5., [0., 0.]);
/// let down_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let mut alloc = EarliestArrivalAllocation::new(search, down_search);
/// let results = earliest_arrival_query(&mut alloc, &query, &mut ops, &graph, edge_label);
/// assert_eq!(
///     results.unwrap(),
///     Some((7., vec![node_index(0), node_index(2)])),
/// );
/// ```
pub fn earliest_arrival_query<'a, PQ1, PQ2, PQ3, G1, G2, G3, F1, F2, F3, CM, Q, T>(
    alloc: &mut EarliestArrivalAllocation<
        ScalarData<T>,
        ProfileIntervalData<T>,
        ScalarData<T>,
        PQ1,
        PQ2,
        PQ3,
    >,
    query: Q,
    ops: &mut BidirectionalTCHEA<G1, G2, F1, F2, T, T, CM>,
    downward_graph: G3,
    downward_edge_label: F3,
) -> Result<Option<(T, Vec<NodeIndex>)>>
where
    PQ1: MinPriorityQueue<Key = NodeIndex, Value = T>,
    PQ2: MinPriorityQueue<Key = NodeIndex, Value = T>,
    PQ3: MinPriorityQueue<Key = NodeIndex, Value = T>,
    G1: IntoEdgesDirected<NodeId = NodeIndex>,
    F1: Fn(G1::EdgeRef) -> &'a TTF<T>,
    G2: IntoEdgesDirected<NodeId = NodeIndex>,
    F2: Fn(G2::EdgeRef) -> &'a TTF<T>,
    G3: IntoEdgesDirected<NodeId = NodeIndex>,
    F3: Fn(G3::EdgeRef) -> &'a TTF<T>,
    CM: NodeMap<Node = NodeIndex, Value = (T, T)>,
    Q: BidirectionalQueryRef<Node = NodeIndex, Label = T, RevLabel = [T; 2]>,
    T: TTFNum + 'a,
{
    alloc.reset();
    alloc.search.solve_query(query, ops);
    let cone = EdgeFiltered::from_fn(downward_graph, |edge| {
        alloc
            .search
            .get_backward_search()
            .get_predecessor(&edge.source())
            .map(|p| p.contains(&edge.target()))
            .unwrap_or(false)
    });
    let mut downward_ops = TimeDependentDijkstra::new(&cone, downward_edge_label);
    let target = query.target().unwrap();
    let bound = *ops.forward_ops().get_bound();
    let downward_query = get_downward_query(target, bound, ops.get_candidates());
    alloc
        .downward_search
        .solve_query(&downward_query, &mut downward_ops);
    if let Some(&label) = alloc.downward_search.get_label(&target) {
        let path = get_path(
            target,
            alloc.search.get_forward_search(),
            &alloc.downward_search,
        )
        .context("Failed to compute the path")?;
        if cfg!(debug_assertions) {
            // Check that there is no loop in the path.
            let n = path.iter().collect::<hashbrown::HashSet<_>>().len();
            assert_eq!(n, path.len(), "Invalid path: {path:?}");
        }
        Ok(Some((label, path)))
    } else {
        Ok(None)
    }
}

fn get_downward_query<T, CM>(
    target: NodeIndex,
    bound: Bound<T>,
    candidates: &CM,
) -> MultipleSourcesQuery<NodeIndex, T>
where
    CM: NodeMap<Node = NodeIndex, Value = (T, T)>,
    T: Copy + PartialOrd,
{
    let mut sources = Vec::with_capacity(candidates.len());
    let mut labels = Vec::with_capacity(candidates.len());
    for (candidate, &(min_bound, forw_score)) in candidates.iter() {
        if !bound.is_smaller(min_bound) {
            sources.push(candidate);
            labels.push(forw_score);
        }
    }
    MultipleSourcesQuery::with_target(target, sources, labels)
}

fn get_path<PQ1, PQ2, FData, DData>(
    node: NodeIndex,
    forward_search: &DijkstraSearch<FData, PQ1>,
    downward_search: &DijkstraSearch<DData, PQ2>,
) -> Result<Vec<NodeIndex>>
where
    FData: NodeData<Predecessor = NodeIndex>,
    DData: NodeData<Predecessor = NodeIndex>,
{
    let down_path = downward_search
        .get_path(&node)
        .context("Failed to get downward path")?;
    let meet_node = down_path[0];
    let mut path = forward_search
        .get_path(&meet_node)
        .context("Failed to get upward path")?;
    path.extend_from_slice(&down_path[1..]);
    Ok(path)
}

/// Returns the earliest possible arrival time from source to target, when leaving source at the
/// given departure time, using the given forward and backward search spaces.
///
/// Returns an error if either the source or target node is not in the search spaces.
pub fn intersect_earliest_arrival_query<T: TTFNum>(
    source: NodeIndex,
    target: NodeIndex,
    departure_time: T,
    search_spaces: &SearchSpaces<T>,
) -> Result<Option<T>> {
    if source == target {
        return Ok(Some(departure_time));
    }
    if let (Some(source_space), Some(target_space)) = (
        search_spaces.get_forward_search_space(&source),
        search_spaces.get_backward_search_space(&target),
    ) {
        let candidates = find_candidates(source_space, target_space);
        if candidates.is_empty() {
            return Ok(None);
        }
        let mut earliest_arrival = T::infinity();
        for candidate in candidates.iter() {
            let source_ttf = &source_space[candidate];
            let target_ttf = &target_space[candidate];
            use log::debug;
            debug!("Candidate: {}", candidate.index());
            debug!("Source TTF: {:?}", source_ttf);
            debug!("Target TTF: {:?}", target_ttf);
            if (departure_time + source_ttf.get_min() + target_ttf.get_min()) >= earliest_arrival {
                continue;
            }
            let mut new_arrival = departure_time + source_ttf.eval(departure_time);
            new_arrival = new_arrival + target_ttf.eval(new_arrival);
            earliest_arrival = earliest_arrival.min(new_arrival);
        }
        Ok(Some(earliest_arrival))
    } else {
        Err(anyhow!(
            "No search space for node {:?} or {:?}",
            source,
            target
        ))
    }
}

/// Returns the minimum [TTF] between source and target using the given forward and backward search
/// spaces.
///
/// Returns an error if either the source or target node is not in the search spaces.
pub fn intersect_profile_query<T: TTFNum>(
    source: NodeIndex,
    target: NodeIndex,
    search_spaces: &SearchSpaces<T>,
) -> Result<Option<TTF<T>>> {
    if source == target {
        return Ok(Some(Default::default()));
    }
    if let (Some(source_space), Some(target_space)) = (
        search_spaces.get_forward_search_space(&source),
        search_spaces.get_backward_search_space(&target),
    ) {
        let candidates = find_candidates(source_space, target_space);
        if candidates.is_empty() {
            return Ok(None);
        }
        let bounds: Vec<(T, T)> = candidates
            .iter()
            .map(|n| {
                // We know that both `source_space` and `target_space` contain key `n`, otherwise
                // `n` would not be a candidate.
                let source_ttf = &source_space[n];
                let target_ttf = &target_space[n];
                (
                    source_ttf.get_min() + target_ttf.get_min(),
                    source_ttf.get_max() + target_ttf.get_max(),
                )
            })
            .collect();
        // Minimum upper bounds over all the candidates.
        let mut upper_bound = bounds
            .iter()
            .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .map(|(_lb, ub)| *ub)
            .unwrap();
        // Candidate with the minimum lower bound.
        let min_candidate = candidates
            .iter()
            .zip(bounds.iter())
            .min_by(|(_n0, a), (_n1, b)| a.0.partial_cmp(&b.0).unwrap())
            .map(|(n, _b)| n)
            .unwrap();
        let mut min_ttf = source_space[min_candidate].link(&target_space[min_candidate]);
        upper_bound = upper_bound.min(min_ttf.get_max());
        for candidate in candidates.iter().filter(|n| *n != min_candidate) {
            let source_ttf = &source_space[candidate];
            let target_ttf = &target_space[candidate];
            if (source_ttf.get_min() + target_ttf.get_min()) >= upper_bound {
                continue;
            }
            let ttf = source_ttf.link(target_ttf);
            min_ttf = min_ttf.merge(&ttf).0;
            upper_bound = upper_bound.min(min_ttf.get_max());
        }
        Ok(Some(min_ttf))
    } else {
        Err(anyhow!(
            "No search space for node {:?} or {:?}",
            source,
            target
        ))
    }
}

fn find_candidates<T>(forw_space: &SearchSpace<T>, back_space: &SearchSpace<T>) -> Vec<NodeIndex> {
    let (smaller, larger) = if forw_space.len() <= back_space.len() {
        (forw_space, back_space)
    } else {
        (back_space, forw_space)
    };
    smaller
        .keys()
        .filter_map(|n| {
            if larger.contains_key(n) {
                Some(*n)
            } else {
                None
            }
        })
        .collect()
}
