//! Trait and structs used to represent Dijkstra algorithms.

use crate::bound::Bound;
use crate::node_data::{NodeData, NodeDataWithExtra};
use crate::query::Query;

use hashbrown::{HashMap, HashSet};
use petgraph::graph::IndexType;
use petgraph::visit::{EdgeRef, IntoEdgesDirected};
use petgraph::Direction;
use std::hash::Hash;
use ttf::{TTFNum, TTF};

/// Trait representing a set of instructions to perform a Dijkstra's algorithm.
///
/// This trait is usually implemented on structure that hold a reference to the graph and edge's
/// weights used for Dijkstra's algorithm.
pub trait DijkstraOps {
    /// Type of the nodes.
    type Node;
    /// Type of the edges.
    type Edge: Copy;
    /// Type of the nodes' data.
    type Data: NodeData;
    /// Type of the nodes' keys (used in the priority queue).
    type Key;
    /// Iterator used when iterating over the edges of a node.
    type EdgeIterator: Iterator<Item = Self::Edge>;

    /// Link the current label to the label of a successor edge.
    fn link(
        &self,
        data: &<Self::Data as NodeData>::Label,
        edge: Self::Edge,
    ) -> <Self::Data as NodeData>::Label;
    /// Return the current node as predecessor data.
    fn as_new_data(
        &self,
        prev: Option<Self::Node>,
        label: <Self::Data as NodeData>::Label,
    ) -> Self::Data;
    /// Return the node to explore given the currently relaxed edge.
    fn get_next_node(&self, edge: Self::Edge) -> Self::Node;
    /// Return an iterator over the edges to explore from the current node.
    fn edges_from(&self, node: Self::Node) -> Self::EdgeIterator;
    /// Return the key of a label.
    fn get_key(&self, label: &<Self::Data as NodeData>::Label) -> Self::Key;
    /// Given the new label and the existing label for a node, update the existing label and the
    /// predecessor.
    ///
    /// Return the new key of the node in the priority queue (only needed if it is smaller than the
    /// previous key).
    fn relax_existing_label(
        &self,
        prev: Self::Node,
        new_label: <Self::Data as NodeData>::Label,
        node_data: &mut Self::Data,
    ) -> Option<Self::Key>;
    /// Perform operations immediately after a node has been relaxed, given its predecessor, its
    /// label and the query.
    fn node_is_relaxed(
        &mut self,
        _u: Self::Node,
        _v: Self::Node,
        _u_data: &Self::Data,
        _v_data: &mut Self::Data,
        _query: impl Query<Node = Self::Node>,
    ) {
    }
    /// Return `true` if a node can be skipped.
    fn skip_node<D: NodeData<Label = <Self::Data as NodeData>::Label>>(
        &self,
        _node: Self::Node,
        _node_data: &Self::Data,
        _data: &HashMap<Self::Node, D>,
    ) -> bool {
        false
    }
    /// Return `true` if the Dijkstra search can stop just before the given node is being settled,
    /// given its key and the query.
    fn stop(
        &self,
        _node: Self::Node,
        _key: Self::Key,
        _query: impl Query<Node = Self::Node>,
    ) -> bool {
        false
    }
}

/// Instructions for Dijksta's algorithm where the labels coincide with the keys.
///
/// This means that the labels are [Copy] and thus many simplifications can be done.
///
/// With ScalarDijkstra, each node is settled only once.
/// This means that we can stop the search as soon as the next node to settle is one of the targets
/// of the query.
///
/// The search can be run forward or backward.
///
/// The graph should implement [petgraph::visit::IntoEdgesDirected] and should not have
/// negative-weight loops.
///
/// # Example
///
/// ```
/// use dijkstra::DijkstraSearch;
/// use dijkstra::ops::ScalarDijkstra;
/// use dijkstra::query::PointToPointQuery;
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use priority_queue::PriorityQueue;
///
/// // Run a standard point-to-point Dijkstra search with scalars on a graph with three edges.
/// let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let graph = DiGraph::<(), i32>::from_edges(&[(0, 1, 1), (1, 2, 2), (0, 2, 4)]);
/// let mut ops = ScalarDijkstra::new_forward(&graph, |e: EdgeReference<i32>| *e.weight());
/// let query = PointToPointQuery::from_default(node_index(0), node_index(2));
/// search.solve_query(&query, &mut ops).unwrap();
/// assert_eq!(search.get_label(&node_index(2)), Some(&3));
/// assert_eq!(
///     search.get_path(&node_index(2)).unwrap(),
///     vec![node_index(0), node_index(1), node_index(2)]
/// );
/// ```
pub struct ScalarDijkstra<G, F> {
    /// Graph used by the algorithm.
    graph: G,
    /// Direction of the search (Forward, using outgoing edges, or Backward, using incoming edges).
    direction: Direction,
    /// Function used to retrieve edge's labels.
    edge_label: F,
}

impl<G, F> ScalarDijkstra<G, F> {
    /// Initialize a new ScalaDijkstra instance, with the given direction.
    fn new(graph: G, edge_label: F, direction: Direction) -> Self {
        ScalarDijkstra {
            graph,
            edge_label,
            direction,
        }
    }

    /// Initialize a new ScalarDijkstra instance for a forward search.
    pub fn new_forward(graph: G, edge_label: F) -> Self {
        ScalarDijkstra::new(graph, edge_label, Direction::Outgoing)
    }

    /// Initialize a new ScalarDijkstra instance for a backward search.
    pub fn new_backward(graph: G, edge_label: F) -> Self {
        ScalarDijkstra::new(graph, edge_label, Direction::Incoming)
    }
}

impl<G, F, T> DijkstraOps for ScalarDijkstra<G, F>
where
    G: IntoEdgesDirected,
    T: TTFNum,
    F: Fn(G::EdgeRef) -> T,
{
    type Node = G::NodeId;
    type Edge = G::EdgeRef;
    type Data = (T, Option<G::NodeId>);
    type Key = T;
    type EdgeIterator = G::EdgesDirected;

    fn link(&self, label: &T, edge: G::EdgeRef) -> T {
        let edge_label = (self.edge_label)(edge);
        *label + edge_label
    }
    fn as_new_data(&self, prev: Option<G::NodeId>, label: T) -> (T, Option<G::NodeId>) {
        (label, prev)
    }
    fn get_next_node(&self, edge: G::EdgeRef) -> G::NodeId {
        match self.direction {
            Direction::Outgoing => edge.target(),
            Direction::Incoming => edge.source(),
        }
    }
    fn edges_from(&self, node: G::NodeId) -> G::EdgesDirected {
        self.graph.edges_directed(node, self.direction)
    }
    fn get_key(&self, label: &T) -> T {
        *label
    }
    fn relax_existing_label(
        &self,
        prev: G::NodeId,
        node_label: T,
        node_data: &mut (T, Option<G::NodeId>),
    ) -> Option<T> {
        if node_label < node_data.0 {
            node_data.0 = node_label;
            node_data.1 = Some(prev);
            return Some(node_label);
        }
        None
    }
    fn stop(&self, node: G::NodeId, _key: T, query: impl Query<Node = G::NodeId>) -> bool {
        // Stop if the next node to settle is one of the query's target.
        query.target() == Some(node)
    }
}

/// Instructions for Dijksta's algorithm where the labels represent time-dependent travel-time
/// functions and where the departure time is given.
///
/// This struct can be used for "earliest-arrival query", i.e., what is the earliest possible
/// arrival time given a departure time and time-dependent edges' weights.
///
/// With TimeDependentDijkstra, each node is settled only once.
/// This means that we can stop the search as soon as the next node to settle is one of the targets
/// of the query.
///
/// The search can be run forward only, i.e., starting from a departure time.
///
/// The search can be run bounded, i.e., the search stops as soon as the arrival time at the next
/// node to be settled exceed the bound.
///
/// The graph should implement [petgraph::visit::IntoEdgesDirected] and its edges' weights should
/// satisfy FIFO (first-in, first-out) to avoid negative-weight loops.
///
/// # Example
///
/// ```
/// use breakpoint_function::PWLFunction;
/// use dijkstra::ops::TimeDependentDijkstra;
/// use dijkstra::query::PointToPointQuery;
/// use dijkstra::DijkstraSearch;
/// use hashbrown::HashMap;
/// use ordered_float::OrderedFloat;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
///
/// let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let graph = DiGraph::<(), PWLFunction<_>>::from_edges(&[
///     (
///         0,
///         1,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(1.)),
///             (OrderedFloat(10.), OrderedFloat(1.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         1,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(2.)),
///             (OrderedFloat(10.), OrderedFloat(2.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         0,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(4.)),
///             (OrderedFloat(10.), OrderedFloat(0.)),
///         ])
///         .unwrap(),
///     ),
/// ]);
/// let mut ops = TimeDependentDijkstra::new(&graph, |e: EdgeReference<_>| &graph[e.id()]);
///
/// // When leaving at 0.0, its better to take path 0 -> 1 -> 2 (travel time is 3.0).
/// let query = PointToPointQuery::new(node_index(0), node_index(2), OrderedFloat(0.));
/// search.solve_query(&query, &mut ops).unwrap();
/// assert_eq!(
///     search.get_label(&node_index(2)),
///     Some(&OrderedFloat(3.))
/// );
/// assert_eq!(
///     search.get_path(&node_index(2)).unwrap(),
///     vec![node_index(0), node_index(1), node_index(2)]
/// );
///
/// // When leaving at 5.0, its better to take path 0 -> 2 (travel time is 2.0, arrival time is 5.0).
/// let query = PointToPointQuery::new(node_index(0), node_index(2), OrderedFloat(5.));
/// search.solve_query(&query, &mut ops).unwrap();
/// assert_eq!(
///     search.get_label(&node_index(2)),
///     Some(&OrderedFloat(5. + 2.))
/// );
/// assert_eq!(
///     search.get_path(&node_index(2)).unwrap(),
///     vec![node_index(0), node_index(2)]
/// );
/// ```
pub struct TimeDependentDijkstra<G, F, T> {
    graph: G,
    edge_label: F,
    bound: Bound<T>,
}

impl<G, F, T> TimeDependentDijkstra<G, F, T> {
    /// Initialize a new TimeDependentDijkstra instance, with a graph and edge weights.
    pub fn new(graph: G, edge_label: F) -> Self {
        TimeDependentDijkstra {
            graph,
            edge_label,
            bound: Bound::new(),
        }
    }

    /// Initialize a new TimeDependentDijkstra instance, with a graph, edge weights and a bound.
    pub fn new_with_bound(graph: G, edge_label: F, bound: T) -> Self {
        TimeDependentDijkstra {
            graph,
            edge_label,
            bound: Bound::from_value(bound),
        }
    }

    /// Return the current bound of the TimeDependentDijkstra.
    pub fn get_bound(&self) -> &Bound<T> {
        &self.bound
    }
}

impl<G, F, T: Copy + PartialOrd> TimeDependentDijkstra<G, F, T> {
    /// Update the current bound of the TimeDependentDijkstra.
    pub fn update_bound(&mut self, value: T) {
        self.bound.update(value);
    }
}

impl<'a, G, F, T> TimeDependentDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
    T: 'a,
{
    pub fn get_ttf(&self, edge: G::EdgeRef) -> &'a TTF<T> {
        (self.edge_label)(edge)
    }
}

impl<'a, G, F, T> DijkstraOps for TimeDependentDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    T: TTFNum + 'a,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
{
    type Node = G::NodeId;
    type Edge = G::EdgeRef;
    type Data = (T, Option<G::NodeId>);
    type Key = T;
    type EdgeIterator = G::EdgesDirected;

    fn link(&self, &arrival_time: &T, edge: G::EdgeRef) -> T {
        let ttf = (self.edge_label)(edge);
        arrival_time + ttf.eval(arrival_time)
    }
    fn as_new_data(&self, prev: Option<G::NodeId>, label: T) -> (T, Option<G::NodeId>) {
        (label, prev)
    }
    fn get_next_node(&self, edge: G::EdgeRef) -> G::NodeId {
        edge.target()
    }
    fn edges_from(&self, node: G::NodeId) -> G::EdgesDirected {
        self.graph.edges_directed(node, Direction::Outgoing)
    }
    fn get_key(&self, label: &T) -> T {
        *label
    }
    fn relax_existing_label(
        &self,
        prev: G::NodeId,
        node_label: T,
        node_data: &mut (T, Option<G::NodeId>),
    ) -> Option<T> {
        if node_label < node_data.0 {
            node_data.0 = node_label;
            node_data.1 = Some(prev);
            return Some(node_label);
        }
        None
    }
    fn stop(&self, node: G::NodeId, key: T, query: impl Query<Node = G::NodeId>) -> bool {
        // Stop if the next node to settle is one of the query's target or if the bound is exceeded.
        query.target() == Some(node) || self.bound.is_smaller(key)
    }
}

/// Instructions for Dijksta's algorithm where the labels represent time-dependent travel-time
/// functions and where we want to compute the fastest travel time between two nodes, for all
/// possible departure times.
///
/// This struct can be used for what is usually called "profile queries".
///
/// Nodes can be settled multiple times because they are re-inserted in the priority queue when an
/// improvement to their label was found.
/// The search stops when we know that the maximum travel time of the target with the min-max
/// travel time cannot be improved.
///
/// The search can be run forward or backward.
///
/// The search can be run bounded, i.e., the search stops as soon as all nodes whose minimum travel
/// time is below the bound have been settled.
///
/// The graph should implement [petgraph::visit::IntoEdgesDirected] and its edges' weights should
/// satisfy FIFO (first-in, first-out) to avoid negative-weight loops.
///
/// # Example
///
/// ```
/// use breakpoint_function::PWLFunction;
/// use dijkstra::ops::ProfileDijkstra;
/// use dijkstra::query::PointToPointQuery;
/// use dijkstra::DijkstraSearch;
/// use hashbrown::HashMap;
/// use ordered_float::OrderedFloat;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
///
/// let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
/// let graph = DiGraph::<(), PWLFunction<_>>::from_edges(&[
///     (
///         0,
///         1,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(1.)),
///             (OrderedFloat(10.), OrderedFloat(1.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         1,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(2.)),
///             (OrderedFloat(10.), OrderedFloat(2.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         0,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(4.)),
///             (OrderedFloat(10.), OrderedFloat(0.)),
///         ])
///         .unwrap(),
///     ),
/// ]);
/// let mut ops = ProfileDijkstra::new_forward(&graph, |e: EdgeReference<_>| &graph[e.id()]);
///
/// let query = PointToPointQuery::from_default(node_index(0), node_index(2));
/// search.solve_query(&query, &mut ops).unwrap();
///
/// let ttf = PWLFunction::from_breakpoints(vec![
///     (OrderedFloat(0.), OrderedFloat(3.)),
///     (OrderedFloat(2.5), OrderedFloat(3.)),
///     (OrderedFloat(10.), OrderedFloat(0.)),
/// ])
/// .unwrap();
/// assert_eq!(
///     search.get_label(&node_index(2)),
///     Some(&ttf)
/// );
/// ```
pub struct ProfileDijkstra<G, F, T> {
    graph: G,
    direction: Direction,
    edge_label: F,
    bound: Bound<T>,
}

impl<G, F, T> ProfileDijkstra<G, F, T> {
    /// Initialize a new ProfileDijkstra instance of a given direction.
    fn new(graph: G, edge_label: F, direction: Direction) -> Self {
        ProfileDijkstra {
            graph,
            edge_label,
            direction,
            bound: Bound::new(),
        }
    }

    /// Initialize a new ProfileDijkstra instance for a forward search.
    pub fn new_forward(graph: G, edge_label: F) -> Self {
        ProfileDijkstra::new(graph, edge_label, Direction::Outgoing)
    }

    /// Initialize a new ProfileDijkstra instance for a backward search.
    pub fn new_backward(graph: G, edge_label: F) -> Self {
        ProfileDijkstra::new(graph, edge_label, Direction::Incoming)
    }

    /// Initialize a new ProfileDijkstra instance of a given direction with a bound.
    fn new_with_bound(graph: G, edge_label: F, direction: Direction, bound: T) -> Self {
        ProfileDijkstra {
            graph,
            edge_label,
            direction,
            bound: Bound::from_value(bound),
        }
    }

    /// Initialize a new ProfileDijkstra instance for a forward search with a bound.
    pub fn new_forward_with_bound(graph: G, edge_label: F, bound: T) -> Self {
        ProfileDijkstra::new_with_bound(graph, edge_label, Direction::Outgoing, bound)
    }

    /// Initialize a new ProfileDijkstra instance for a backward search with a bound.
    pub fn new_backward_with_bound(graph: G, edge_label: F, bound: T) -> Self {
        ProfileDijkstra::new_with_bound(graph, edge_label, Direction::Incoming, bound)
    }

    /// Return the current bound of the ProfileDijkstra.
    pub fn get_bound(&self) -> &Bound<T> {
        &self.bound
    }
}

impl<G, F, T: Copy + PartialOrd> ProfileDijkstra<G, F, T> {
    /// Update the current bound of the ProfileDijkstra.
    pub fn update_bound(&mut self, value: T) {
        self.bound.update(value);
    }
}

impl<'a, G, F, T> ProfileDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
    T: 'a,
{
    pub fn get_ttf(&self, edge: G::EdgeRef) -> &'a TTF<T> {
        (self.edge_label)(edge)
    }
}

impl<'a, G, F, T> DijkstraOps for ProfileDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    G::NodeId: Eq + Hash,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
{
    type Node = G::NodeId;
    type Edge = G::EdgeRef;
    type Data = (TTF<T>, Option<HashSet<G::NodeId>>);
    type Key = T;
    type EdgeIterator = G::EdgesDirected;

    fn link(&self, current_ttf: &TTF<T>, edge: G::EdgeRef) -> TTF<T> {
        let edge_ttf = (self.edge_label)(edge);
        match self.direction {
            Direction::Outgoing => current_ttf.link(edge_ttf),
            Direction::Incoming => edge_ttf.link(current_ttf),
        }
    }
    fn as_new_data(
        &self,
        prev: Option<G::NodeId>,
        label: TTF<T>,
    ) -> (TTF<T>, Option<HashSet<G::NodeId>>) {
        let mut hs = HashSet::new();
        if let Some(p) = prev {
            hs.insert(p);
        }
        (label, Some(hs))
    }
    fn get_next_node(&self, edge: G::EdgeRef) -> G::NodeId {
        match self.direction {
            Direction::Outgoing => edge.target(),
            Direction::Incoming => edge.source(),
        }
    }
    fn edges_from(&self, node: G::NodeId) -> G::EdgesDirected {
        self.graph.edges_directed(node, self.direction)
    }
    fn get_key(&self, ttf: &TTF<T>) -> T {
        ttf.get_min()
    }
    fn relax_existing_label(
        &self,
        prev: G::NodeId,
        node_label: TTF<T>,
        node_data: &mut (TTF<T>, Option<HashSet<G::NodeId>>),
    ) -> Option<T> {
        let (merged_label, descr) = node_label.merge(&node_data.0);
        if descr.f_undercuts_strictly {
            // The label of the relaxed node was used to compute the new label.
            node_data.0 = merged_label;
            if let Some(p) = node_data.predecessor_mut() {
                if !descr.g_undercuts_strictly {
                    // The label of the relaxed edge dominates the old label.
                    p.clear();
                }
                p.insert(prev);
            }
            // The existing label was improved so we return its lower bound so that the key get
            // decreased or the node is re-inserted in the priority queue.
            Some(node_data.0.get_min())
        } else {
            None
        }
    }
    fn stop(&self, _node: G::NodeId, key: T, _query: impl Query<Node = G::NodeId>) -> bool {
        // Stop if the next key (i.e., the lower bound of the next TTF) is larger than the bound
        // (i.e., the minimum upper bound over the TTF of all targets).
        self.bound.is_smaller(key)
    }
    fn node_is_relaxed(
        &mut self,
        _u: G::NodeId,
        v: G::NodeId,
        _u_data: &(TTF<T>, Option<HashSet<G::NodeId>>),
        v_data: &mut (TTF<T>, Option<HashSet<G::NodeId>>),
        query: impl Query<Node = Self::Node>,
    ) {
        if query.target() == Some(v) {
            self.bound.update(v_data.0.get_max());
        }
    }
}

/// Instructions for Dijksta's algorithm where the labels represent time-dependent travel-time
/// functions and where we want to compute a lower bound and upper bound of the travel-time profile
/// between any two nodes.
///
/// This corresponds to Algorithm 3 in Batz et al. (2013)[^ref].
///
/// [^ref]: Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013).
///     Minimum time-dependent travel times with contraction hierarchies.
///     _Journal of Experimental Algorithmics (JEA)_, _18_, 1-1.
///
/// Nodes can be settled multiple times because they are re-inserted in the priority queue when an
/// improvement to their upper bound was found.
/// The search stops when we know that the upper bound of the target with the min-max upper bound
/// cannot be improved.
///
/// The search can be run forward or backward.
///
/// The search can be run bounded, i.e., the search stops as soon as all nodes whose lower bound
/// travel time is below the bound have been settled.
///
/// The predecessors of a node is a [HashSet] that is guaranteed to contain all nodes that could be
/// part of an earliest-arrival path from a source to the node.
///
/// The graph should implement [petgraph::visit::IntoEdgesDirected] and its edges' weights should
/// be positive to avoid negative-weight loops.
///
/// # Example
///
/// ```
/// use breakpoint_function::PWLFunction;
/// use tch::ops::ProfileIntervalDijkstra;
/// use dijkstra::query::PointToPointQuery;
/// use dijkstra::DijkstraSearch;
/// use hashbrown::HashMap;
/// use ordered_float::OrderedFloat;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
///
/// let mut search = DijkstraSearch::new(HashMap::new(), HashMap::new(), PriorityQueue::new());
/// let graph = DiGraph::<(), PWLFunction<_>>::from_edges(&[
///     (
///         0,
///         1,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(1.)),
///             (OrderedFloat(10.), OrderedFloat(1.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         1,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(2.)),
///             (OrderedFloat(10.), OrderedFloat(2.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         0,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(4.)),
///             (OrderedFloat(10.), OrderedFloat(0.)),
///         ])
///         .unwrap(),
///     ),
/// ]);
/// let mut ops = ProfileIntervalDijkstra::new_forward(&graph, |e: EdgeReference<_>| &graph[e.id()]);
///
/// let zero = OrderedFloat(0.);
/// let query = PointToPointQuery::new(node_index(0), node_index(2), [zero, zero]);
/// search.solve_query(&query, &mut ops).unwrap();
///
/// assert_eq!(
///     search.get_label(&node_index(2)),
///     Some(&[OrderedFloat(0.), OrderedFloat(3.)])
/// );
/// let p = search.get_predecessor(&node_index(2)).unwrap();
/// assert!(p.contains(&node_index(0)));
/// assert!(p.contains(&node_index(1)));
/// ```
pub struct ProfileIntervalDijkstra<G, F, T> {
    graph: G,
    edge_label: F,
    direction: Direction,
    bound: Bound<T>,
    stalling: bool,
}

impl<G, F, T> ProfileIntervalDijkstra<G, F, T> {
    /// Initialize a new ProfileIntervalDijkstra instance of a given direction.
    fn new(graph: G, edge_label: F, direction: Direction, stalling: bool) -> Self {
        ProfileIntervalDijkstra {
            graph,
            edge_label,
            direction,
            bound: Bound::new(),
            stalling,
        }
    }

    /// Initialize a new ProfileIntervalDijkstra instance for a forward search.
    pub fn new_forward(graph: G, edge_label: F) -> Self {
        ProfileIntervalDijkstra::new(graph, edge_label, Direction::Outgoing, false)
    }

    /// Initialize a new ProfileIntervalDijkstra instance for a backward search.
    pub fn new_backward(graph: G, edge_label: F) -> Self {
        ProfileIntervalDijkstra::new(graph, edge_label, Direction::Incoming, false)
    }

    /// Initialize a new ProfileIntervalDijkstra instance of a given direction with a bound.
    fn new_with_bound(
        graph: G,
        edge_label: F,
        direction: Direction,
        bound: T,
        stalling: bool,
    ) -> Self {
        ProfileIntervalDijkstra {
            graph,
            edge_label,
            direction,
            bound: Bound::from_value(bound),
            stalling,
        }
    }

    /// Initialize a new ProfileIntervalDijkstra instance for a forward search with a bound.
    pub fn new_forward_with_bound(graph: G, edge_label: F, bound: T) -> Self {
        ProfileIntervalDijkstra::new_with_bound(
            graph,
            edge_label,
            Direction::Outgoing,
            bound,
            false,
        )
    }

    /// Initialize a new ProfileIntervalDijkstra instance for a backward search with a bound.
    pub fn new_backward_with_bound(graph: G, edge_label: F, bound: T) -> Self {
        ProfileIntervalDijkstra::new_with_bound(
            graph,
            edge_label,
            Direction::Incoming,
            bound,
            false,
        )
    }

    /// Initialize a new ProfileIntervalDijkstra instance for a forward search with stall-on-demand.
    pub fn new_forward_with_stall_on_demand(graph: G, edge_label: F) -> Self {
        ProfileIntervalDijkstra::new(graph, edge_label, Direction::Outgoing, true)
    }

    /// Initialize a new ProfileIntervalDijkstra instance for a backward search with
    /// stall-on-demand.
    pub fn new_backward_with_stall_on_demand(graph: G, edge_label: F) -> Self {
        ProfileIntervalDijkstra::new(graph, edge_label, Direction::Incoming, true)
    }

    /// Return a reference to the current bound of the ops.
    pub fn get_bound(&self) -> &Bound<T> {
        &self.bound
    }
}

impl<G, F, T: Copy + PartialOrd> ProfileIntervalDijkstra<G, F, T> {
    pub fn update_bound(&mut self, value: T) {
        self.bound.update(value);
    }
}

impl<'a, G, F, T> ProfileIntervalDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
    G::NodeId: Eq + Hash,
{
    fn can_be_stalled<D: NodeData<Label = [T; 2]>>(
        &self,
        node: G::NodeId,
        node_data: &([T; 2], Option<HashSet<G::NodeId>>),
        data: &HashMap<G::NodeId, D>,
    ) -> bool {
        for edge in self.graph.edges_directed(node, self.direction.opposite()) {
            let other_node = match self.direction {
                Direction::Outgoing => edge.source(),
                Direction::Incoming => edge.target(),
            };
            if let Some(prev_data) = data.get(&other_node) {
                let upper_bound = prev_data.label()[1] + (self.edge_label)(edge).get_max();
                if upper_bound.approx_lt(&node_data.label()[0]) {
                    // The node can be stalled because the arrival time at the current node
                    // can be improved by going through the current edge.
                    return true;
                }
            }
        }
        false
    }
}

impl<'a, G, F, T> ProfileIntervalDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
    T: 'a,
{
    pub fn get_ttf(&self, edge: G::EdgeRef) -> &'a TTF<T> {
        (self.edge_label)(edge)
    }
}

impl<'a, G, F, T> DijkstraOps for ProfileIntervalDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    G::NodeId: Eq + Hash,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
{
    type Node = G::NodeId;
    type Edge = G::EdgeRef;
    type Data = ([T; 2], Option<HashSet<G::NodeId>>);
    type Key = T;
    type EdgeIterator = G::EdgesDirected;

    fn link(&self, label: &[T; 2], edge: G::EdgeRef) -> [T; 2] {
        let edge_label = (self.edge_label)(edge);
        [
            label[0] + edge_label.get_min(),
            label[1] + edge_label.get_max(),
        ]
    }
    fn as_new_data(
        &self,
        prev: Option<G::NodeId>,
        label: [T; 2],
    ) -> ([T; 2], Option<HashSet<G::NodeId>>) {
        let mut hs = HashSet::new();
        if let Some(p) = prev {
            hs.insert(p);
        }
        (label, Some(hs))
    }
    fn get_next_node(&self, edge: G::EdgeRef) -> G::NodeId {
        match self.direction {
            Direction::Outgoing => edge.target(),
            Direction::Incoming => edge.source(),
        }
    }
    fn edges_from(&self, node: G::NodeId) -> G::EdgesDirected {
        self.graph.edges_directed(node, self.direction)
    }
    fn get_key(&self, label: &[T; 2]) -> T {
        label[0]
    }
    fn relax_existing_label(
        &self,
        prev: G::NodeId,
        new_label: [T; 2],
        (node_label, node_pred): &mut ([T; 2], Option<HashSet<G::NodeId>>),
    ) -> Option<T> {
        if new_label[1] < node_label[0] {
            // The new label dominates the existing one.
            *node_label = new_label;
            if let Some(p) = node_pred {
                let mut hs = HashSet::new();
                hs.insert(prev);
                *p = hs;
            }
            return Some(new_label[0]);
        }
        if node_label[1] < new_label[0] {
            // The existing label dominates the new one.
            return None;
        }
        if let Some(p) = node_pred {
            p.insert(prev);
        }
        let mut has_improved = false;
        if new_label[1] < node_label[1] {
            node_label[1] = new_label[1];
            has_improved = true;
        }
        if new_label[0] < node_label[0] {
            node_label[0] = new_label[0];
            has_improved = true;
        }
        // We only return the lower bound the label has changed.
        if has_improved {
            Some(node_label[0])
        } else {
            None
        }
    }
    fn stop(&self, _node: G::NodeId, key: T, _query: impl Query<Node = G::NodeId>) -> bool {
        // Stop if the next key (i.e., the lower bound of the next TTF) is larger than the bound
        // (i.e., the minimum upper bound over the TTF of all targets).
        self.bound.is_smaller(key)
    }
    fn node_is_relaxed(
        &mut self,
        _u: G::NodeId,
        v: G::NodeId,
        _u_data: &([T; 2], Option<HashSet<G::NodeId>>),
        v_data: &mut ([T; 2], Option<HashSet<G::NodeId>>),
        query: impl Query<Node = G::NodeId>,
    ) {
        // If the relaxed node is one of the target, set the bound to the upper bound of its label.
        if query.target() == Some(v) {
            self.bound.update(v_data.0[1]);
        }
    }
    fn skip_node<D: NodeData<Label = [T; 2]>>(
        &self,
        node: G::NodeId,
        node_data: &Self::Data,
        data: &HashMap<G::NodeId, D>,
    ) -> bool {
        self.stalling && self.can_be_stalled(node, node_data, data)
    }
}

/// Variant of [ProfileIntervalDijkstra] where we store only two predecessors for each node.
///
/// The first predecessor is the last node that improved the lower bound, the second predecessor is
/// the last node that improved the upper bound.
///
/// This corresponds to the algorithm described in the paragraph _Thinning out the Corridor
/// Heuristically_ of Batz et al. (2013)[^ref].
///
/// [^ref]: Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013).
///     Minimum time-dependent travel times with contraction hierarchies.
///     _Journal of Experimental Algorithmics (JEA)_, _18_, 1-1.
///
/// # Example
///
/// ```
/// use breakpoint_function::PWLFunction;
/// use tch::ops::ThinProfileIntervalDijkstra;
/// use dijkstra::query::PointToPointQuery;
/// use dijkstra::DijkstraSearch;
/// use hashbrown::HashMap;
/// use ordered_float::OrderedFloat;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use petgraph::visit::EdgeRef;
/// use priority_queue::PriorityQueue;
///
/// let mut search = DijkstraSearch::new(HashMap::new(), HashMap::new(), PriorityQueue::new());
/// let graph = DiGraph::<(), PWLFunction<_>>::from_edges(&[
///     (
///         0,
///         1,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(1.)),
///             (OrderedFloat(10.), OrderedFloat(1.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         1,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(2.)),
///             (OrderedFloat(10.), OrderedFloat(2.)),
///         ])
///         .unwrap(),
///     ),
///     (
///         0,
///         2,
///         PWLFunction::from_breakpoints(vec![
///             (OrderedFloat(0.), OrderedFloat(4.)),
///             (OrderedFloat(10.), OrderedFloat(0.)),
///         ])
///         .unwrap(),
///     ),
/// ]);
/// let mut ops = ThinProfileIntervalDijkstra::new_forward(
///     &graph, |e: EdgeReference<_>| &graph[e.id()]
/// );
///
/// let zero = OrderedFloat(0.);
/// let query = PointToPointQuery::new(node_index(0), node_index(2), [zero, zero]);
/// search.solve_query(&query, &mut ops).unwrap();
///
/// assert_eq!(
///     search.get_label(&node_index(2)),
///     Some(&[OrderedFloat(0.), OrderedFloat(3.)])
/// );
/// assert_eq!(
///     search.get_predecessor(&node_index(2)),
///     Some(&[node_index(0), node_index(1)])
/// );
/// ```
pub struct ThinProfileIntervalDijkstra<G, F, T> {
    graph: G,
    edge_label: F,
    direction: Direction,
    bound: Bound<T>,
}

impl<G, F, T> ThinProfileIntervalDijkstra<G, F, T> {
    /// Initialize a new ThinProfileIntervalDijkstra instance of a given direction.
    fn new(graph: G, edge_label: F, direction: Direction) -> Self {
        ThinProfileIntervalDijkstra {
            graph,
            edge_label,
            direction,
            bound: Bound::new(),
        }
    }

    /// Initialize a new ThinProfileIntervalDijkstra instance for a forward search.
    pub fn new_forward(graph: G, edge_label: F) -> Self {
        ThinProfileIntervalDijkstra::new(graph, edge_label, Direction::Outgoing)
    }

    /// Initialize a new ThinProfileIntervalDijkstra instance for a backward search.
    pub fn new_backward(graph: G, edge_label: F) -> Self {
        ThinProfileIntervalDijkstra::new(graph, edge_label, Direction::Incoming)
    }

    /// Initialize a new ThinProfileIntervalDijkstra instance of a given direction with a bound.
    fn new_with_bound(graph: G, edge_label: F, direction: Direction, bound: T) -> Self {
        ThinProfileIntervalDijkstra {
            graph,
            edge_label,
            direction,
            bound: Bound::from_value(bound),
        }
    }

    /// Initialize a new ThinProfileIntervalDijkstra instance for a forward search with a bound.
    pub fn new_forward_with_bound(graph: G, edge_label: F, bound: T) -> Self {
        ThinProfileIntervalDijkstra::new_with_bound(graph, edge_label, Direction::Outgoing, bound)
    }

    /// Initialize a new ThinProfileIntervalDijkstra instance for a backward search with a bound.
    pub fn new_backward_with_bound(graph: G, edge_label: F, bound: T) -> Self {
        ThinProfileIntervalDijkstra::new_with_bound(graph, edge_label, Direction::Incoming, bound)
    }

    /// Return a reference to the current bound of the ops.
    pub fn get_bound(&self) -> &Bound<T> {
        &self.bound
    }
}

impl<'a, G, F, T> DijkstraOps for ThinProfileIntervalDijkstra<G, F, T>
where
    G: IntoEdgesDirected,
    G::NodeId: Eq + Hash,
    F: Fn(G::EdgeRef) -> &'a TTF<T>,
    T: TTFNum + 'a,
{
    type Node = G::NodeId;
    type Edge = G::EdgeRef;
    type Data = ([T; 2], Option<[G::NodeId; 2]>);
    type Key = T;
    type EdgeIterator = G::EdgesDirected;

    fn link(&self, label: &[T; 2], edge: G::EdgeRef) -> [T; 2] {
        let edge_label = (self.edge_label)(edge);
        [
            label[0] + edge_label.get_min(),
            label[1] + edge_label.get_max(),
        ]
    }
    fn as_new_data(
        &self,
        prev: Option<G::NodeId>,
        label: [T; 2],
    ) -> ([T; 2], Option<[G::NodeId; 2]>) {
        (label, prev.map(|p| [p, p]))
    }
    fn get_next_node(&self, edge: G::EdgeRef) -> G::NodeId {
        match self.direction {
            Direction::Outgoing => edge.target(),
            Direction::Incoming => edge.source(),
        }
    }
    fn edges_from(&self, node: G::NodeId) -> G::EdgesDirected {
        self.graph.edges_directed(node, self.direction)
    }
    fn get_key(&self, label: &[T; 2]) -> T {
        label[0]
    }
    fn relax_existing_label(
        &self,
        prev: G::NodeId,
        new_label: [T; 2],
        node_data: &mut ([T; 2], Option<[G::NodeId; 2]>),
    ) -> Option<T> {
        let mut has_improved = false;
        if new_label[1] < node_data.0[1] {
            // The upper bound is improved.
            node_data.0[1] = new_label[1];
            if let Some([_, ref mut p]) = node_data.1 {
                *p = prev;
            }
            has_improved = true;
        }
        if new_label[0] < node_data.0[0] {
            // The lower bound is improved.
            node_data.0[0] = new_label[0];
            if let Some([ref mut p, _]) = node_data.1 {
                *p = prev;
            }
            has_improved = true;
        }
        // We only return the lower bound the label has changed.
        if has_improved {
            Some(node_data.0[0])
        } else {
            None
        }
    }
    fn stop(&self, _node: G::NodeId, key: T, _query: impl Query<Node = G::NodeId>) -> bool {
        // Stop if the next key (i.e., the lower bound of the next TTF) is larger than the bound
        // (i.e., the minimum upper bound over the TTF of all targets).
        self.bound.is_smaller(key)
    }
    fn node_is_relaxed(
        &mut self,
        _u: G::NodeId,
        v: G::NodeId,
        _u_data: &([T; 2], Option<[G::NodeId; 2]>),
        v_data: &mut ([T; 2], Option<[G::NodeId; 2]>),
        query: impl Query<Node = G::NodeId>,
    ) {
        // If the relaxed node is one of the target, set the bound to the upper bound of its label.
        if query.target() == Some(v) {
            self.bound.update(v_data.0[1]);
        }
    }
}

/// A wrapper around [DijkstraOps] that adds a hop-limit.
///
/// All nodes that are further away from a source node than a given maximum number of edges are
/// skipped.
///
/// See [HopLimit] for more.
///
/// # Example
///
/// ```
/// use dijkstra::DijkstraSearch;
/// use dijkstra::ops::ScalarDijkstra;
/// use dijkstra::query::PointToPointQuery;
/// use hashbrown::HashMap;
/// use petgraph::graph::{node_index, DiGraph, EdgeReference};
/// use priority_queue::PriorityQueue;
/// use tch::HopLimit;
/// use tch::ops::HopLimitedDijkstra;
///
/// // Standard scalar Dijkstra search with a hop limit of 1.
/// let mut search = DijkstraSearch::new(HashMap::new(), HashMap::new(), PriorityQueue::new());
/// let graph = DiGraph::<(), i32>::from_edges(&[(0, 1, 1), (1, 2, 2), (0, 2, 4)]);
/// let mut map = HashMap::new();
/// let mut ops = HopLimitedDijkstra::new(
///     ScalarDijkstra::new_forward(&graph, |e: EdgeReference<i32>| *e.weight()),
///     HopLimit::new(1, &mut map),
/// );
/// let query = PointToPointQuery::new(node_index(0), node_index(2), 0);
/// search.solve_query(&query, &mut ops).unwrap();
/// // Only possible path with a hop limit of 1 is edge 0 -> 2.
/// assert_eq!(search.get_label(&node_index(2)), Some(&4));
/// assert_eq!(
///     search.get_path(&node_index(2)).unwrap(),
///     vec![node_index(0), node_index(2)]
/// );
/// ```
pub struct HopLimitedDijkstra<O> {
    ops: O,
    hop_limit: u8,
}

impl<O> HopLimitedDijkstra<O> {
    /// Initialize a new HopLimitedDijkstra instance.
    pub fn new(ops: O, hop_limit: u8) -> Self {
        HopLimitedDijkstra { ops, hop_limit }
    }
}

impl<O> DijkstraOps for HopLimitedDijkstra<O>
where
    O: DijkstraOps,
    O::Node: IndexType,
{
    type Node = O::Node;
    type Edge = O::Edge;
    type Data = NodeDataWithExtra<O::Data, u8>;
    type Key = O::Key;
    type EdgeIterator = O::EdgeIterator;

    fn link(
        &self,
        current_label: &<O::Data as NodeData>::Label,
        edge: Self::Edge,
    ) -> <O::Data as NodeData>::Label {
        (self.ops).link(current_label, edge)
    }
    fn as_new_data(
        &self,
        prev: Option<Self::Node>,
        label: <O::Data as NodeData>::Label,
    ) -> NodeDataWithExtra<O::Data, u8> {
        NodeDataWithExtra {
            data: (self.ops).as_new_data(prev, label),
            extra: 0,
        }
    }
    fn get_next_node(&self, edge: Self::Edge) -> Self::Node {
        (self.ops).get_next_node(edge)
    }
    fn edges_from(&self, node: Self::Node) -> Self::EdgeIterator {
        (self.ops).edges_from(node)
    }
    fn get_key(&self, label: &<O::Data as NodeData>::Label) -> Self::Key {
        (self.ops).get_key(label)
    }
    fn relax_existing_label(
        &self,
        node: Self::Node,
        new_label: <O::Data as NodeData>::Label,
        node_data: &mut NodeDataWithExtra<O::Data, u8>,
    ) -> Option<Self::Key> {
        (self.ops).relax_existing_label(node, new_label, &mut node_data.data)
    }
    fn stop(&self, node: Self::Node, key: Self::Key, query: impl Query<Node = Self::Node>) -> bool {
        (self.ops).stop(node, key, query)
    }
    fn node_is_relaxed(
        &mut self,
        u: Self::Node,
        v: Self::Node,
        u_data: &NodeDataWithExtra<O::Data, u8>,
        v_data: &mut NodeDataWithExtra<O::Data, u8>,
        query: impl Query<Node = Self::Node>,
    ) {
        // Update the number of hop for v.
        let nb_hop = u_data.extra + 1;
        if v_data.extra == 0 {
            v_data.extra = nb_hop;
        } else {
            v_data.extra = std::cmp::min(v_data.extra, nb_hop);
        }
        (self.ops).node_is_relaxed(u, v, &u_data.data, &mut v_data.data, query)
    }
    fn skip_node<D: NodeData<Label = <O::Data as NodeData>::Label>>(
        &self,
        node: Self::Node,
        node_data: &NodeDataWithExtra<O::Data, u8>,
        data: &HashMap<Self::Node, D>,
    ) -> bool {
        node_data.extra > self.hop_limit || (self.ops).skip_node(node, &node_data.data, data)
    }
}

pub struct BoundedDijkstra<O>(pub O);

impl<O> DijkstraOps for BoundedDijkstra<O>
where
    O: DijkstraOps,
{
    type Node = O::Node;
    type Edge = O::Edge;
    type Data = NodeDataWithExtra<O::Data, Option<O::Key>>;
    type Key = O::Key;
    type EdgeIterator = O::EdgeIterator;

    fn link(
        &self,
        current_label: &<O::Data as NodeData>::Label,
        edge: Self::Edge,
    ) -> <O::Data as NodeData>::Label {
        (self.0).link(current_label, edge)
    }
    fn as_new_data(
        &self,
        prev: Option<Self::Node>,
        label: <O::Data as NodeData>::Label,
    ) -> NodeDataWithExtra<O::Data, Option<O::Key>> {
        NodeDataWithExtra {
            data: (self.0).as_new_data(prev, label),
            extra: None,
        }
    }
    fn get_next_node(&self, edge: Self::Edge) -> Self::Node {
        (self.0).get_next_node(edge)
    }
    fn edges_from(&self, node: Self::Node) -> Self::EdgeIterator {
        (self.0).edges_from(node)
    }
    fn get_key(&self, label: &<O::Data as NodeData>::Label) -> Self::Key {
        (self.0).get_key(label)
    }
    fn relax_existing_label(
        &self,
        node: Self::Node,
        new_label: <O::Data as NodeData>::Label,
        node_data: &mut Self::Data,
    ) -> Option<Self::Key> {
        (self.0).relax_existing_label(node, new_label, &mut node_data.data)
    }
    fn stop(&self, node: Self::Node, key: Self::Key, query: impl Query<Node = Self::Node>) -> bool {
        (self.0).stop(node, key, query)
    }
    fn node_is_relaxed(
        &mut self,
        u: Self::Node,
        v: Self::Node,
        u_data: &Self::Data,
        v_data: &mut Self::Data,
        query: impl Query<Node = Self::Node>,
    ) {
        (self.0).node_is_relaxed(u, v, &u_data.data, &mut v_data.data, query)
    }
    fn skip_node<D: NodeData<Label = <Self::Data as NodeData>::Label>>(
        &self,
        node: Self::Node,
        node_data: &Self::Data,
        data: &HashMap<Self::Node, D>,
    ) -> bool {
        (self.0).skip_node(node, &node_data.data, data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::query::PointToPointQuery;
    use crate::search::DijkstraSearch;
    use hashbrown::HashMap;
    use petgraph::graph::{node_index, DiGraph, EdgeReference};
    use petgraph::visit::EdgeRef;
    use priority_queue::PriorityQueue;
    use ttf::PwlTTF;

    #[test]
    fn profile_dijkstra_test() {
        // Example where node re-insert is important.
        // Network is:
        //   1
        //  / \
        // 0   3 - 4
        //  \ /
        //   2
        let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let graph = DiGraph::<(), TTF<f64>>::from_edges(&[
            (
                0,
                1,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![(0., 5.), (100., 5.)])),
            ),
            (
                1,
                3,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![(0., 5.), (100., 5.)])),
            ),
            (
                0,
                2,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![
                    (0., 0.),
                    (50., 10.),
                    (100., 0.),
                ])),
            ),
            (
                2,
                3,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![
                    (0., 0.),
                    (60., 10.),
                    (100., 0.),
                ])),
            ),
            (
                3,
                4,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![(0., 0.), (100., 0.)])),
            ),
        ]);
        let mut ops = ProfileDijkstra::new_forward(&graph, |e: EdgeReference<_>| &graph[e.id()]);

        let query = PointToPointQuery::from_default(node_index(0), node_index(4));
        search.solve_query(&query, &mut ops);

        let ttf = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
            (0., 0.),
            (25., 10.),
            (75., 10.),
            (100., 0.),
        ]));
        assert_eq!(search.get_label(&node_index(4)).unwrap(), &ttf);
    }

    #[test]
    fn profile_interval_dijkstra_test() {
        // Example where node re-insert is important.
        // Network is:
        //   1
        //  / \
        // 0   3 - 4
        //  \ /
        //   2
        let mut search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let graph = DiGraph::<(), TTF<f64>>::from_edges(&[
            (
                0,
                1,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![(0., 5.), (100., 5.)])),
            ),
            (
                1,
                3,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![(0., 5.), (100., 5.)])),
            ),
            (
                0,
                2,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![
                    (0., 0.),
                    (50., 10.),
                    (100., 0.),
                ])),
            ),
            (
                2,
                3,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![
                    (0., 0.),
                    (60., 10.),
                    (100., 0.),
                ])),
            ),
            (
                3,
                4,
                TTF::Piecewise(PwlTTF::from_breakpoints(vec![(0., 0.), (100., 0.)])),
            ),
        ]);
        let mut ops =
            ProfileIntervalDijkstra::new_forward(&graph, |e: EdgeReference<_>| &graph[e.id()]);

        let query = PointToPointQuery::from_default(node_index(0), node_index(4));
        search.solve_query(&query, &mut ops);

        assert_eq!(search.get_label(&node_index(4)), Some(&[0., 10.]));
    }
}
