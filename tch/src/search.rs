use super::min_queue::MinPriorityQueue;
use super::node_data::NodeData;
use super::ops::DijkstraOps;
use super::query::QueryRef;

use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use petgraph::graph::NodeIndex;

/// A data structure that can be used to run any uni-directional Dijkstra's algorithm.
///
/// The structure is composed of:
///
/// - A [NodeMap] to store the nodes' data (including the labels and the predecessors).
///
/// - A [MinPriorityQueue] that represent the order in which the nodes are settled.
#[derive(Clone, Debug, Default)]
pub struct DijkstraSearch<D, PQ> {
    /// A map Node -> Data.
    data: HashMap<NodeIndex, D>,
    /// A priority queue over nodes' keys.
    queue: PQ,
}

impl<D, PQ> DijkstraSearch<D, PQ> {
    /// Initialize a new DijkstraRun.
    pub fn new(data: HashMap<NodeIndex, D>, queue: PQ) -> Self {
        DijkstraSearch { data, queue }
    }

    /// Return a reference to the node map of the DijkstraSearch.
    pub fn node_map(&self) -> &HashMap<NodeIndex, D> {
        &self.data
    }

    /// Return a mutable reference to the node map of the DijkstraSearch.
    pub fn node_map_mut(&mut self) -> &mut HashMap<NodeIndex, D> {
        &mut self.data
    }

    /// Return a reference to the priority queue of the DijkstraSearch.
    pub fn priority_queue(&self) -> &PQ {
        &self.queue
    }

    /// Return a mutable reference to the priority queue of the DijkstraSearch.
    pub fn priority_queue_mut(&mut self) -> &mut PQ {
        &mut self.queue
    }
}

impl<D, PQ> DijkstraSearch<D, PQ>
where
    PQ: MinPriorityQueue,
{
    /// Return true if the priority queue is empty.
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// Reset all data structures of the instance.
    pub fn reset(&mut self) {
        self.data.clear();
        self.queue.reset();
    }

    /// Empty the priority queue.
    pub fn empty_queue(&mut self) {
        self.queue.reset();
    }

    /// Pop the element with minimum value in the queue.
    pub fn pop_queue(&mut self) -> Option<(PQ::Key, PQ::Value)> {
        self.queue.pop()
    }
}

impl<PQ, D, K> DijkstraSearch<D, PQ>
where
    PQ: MinPriorityQueue<Key = NodeIndex, Value = K>,
    K: Copy,
{
    /// Initialize and solve a [QueryRef], using the given [DijkstraOps].
    ///
    /// This does not return any result but the results can be retrieved from the internal
    /// structure of the DijkstraSearch or from the [DijkstraOps].
    ///
    /// The [QueryRef], [DijkstraOps] and DijkstraSearch must all be compatible.
    /// In particular:
    ///
    /// - The Node type must coincide.
    ///
    /// - The Key type must coincide.
    ///
    /// - The Data type must coincide.
    pub fn solve_query<Q, O, L>(&mut self, query: Q, ops: &mut O)
    where
        Q: QueryRef<Node = NodeIndex, Label = L>,
        O: DijkstraOps<Node = NodeIndex, Data = D, Key = K>,
        D: NodeData<Label = L>,
    {
        self.init_query(query, ops);
        self.solve(query, ops);
    }

    /// Reset the search and initialize a new [QueryRef], using the given [DijkstraOps].
    pub fn init_query<Q, O, L>(&mut self, query: Q, ops: &O)
    where
        Q: QueryRef<Node = NodeIndex, Label = L>,
        O: DijkstraOps<Node = NodeIndex, Data = D, Key = K>,
        D: NodeData<Label = L>,
    {
        self.reset();
        for (source, label) in query.sources_with_labels() {
            let key = ops.get_key(&label);
            self.queue.push(source, key);
            self.data.insert(source, ops.as_new_data(None, label));
        }
    }

    /// Solve a query that is already initialized.
    fn solve<Q, O, L>(&mut self, query: Q, ops: &mut O)
    where
        Q: QueryRef<Node = NodeIndex, Label = L>,
        O: DijkstraOps<Node = NodeIndex, Data = D, Key = K>,
        D: NodeData<Label = L>,
    {
        // Settle the nodes in order of increasing priority in the queue.
        while let Some((node, key)) = self.pop_queue() {
            self.settle_node(node, key, query, ops);
        }
    }

    /// Settle the next node of the Dijkstra run, i.e., relax all its edges.
    pub fn settle_node<Q, O, L>(&mut self, node: NodeIndex, key: K, query: Q, ops: &mut O)
    where
        Q: QueryRef<Node = NodeIndex, Label = L>,
        O: DijkstraOps<Node = NodeIndex, Data = D, Key = K>,
        D: NodeData<Label = L>,
    {
        if ops.stop(node, key, query) {
            // Empty the queue so that the search will stop.
            self.empty_queue();
            return;
        }
        // We want to access data for `node` without borrowing `self.data` so we remove the data
        // from the HashMap.
        let node_data = self.data.remove(&node).unwrap();
        if ops.skip_node(node, &node_data, &self.data) {
            debug_assert!(!self.data.contains_key(&node));
            self.data.insert(node, node_data);
            return;
        }
        for edge in ops.edges_from(node) {
            self.relax_edge(edge, node, &node_data, query, ops);
        }
        // We re-insert the data now.
        // The function `relax_edge` did not try to modify it as long as self-loops are not
        // allowed.
        debug_assert!(!self.data.contains_key(&node));
        self.data.insert(node, node_data);
    }

    /// Relax an edge.
    ///
    /// Arguments:
    ///
    /// - `edge`: The edge to relax
    ///
    /// - `current`: The node that is currently settled. This is an endpoint of the edge. The other
    /// endpoint being the node to update.
    ///
    /// - `key`: The key of node `current`.
    ///
    /// - `query`: The query that we want to solve.
    ///
    /// - `ops`: A [DijkstraOps] that describes how to solve the query.
    fn relax_edge<Q, O, L>(
        &mut self,
        uv_edge: O::Edge,
        u: NodeIndex,
        u_data: &D,
        query: Q,
        ops: &mut O,
    ) where
        Q: QueryRef<Node = NodeIndex, Label = L>,
        O: DijkstraOps<Node = NodeIndex, Data = D, Key = K>,
        D: NodeData<Label = L>,
    {
        let v = ops.get_next_node(uv_edge);
        // This operation is safe as long as there is no self-loop edges (so that `u_data` is
        // always different from `v_data`).
        let v_label_from_u = ops.link(u_data.label(), uv_edge);
        let v_data = if let Some(v_data) = self.data.get_mut(&v) {
            if let Some(new_key) = ops.relax_existing_label(u, v_label_from_u, v_data) {
                self.queue.decrease_value(v, new_key);
            }
            v_data
        } else {
            self.queue.push(v, ops.get_key(&v_label_from_u));
            let v_data = ops.as_new_data(Some(u), v_label_from_u);
            self.data.insert_unique_unchecked(v, v_data).1
        };
        ops.node_is_relaxed(u, v, u_data, v_data, query);
    }
}

impl<PQ, D> DijkstraSearch<D, PQ> {
    /// Return the current label of a node (or `None` if the node has never been explored).
    pub fn get_data(&self, node: &NodeIndex) -> Option<&D> {
        self.data.get(node)
    }
}

impl<PQ, D, L> DijkstraSearch<D, PQ>
where
    D: NodeData<Label = L>,
{
    /// Return the current label of a node (or `None` if the node has never been explored).
    pub fn get_label(&self, node: &NodeIndex) -> Option<&L> {
        self.data.get(node).map(|d| d.label())
    }
}

impl<PQ, D, P> DijkstraSearch<D, PQ>
where
    D: NodeData<Predecessor = P>,
{
    /// Return the current label of a node (or `None` if the node has never been explored).
    pub fn get_predecessor(&self, node: &NodeIndex) -> Option<&P> {
        self.data.get(node).and_then(|d| d.predecessor())
    }
}

impl<PQ, D, K> DijkstraSearch<D, PQ>
where
    PQ: MinPriorityQueue<Key = NodeIndex, Value = K>,
    K: Copy,
{
    /// Peek the value of the next key in the priority queue.
    pub fn peek_key(&self) -> Option<K> {
        self.queue.peek().map(|(_, &k)| k)
    }
}

// Implementations where the Predecessor type coincide with the Node type.
impl<PQ, D> DijkstraSearch<D, PQ>
where
    D: NodeData<Predecessor = NodeIndex>,
{
    /// Return the reverse path from any source node to `end`.
    ///
    /// The function takes recursively the predecessors of the current node until a node without
    /// predecessor is reached.
    pub fn get_reverse_path(&self, &end: &NodeIndex) -> Result<Vec<NodeIndex>> {
        let mut path = vec![end];
        let mut visited = HashSet::new();
        visited.insert(end);
        let mut next = end;
        while let Some(&pred) = self.get_predecessor(&next) {
            path.push(pred);
            if visited.contains(&pred) {
                return Err(anyhow!("Found a loop in the shortest path: {:?}", path));
            }
            visited.insert(pred);
            next = pred;
        }
        Ok(path)
    }

    /// Return the path, from any source node to `end`, as a vector of nodes, using the predecessor
    /// map of the DijkstraSearch.
    ///
    /// The path returned is only valid if the predecessor map is filled correctly and if the node
    /// `end` has been reached by the search.
    pub fn get_path(&self, end: &NodeIndex) -> Result<Vec<NodeIndex>> {
        let mut path = self.get_reverse_path(end)?;
        path.reverse();
        Ok(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hashbrown::HashMap;
    use petgraph::graph::node_index;
    use priority_queue::PriorityQueue;

    #[test]
    fn path_test() {
        let mut labels: HashMap<NodeIndex, (i32, Option<NodeIndex>)> = HashMap::new();
        labels.insert(node_index(1), (0, Some(node_index(0))));
        labels.insert(node_index(2), (0, Some(node_index(1))));
        labels.insert(node_index(3), (0, Some(node_index(4))));
        labels.insert(node_index(4), (0, Some(node_index(3))));
        let priority_queue: PriorityQueue<NodeIndex, ()> = PriorityQueue::new();
        let search = DijkstraSearch::new(labels, priority_queue);
        assert_eq!(
            search.get_path(&node_index(2)).unwrap(),
            vec![node_index(0), node_index(1), node_index(2)]
        );
        assert!(search.get_path(&node_index(4)).is_err());
    }
}
