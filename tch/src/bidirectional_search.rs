// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use anyhow::{Context, Result};
use petgraph::{graph::NodeIndex, Direction};

use crate::bidirectional_ops::BidirectionalDijkstraOps;
use crate::min_queue::MinPriorityQueue;
use crate::node_data::NodeData;
use crate::ops::DijkstraOps;
use crate::query::*;
use crate::search::DijkstraSearch;

/// A data structure that can be used to run bidirectional Dijkstra's algorithms.
///
/// The structure holds a forward and a backward [DijkstraSearch].
#[derive(Clone, Debug)]
pub struct BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2> {
    forward_search: DijkstraSearch<FData, PQ1>,
    backward_search: DijkstraSearch<BData, PQ2>,
    current_direction: Direction,
}

impl<FData, BData, PQ1, PQ2> Default for BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2>
where
    FData: Default,
    BData: Default,
    PQ1: Default,
    PQ2: Default,
{
    fn default() -> Self {
        BidirectionalDijkstraSearch {
            forward_search: Default::default(),
            backward_search: Default::default(),
            current_direction: Direction::Incoming,
        }
    }
}

impl<FData, BData, PQ1, PQ2> BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2> {
    /// Initializes a new BidirectionalDijkstraSearch from a forward and a backward
    /// [DijkstraSearch].
    pub fn new(
        forward_search: DijkstraSearch<FData, PQ1>,
        backward_search: DijkstraSearch<BData, PQ2>,
    ) -> Self {
        BidirectionalDijkstraSearch {
            forward_search,
            backward_search,
            current_direction: Direction::Incoming,
        }
    }

    /// Returns a reference to the [DijkstraSearch] for the forward direction.
    pub fn get_forward_search(&self) -> &DijkstraSearch<FData, PQ1> {
        &self.forward_search
    }

    /// Returns a reference to the [DijkstraSearch] for the backward direction.
    pub fn get_backward_search(&self) -> &DijkstraSearch<BData, PQ2> {
        &self.backward_search
    }
}

impl<FData, BData, PQ1, PQ2> BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2>
where
    PQ1: MinPriorityQueue,
    PQ2: MinPriorityQueue,
{
    /// Resets all data structures of the BidirectionalDijkstraSearch.
    pub fn reset(&mut self) {
        self.forward_search.reset();
        self.backward_search.reset();
        self.current_direction = Direction::Incoming;
    }
}

impl<PQ1, PQ2, FData, BData, FKey, BKey> BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2>
where
    PQ1: MinPriorityQueue<Key = NodeIndex, Value = FKey>,
    PQ2: MinPriorityQueue<Key = NodeIndex, Value = BKey>,
    FKey: Copy,
    BKey: Copy,
{
    /// Resets the search and initialize a new [BidirectionalQueryRef], using the given
    /// [BidirectionalDijkstraOps].
    pub fn init_query<Q, O, FLabel, BLabel>(&mut self, query: Q, ops: &mut O)
    where
        Q: BidirectionalQueryRef<Node = NodeIndex, Label = FLabel, RevLabel = BLabel>,
        O: BidirectionalDijkstraOps<Node = NodeIndex>,
        O::FOps: DijkstraOps<Data = FData, Key = FKey>,
        O::BOps: DijkstraOps<Data = BData, Key = BKey>,
        FData: NodeData<Label = FLabel>,
        BData: NodeData<Label = BLabel>,
    {
        self.reset();
        self.forward_search.init_query(query, ops.forward_ops());
        self.backward_search
            .init_query(query.reverse(), ops.backward_ops());
    }

    /// Initializes and solve a [BidirectionalQueryRef], using the given
    /// [BidirectionalDijkstraOps].
    ///
    /// This does not return any result but the results can be retrieved from the internal structure
    /// of the BidirectionalDijkstraSearch or from the BidirectionalDijkstraOps.
    ///
    /// The [BidirectionalQueryRef], [BidirectionalDijkstraOps] and [BidirectionalDijkstraSearch]
    /// must all be compatible. In particular:
    ///
    /// - The Node type must coincide.
    ///
    /// - The Key type must coincide, for both the forward and backward search.
    ///
    /// - The Label type must coincide, for both the forward and backward search.
    ///
    /// - The Predecessor type must coincide, for both the forward and backward search.
    pub fn solve_query<Q, O, FLabel, BLabel>(&mut self, query: Q, ops: &mut O)
    where
        Q: BidirectionalQueryRef<Node = NodeIndex, Label = FLabel, RevLabel = BLabel>,
        O: BidirectionalDijkstraOps<Node = NodeIndex>,
        O::FOps: DijkstraOps<Data = FData, Key = FKey>,
        O::BOps: DijkstraOps<Data = BData, Key = BKey>,
        FData: NodeData<Label = FLabel>,
        BData: NodeData<Label = BLabel>,
    {
        self.init_query(query, ops);
        self.solve(query, ops);
    }

    /// Switches the direction of the search.
    ///
    /// If the priority queue of the new direction is empty, the direction is not switched so that
    /// both priority queues get emptied before the algorithm stops.
    fn change_direction(&mut self) {
        match self.current_direction {
            Direction::Outgoing => {
                if !self.backward_search.is_empty() {
                    self.current_direction = Direction::Incoming;
                }
            }
            Direction::Incoming => {
                if !self.forward_search.is_empty() {
                    self.current_direction = Direction::Outgoing;
                }
            }
        }
    }

    /// Finds the next node that needs to be settled and settle it.
    pub fn next<Q, O, FLabel, BLabel>(&mut self, query: Q, ops: &mut O)
    where
        Q: BidirectionalQueryRef<Node = NodeIndex, Label = FLabel, RevLabel = BLabel>,
        O: BidirectionalDijkstraOps<Node = NodeIndex>,
        O::FOps: DijkstraOps<Data = FData, Key = FKey>,
        O::BOps: DijkstraOps<Data = BData, Key = BKey>,
        FData: NodeData<Label = FLabel>,
        BData: NodeData<Label = BLabel>,
    {
        self.change_direction();
        match self.current_direction {
            Direction::Outgoing => {
                if let Some((node, key)) = self.forward_search.pop_queue() {
                    // The target node is not stalled so to make sure that the pre-settly check is
                    // running on it.
                    if Some(node) != query.target()
                        && ops.can_be_stalled(
                            node,
                            Some(key),
                            None,
                            self.forward_search.node_map_mut(),
                            self.backward_search.node_map_mut(),
                        )
                    {
                        return;
                    }
                    if let Some(back_label) = self.backward_search.get_data(&node) {
                        // The backward search has already visited this node.
                        // We retrieve the forward label and run the pre-settle check.
                        if ops.pre_settle_check(
                            node,
                            self.forward_search.get_data(&node).unwrap(),
                            back_label,
                            Some(key),
                            self.backward_search.peek_key(),
                            query,
                        ) {
                            self.empty_queues();
                            return;
                        }
                    }
                    self.forward_search
                        .settle_node(node, key, query, ops.forward_ops());
                }
            }
            Direction::Incoming => {
                if let Some((node, key)) = self.backward_search.pop_queue() {
                    // The source node is not stalled so to make sure that the pre-settly check is
                    // running on it.
                    if query.sources().any(|s| s == node)
                        && ops.can_be_stalled(
                            node,
                            None,
                            Some(key),
                            self.forward_search.node_map_mut(),
                            self.backward_search.node_map_mut(),
                        )
                    {
                        return;
                    }
                    if let Some(forw_label) = self.forward_search.get_data(&node) {
                        // The forward search has already visited this node.
                        // We retrieve the backward label and run the pre-settle check.
                        if ops.pre_settle_check(
                            node,
                            forw_label,
                            self.backward_search.get_data(&node).unwrap(),
                            self.forward_search.peek_key(),
                            Some(key),
                            query,
                        ) {
                            self.empty_queues();
                            return;
                        }
                    }
                    self.backward_search.settle_node(
                        node,
                        key,
                        query.reverse(),
                        ops.backward_ops(),
                    );
                }
            }
        }
    }

    /// Solves a query by settling nodes until the priority queues for both directions are empty.
    pub fn solve<Q, O, FLabel, BLabel>(&mut self, query: Q, ops: &mut O)
    where
        Q: BidirectionalQueryRef<Node = NodeIndex, Label = FLabel, RevLabel = BLabel>,
        O: BidirectionalDijkstraOps<Node = NodeIndex>,
        O::FOps: DijkstraOps<Data = FData, Key = FKey>,
        O::BOps: DijkstraOps<Data = BData, Key = BKey>,
        FData: NodeData<Label = FLabel>,
        BData: NodeData<Label = BLabel>,
    {
        while !self.forward_search.is_empty() || !self.backward_search.is_empty() {
            self.next(query, ops);
        }
    }

    /// Empties the priority queue of both the forward and backward search.
    fn empty_queues(&mut self) {
        self.forward_search.empty_queue();
        self.backward_search.empty_queue();
    }
}

impl<PQ1, PQ2, FData, BData> BidirectionalDijkstraSearch<FData, BData, PQ1, PQ2>
where
    FData: NodeData<Predecessor = NodeIndex>,
    BData: NodeData<Predecessor = NodeIndex>,
{
    /// Returns a path from a source to a target of the current query, given the meeting node of the
    /// forward and backward search.
    ///
    /// The path returned is valid only if the predecessor maps of the forward and backward
    /// searches are filled correctly and if the given meeting node is effectively a valid meeting
    /// node.
    pub fn get_path(&self, meeting_node: NodeIndex) -> Result<Vec<NodeIndex>> {
        // Forward path from a source of the forward search to the meeting node.
        let mut path = self
            .forward_search
            .get_path(&meeting_node)
            .context("Failed to compute forward path")?;
        // Backward path from the meeting node to a source of the backward search (i.e., a target
        // of the query).
        let back_path = self
            .backward_search
            .get_reverse_path(&meeting_node)
            .context("Failed to compute backward path")?;
        // Extend the forward path with the backward path (excluding the meeting node so that it is
        // not repeated.
        path.extend_from_slice(&back_path[1..]);
        Ok(path)
    }
}
