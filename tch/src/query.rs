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

//! Traits and structs used to represent Dijkstra queries.
use std::iter;

/// A Dijkstra query with 1 or more source nodes and 0 or more target nodes.
pub trait Query {
    /// Type of the source / target nodes.
    type Node;
    /// Type of the node labels.
    type Label;
    /// Iterates over the source nodes of the query.
    fn sources<'a>(&'a self) -> Box<dyn Iterator<Item = Self::Node> + 'a>;
    /// Returns the target node of the query (if any).
    fn target(&self) -> Option<Self::Node>;
    /// Iterates over the source nodes together with their initial label.
    fn sources_with_labels<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (Self::Node, Self::Label)> + 'a>;
}

impl<Q> Query for &Q
where
    Q: Query,
{
    type Node = Q::Node;
    type Label = Q::Label;
    fn sources<'a>(&'a self) -> Box<dyn Iterator<Item = Q::Node> + 'a> {
        (*self).sources()
    }
    fn target(&self) -> Option<Q::Node> {
        (*self).target()
    }
    fn sources_with_labels<'a>(&'a self) -> Box<dyn Iterator<Item = (Q::Node, Q::Label)> + 'a> {
        (*self).sources_with_labels()
    }
}

/// A copyable reference to a [Query].
pub trait QueryRef: Copy + Query {}

impl<Q> QueryRef for &Q where Q: Query {}

/// A Dijkstra query with 1 or more source nodes and 1 or more target nodes and that can be run in
/// both directions.
pub trait BidirectionalQuery: Query {
    /// Type fo the node labels from reverse direction.
    type RevLabel;
    /// Type of the reverse query.
    type RevQuery: Query<Node = Self::Node, Label = Self::RevLabel>;
    /// Returns the query corresponding to the reverse direction.
    fn reverse(&self) -> &Self::RevQuery;
}

impl<Q> BidirectionalQuery for &Q
where
    Q: BidirectionalQuery,
{
    type RevLabel = Q::RevLabel;
    type RevQuery = Q::RevQuery;
    fn reverse(&self) -> &Q::RevQuery {
        (*self).reverse()
    }
}

/// A copyable reference to a [BidirectionalQuery].
pub trait BidirectionalQueryRef: Copy + BidirectionalQuery + QueryRef {}

impl<Q> BidirectionalQueryRef for &Q where Q: BidirectionalQuery {}

/// A query from one source node to all nodes.
#[derive(Clone, Debug)]
pub struct SingleSourceQuery<N, L> {
    source: N,
    initial_label: L,
}

impl<N, L> SingleSourceQuery<N, L> {
    /// Creates a new [SingleSourceQuery] from the given source node and its initial label.
    pub fn new(source: N, initial_label: L) -> Self {
        SingleSourceQuery {
            source,
            initial_label,
        }
    }
}

impl<N, L: Default> SingleSourceQuery<N, L> {
    /// Creates a new [SingleSourceQuery] from the given source node, using the default value as
    /// label.
    pub fn from_default(source: N) -> Self {
        SingleSourceQuery::new(source, Default::default())
    }
}

impl<N: Copy, L: Clone> Query for SingleSourceQuery<N, L> {
    type Node = N;
    type Label = L;
    fn sources<'a>(&'a self) -> Box<dyn Iterator<Item = N> + 'a> {
        Box::new(iter::once(self.source))
    }
    fn target(&self) -> Option<N> {
        None
    }
    fn sources_with_labels<'a>(&'a self) -> Box<dyn Iterator<Item = (N, L)> + 'a> {
        Box::new(iter::once((self.source, self.initial_label.clone())))
    }
}

/// A query from one source node to one target node.
#[derive(Clone, Debug)]
pub struct PointToPointQuery<N, L> {
    source: N,
    target: N,
    initial_label: L,
}

impl<N, L> PointToPointQuery<N, L> {
    /// Creates a new [PointToPointQuery] from the given source and target node and the initial
    /// label of the source node.
    pub fn new(source: N, target: N, initial_label: L) -> Self {
        PointToPointQuery {
            source,
            target,
            initial_label,
        }
    }
}

impl<N, L: Default> PointToPointQuery<N, L> {
    /// Creates a new [PointToPointQuery] from the given source and target node, using the default
    /// value as label.
    pub fn from_default(source: N, target: N) -> Self {
        PointToPointQuery::new(source, target, Default::default())
    }
}

impl<N: Copy, L: Clone> Query for PointToPointQuery<N, L> {
    type Node = N;
    type Label = L;
    fn sources<'a>(&'a self) -> Box<dyn Iterator<Item = N> + 'a> {
        Box::new(iter::once(self.source))
    }
    fn target(&self) -> Option<N> {
        Some(self.target)
    }
    fn sources_with_labels<'a>(&'a self) -> Box<dyn Iterator<Item = (N, L)> + 'a> {
        Box::new(iter::once((self.source, self.initial_label.clone())))
    }
}

/// A query from multiple source nodes to all other nodes.
#[derive(Clone, Debug)]
pub struct MultipleSourcesQuery<N, L> {
    sources: Vec<N>,
    labels: Vec<L>,
    target: Option<N>,
}

impl<N, L> MultipleSourcesQuery<N, L> {
    /// Creates a new [MultipleSourcesQuery] from a vector of source nodes and their initial
    /// labels.
    ///
    /// To get the label of a given source node, the query cycles over the labels so the number of
    /// labels can be smaller or larger than the number of source nodes.
    pub fn new(sources: Vec<N>, labels: Vec<L>) -> Self {
        MultipleSourcesQuery {
            sources,
            labels,
            target: None,
        }
    }

    /// Creates a new [MultipleSourcesQuery] from a vector of source nodes, their initial labels
    /// and a target node.
    ///
    /// To get the label of a given source node, the query cycles over the labels so the number of
    /// labels can be smaller or larger than the number of source nodes.
    pub fn with_target(target: N, sources: Vec<N>, labels: Vec<L>) -> Self {
        MultipleSourcesQuery {
            sources,
            labels,
            target: Some(target),
        }
    }
}

impl<N, L: Default> MultipleSourcesQuery<N, L> {
    /// Creates a new [MultipleSourcesQuery] from a vector of source nodes, using the default value
    /// as label.
    pub fn from_default(sources: Vec<N>) -> Self {
        MultipleSourcesQuery::new(sources, vec![Default::default()])
    }
}

impl<N: Copy, L: Clone> Query for MultipleSourcesQuery<N, L> {
    type Node = N;
    type Label = L;
    fn sources<'a>(&'a self) -> Box<dyn Iterator<Item = N> + 'a> {
        Box::new(self.sources.iter().copied())
    }
    fn target(&self) -> Option<N> {
        self.target
    }
    fn sources_with_labels<'a>(&'a self) -> Box<dyn Iterator<Item = (N, L)> + 'a> {
        // If there are less labels than nodes, we cycle over the labels.
        Box::new(
            self.sources
                .iter()
                .copied()
                .zip(self.labels.iter().cycle().cloned()),
        )
    }
}

/// A bidirectional query from one source to one target.
#[derive(Clone, Debug)]
pub struct BidirectionalPointToPointQuery<N, L0, L1> {
    forw_query: PointToPointQuery<N, L0>,
    back_query: PointToPointQuery<N, L1>,
}

impl<N: Copy, L0, L1> BidirectionalPointToPointQuery<N, L0, L1> {
    /// Creates a new [BidirectionalPointToPointQuery] from a source and target node and their
    /// respective initial label.
    pub fn new(source: N, target: N, forward_label: L0, backward_label: L1) -> Self {
        let forw_query = PointToPointQuery::new(source, target, forward_label);
        let back_query = PointToPointQuery::new(target, source, backward_label);
        BidirectionalPointToPointQuery {
            forw_query,
            back_query,
        }
    }
}

impl<N: Copy, L0: Default, L1: Default> BidirectionalPointToPointQuery<N, L0, L1> {
    /// Creates a new [BidirectionalPointToPointQuery] from a source and target node, using the
    /// default values as labels.
    pub fn from_default(source: N, target: N) -> Self {
        let forw_query = PointToPointQuery::new(source, target, Default::default());
        let back_query = PointToPointQuery::new(target, source, Default::default());
        BidirectionalPointToPointQuery {
            forw_query,
            back_query,
        }
    }
}

impl<N: Copy, L0: Clone, L1> Query for BidirectionalPointToPointQuery<N, L0, L1> {
    type Node = N;
    type Label = L0;
    fn sources<'a>(&'a self) -> Box<dyn Iterator<Item = N> + 'a> {
        self.forw_query.sources()
    }
    fn target(&self) -> Option<N> {
        self.forw_query.target()
    }
    fn sources_with_labels<'a>(&'a self) -> Box<dyn Iterator<Item = (N, L0)> + 'a> {
        self.forw_query.sources_with_labels()
    }
}

impl<N, L0, L1> BidirectionalQuery for BidirectionalPointToPointQuery<N, L0, L1>
where
    N: Copy,
    L0: Clone,
    L1: Clone,
{
    type RevLabel = L1;
    type RevQuery = PointToPointQuery<N, L1>;
    fn reverse(&self) -> &PointToPointQuery<N, L1> {
        &self.back_query
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiple_sources_test() {
        let query = MultipleSourcesQuery::new(vec![0, 1, 2], vec![0., 1.]);
        let mut sources_with_labels = query.sources_with_labels();
        assert_eq!(sources_with_labels.next(), Some((0, 0.)));
        assert_eq!(sources_with_labels.next(), Some((1, 1.)));
        assert_eq!(sources_with_labels.next(), Some((2, 0.)));
        assert_eq!(sources_with_labels.next(), None);

        let query = MultipleSourcesQuery::new(vec![0, 1, 2], vec![0., 1., 2., 3.]);
        let mut sources_with_labels = query.sources_with_labels();
        assert_eq!(sources_with_labels.next(), Some((0, 0.)));
        assert_eq!(sources_with_labels.next(), Some((1, 1.)));
        assert_eq!(sources_with_labels.next(), Some((2, 2.)));
        assert_eq!(sources_with_labels.next(), None);
    }

    #[test]
    fn bidirectional_query_test() {
        let query = BidirectionalPointToPointQuery::new(0, 1, 0., 1.);
        assert_eq!(query.sources().next(), Some(0));
        assert_eq!(query.target(), Some(1));
        assert_eq!(query.sources_with_labels().next(), Some((0, 0.)));
        let rev_query = query.reverse();
        assert_eq!(rev_query.sources().next(), Some(1));
        assert_eq!(rev_query.target(), Some(0));
        assert_eq!(rev_query.sources_with_labels().next(), Some((1, 1.)));
    }
}
