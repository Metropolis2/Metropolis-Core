use hashbrown::HashSet;
use petgraph::graph::NodeIndex;
use serde::{Deserialize, Serialize};
use ttf::TTF;

/// Trait for Structs that can hold node-specific data during a Dijkstra search.
pub trait NodeData {
    /// Type of the label associated to the nodes.
    type Label;
    /// Type of the nodes' predecessor.
    type Predecessor;
    /// Returns a reference to the label of the node.
    fn label(&self) -> &Self::Label;
    /// Returns a mutable reference to the label of the node.
    fn label_mut(&mut self) -> &mut Self::Label;
    /// Returns a reference to the predecessor of the node (if any).
    fn predecessor(&self) -> Option<&Self::Predecessor>;
    /// Returns a mutable reference to the predecessor of the node (if any).
    fn predecessor_mut(&mut self) -> Option<&mut Self::Predecessor>;
}

impl<L, P> NodeData for (L, Option<P>) {
    type Label = L;
    type Predecessor = P;
    fn label(&self) -> &L {
        &self.0
    }
    fn label_mut(&mut self) -> &mut L {
        &mut self.0
    }
    fn predecessor(&self) -> Option<&P> {
        self.1.as_ref()
    }
    fn predecessor_mut(&mut self) -> Option<&mut P> {
        self.1.as_mut()
    }
}

/// A Struct that can store extra data in addition to the standard node's data.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct NodeDataWithExtra<D1, D2> {
    /// The standard node's data.
    pub data: D1,
    /// Extra data.
    pub extra: D2,
}

impl<D1: NodeData, D2> NodeData for NodeDataWithExtra<D1, D2> {
    type Label = D1::Label;
    type Predecessor = D1::Predecessor;
    fn label(&self) -> &Self::Label {
        self.data.label()
    }
    fn label_mut(&mut self) -> &mut Self::Label {
        self.data.label_mut()
    }
    fn predecessor(&self) -> Option<&Self::Predecessor> {
        self.data.predecessor()
    }
    fn predecessor_mut(&mut self) -> Option<&mut Self::Predecessor> {
        self.data.predecessor_mut()
    }
}

/// Type to store a scalar label and a node predecessor.
pub(crate) type ScalarData<T> = (T, Option<NodeIndex>);

/// Type to store a time interval label, and a set of predecessor nodes.
pub(crate) type ProfileIntervalData<T> = ([T; 2], Option<HashSet<NodeIndex>>);

/// Type to store a time interval label, a set of predecessor nodes and an additional time label.
pub(crate) type ProfileIntervalDataWithExtra<T> =
    NodeDataWithExtra<([T; 2], Option<HashSet<NodeIndex>>), Option<T>>;

/// Type to store a TTF label and a set of predecessor nodes.
pub(crate) type ProfileData<T> = (TTF<T>, Option<HashSet<NodeIndex>>);
