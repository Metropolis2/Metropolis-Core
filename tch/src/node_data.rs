use hashbrown::HashSet;
use petgraph::graph::NodeIndex;
use ttf::TTF;

pub trait NodeData {
    type Label;
    type Predecessor;
    fn label(&self) -> &Self::Label;
    fn label_mut(&mut self) -> &mut Self::Label;
    fn predecessor(&self) -> Option<&Self::Predecessor>;
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

#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct NodeDataWithExtra<D1, D2> {
    pub data: D1,
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

pub type ScalarData<T> = (T, Option<NodeIndex>);

pub type ScalarDataWithExtra<T> = NodeDataWithExtra<(T, Option<NodeIndex>), Option<T>>;

pub type ProfileIntervalData<T> = ([T; 2], Option<HashSet<NodeIndex>>);

pub type ProfileIntervalDataWithExtra<T> =
    NodeDataWithExtra<([T; 2], Option<HashSet<NodeIndex>>), Option<T>>;

pub type ProfileData<T> = (TTF<T>, Option<HashSet<NodeIndex>>);

pub type ProfileDataWithExtra<T> =
    NodeDataWithExtra<(TTF<T>, Option<HashSet<NodeIndex>>), Option<T>>;
