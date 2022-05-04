#[cfg(feature = "serde-1")]
#[macro_use]
extern crate serde_derive;

pub mod algo;
pub mod bidirectional_ops;
mod bidirectional_search;
mod bound;
mod contraction_hierarchies;
mod min_queue;
pub mod node_data;
mod node_map;
pub mod ops;
mod preprocessing;
pub mod query;
mod search;

pub use bidirectional_search::BidirectionalDijkstraSearch;
pub use contraction_hierarchies::{
    HierarchyDirection, HierarchyEdge, HierarchyEdgeClass, HierarchyOverlay, SearchSpaces,
};
pub use node_map::VecMap;
pub use preprocessing::ContractionParameters;
pub use search::DijkstraSearch;

use petgraph::graph::NodeIndex;

pub type DefaultEarliestArrivalAllocation<T> = algo::EarliestArrivalAllocation<
    node_data::ScalarData<T>,
    node_data::ProfileIntervalData<T>,
    node_data::ScalarData<T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
>;
