//! Set of algorithms based on Time-Dependent Contraction Hierarchies.
#![warn(
    elided_lifetimes_in_paths,
    explicit_outlives_requirements,
    macro_use_extern_crate,
    missing_debug_implementations,
    missing_docs,
    non_ascii_idents,
    noop_method_call,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unused_crate_dependencies,
    unused_extern_crates,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications
)]
#![warn(clippy::all)]

pub mod algo;
pub mod bidirectional_ops;
mod bidirectional_search;
mod bound;
mod contraction_hierarchies;
mod min_queue;
mod node_data;
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

/// Baseline allocation for the [EarliestArrivalAllocation](algo::EarliestArrivalAllocation).
pub type DefaultEarliestArrivalAllocation<T> = algo::EarliestArrivalAllocation<
    node_data::ScalarData<T>,
    node_data::ProfileIntervalData<T>,
    node_data::ScalarData<T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
>;

// Dependencies only used in the bins.
// TODO: Remove them when the bin will no longer be useful.
use bincode as _;
use csv as _;
use geojson as _;
use serde_json as _;
