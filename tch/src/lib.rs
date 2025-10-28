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

//! Set of algorithms based on Time-Dependent Contraction Hierarchies.
#![doc(html_no_source)]

pub mod algo;
pub mod bidirectional_ops;
mod bidirectional_search;
mod bound;
mod contraction_hierarchies;
// TODO: the io module share many functions with the one in core, they should be merged
pub mod io;
mod min_queue;
mod node_data;
mod node_map;
pub mod ops;
mod preprocessing;
pub mod query;
mod search;
pub mod tools;

pub use bidirectional_search::BidirectionalDijkstraSearch;
pub use contraction_hierarchies::{
    HierarchyDirection, HierarchyEdge, HierarchyEdgeClass, HierarchyOverlay, SearchSpaces,
};
pub use node_map::VecMap;
use petgraph::graph::NodeIndex;
pub use preprocessing::ContractionParameters;
pub use search::DijkstraSearch;
pub use tools::{run_queries, run_queries_with_writer};

/// Baseline allocation for the [EarliestArrivalAllocation](algo::EarliestArrivalAllocation).
pub type DefaultEarliestArrivalAllocation<T> = algo::EarliestArrivalAllocation<
    node_data::ScalarData<T>,
    node_data::ProfileIntervalData<T>,
    node_data::ScalarData<T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
>;

/// Baseline [BidirectionalDijkstraSearch] for TCH interval profile queries.
pub type DefaultBidirectionalIntervalSearch<T> = BidirectionalDijkstraSearch<
    node_data::ProfileIntervalDataWithExtra<T>,
    node_data::ProfileIntervalDataWithExtra<T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
>;

/// Baseline [BidirectionalDijkstraSearch] for the [profile search](algo::profile_query).
pub type DefaultBidirectionalProfileSearch<T> = BidirectionalDijkstraSearch<
    node_data::ProfileData<T>,
    node_data::ProfileData<T>,
    min_queue::MinPQ<NodeIndex, T>,
    min_queue::MinPQ<NodeIndex, T>,
>;

/// Baseline allocation for the TCH profile query.
#[derive(Clone, Debug, Default)]
pub struct DefaultTCHProfileAllocation<T: ttf::TTFNum> {
    /// Allocation for the interval search.
    pub interval_search: DefaultBidirectionalIntervalSearch<T>,
    /// Allocation for the profile search.
    pub profile_search: DefaultBidirectionalProfileSearch<T>,
}

// Dependencies only used in the bins.
use clap as _;
use csv as _;
use serde_json as _;
use simplelog as _;
