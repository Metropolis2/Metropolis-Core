// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs and functions for the command-line tool.

use std::{
    ops::{Deref, DerefMut},
    time::Duration,
};

use hashbrown::HashMap;
use petgraph::{
    graph::{EdgeIndex, NodeIndex},
    prelude::DiGraph,
};
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize};
use serde_with::{serde_as, DurationSecondsWithFrac};
use ttf::{TTFSimplification, TTF};

use crate::{
    ContractionParameters, DefaultBidirectionalProfileSearch, DefaultEarliestArrivalAllocation,
    DefaultTCHProfileAllocation,
};

/// Set of parameters.
#[derive(Clone, Debug, Default, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Parameters")]
#[schemars(description = "Set of parameters.")]
pub struct Parameters<T> {
    /// Algorithm type to use for the queries.
    #[serde(default)]
    pub algorithm: AlgorithmType,
    /// If `true`, the routes corresponding to the earliest-arrival queries are exported.
    #[serde(default)]
    pub output_route: bool,
    /// Number of threads to use to parallelize queries.
    ///
    /// Default (0) is to use all the threads of the CPU.
    #[serde(default)]
    pub nb_threads: usize,
    /// [ContractionParameters] controlling how a [HierarchyOverlay] is built from a [RoadNetwork].
    #[serde(default)]
    #[schemars(
        description = "Parameters controlling how a hierarchy overlay is built from a road network graph."
    )]
    pub contraction: ContractionParameters,
    /// [TTFSimplification] describing how the edges' TTFs are simplified before doing anything.
    #[serde(default = "TTFSimplification::<T>::default")]
    #[schemars(description = "How to simplify the edges TTFs before doing anyting else.")]
    pub weight_simplification: TTFSimplification<T>,
    /// [TTFSimplification] describing how the edges' TTFs are simplified after the
    /// HierarchyOverlay is built.
    #[serde(default = "TTFSimplification::<T>::default")]
    #[schemars(
        description = "How to simplify the edges TTFs after the hierarchy overlay is built."
    )]
    pub overlay_simplification: TTFSimplification<T>,
    /// [TTFSimplification] describing how the TTFs of the forward and backward search spaces
    /// are simplified.
    #[serde(default = "TTFSimplification::<T>::default")]
    #[schemars(
        description = "How to simplify the TTFs of the forward and backward search spaces."
    )]
    pub search_space_simplification: TTFSimplification<T>,
    /// [TTFSimplification] describing how the TTFs resuling from the queries are simplified.
    #[serde(default = "TTFSimplification::<T>::default")]
    #[schemars(description = "How to simplify the TTFs resulting from the queries.")]
    pub result_simplification: TTFSimplification<T>,
}

/// Algorithm type to use for the queries.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub enum AlgorithmType {
    /// Try to guess which algorithm will be the fastest.
    #[default]
    Best,
    /// Dijkstra algorithm: no pre-processing, slow queries.
    Dijkstra,
    /// Time-dependent contraction hierarchies (TCH): long pre-processing time, fast queries.
    #[serde(rename = "TCH")]
    Tch,
    /// Many-to-many TCH: Longest pre-processing time, fastest queries.
    Intersect,
}

/// Map that yields the travel-time function for any edge.
pub type Weights = HashMap<EdgeIndex, TTF<f64>>;

const fn one() -> TTF<f64> {
    TTF::Constant(1.0)
}

/// A set of nodes connected through directed edges.
#[derive(Clone, Debug, JsonSchema)]
pub struct Graph(#[schemars(with = "DeserGraph")] pub DiGraph<(), TTF<f64>>);

impl Deref for Graph {
    type Target = DiGraph<(), TTF<f64>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Graph {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'de> Deserialize<'de> for Graph {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let deser_graph = DeserGraph::deserialize(deserializer)?;
        let graph = DiGraph::from_edges(
            deser_graph
                .edges
                .into_iter()
                .map(|e| (e.source, e.target, e.weight)),
        );
        Ok(Graph(graph))
    }
}

#[derive(Deserialize, JsonSchema)]
#[serde(rename = "Graph")]
#[serde(transparent)]
pub(crate) struct DeserGraph {
    /// Edges of the graph, represented as a tuple `(s, t, e)`, where `s` is the id of the source
    /// node, `t` is the id of the target node and `e` is the description of the edge.
    #[validate(length(min = 1))]
    edges: Vec<Edge>,
}

#[derive(Clone, Debug, Deserialize, JsonSchema)]
struct Edge {
    source: u32,
    target: u32,
    #[serde(default = "one")]
    weight: TTF<f64>,
}

/// Point-to-point query (earliest-arrival or profile).
#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize, JsonSchema)]
pub struct Query {
    /// Index of the query.
    pub id: u64,
    /// Index of the source node.
    #[schemars(with = "usize")]
    pub source: NodeIndex,
    /// Index of the target node.
    #[schemars(with = "usize")]
    pub target: NodeIndex,
    /// Departure time from source of the query (if not specified, the query is a profile query).
    #[serde(default)]
    pub departure_time: Option<f64>,
}

/// Result of a query.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(untagged)]
pub enum QueryResult {
    /// Id and rrival time (for earliest-arrival queries).
    ArrivalTime((u64, f64)),
    /// Id, arrival time and route (for earliest-arrival queries).
    #[schemars(with = "(f64, Vec<usize>)")]
    ArrivalTimeAndRoute((u64, f64, Vec<EdgeIndex>)),
    /// Id and travel-time function (for profile queries).
    TravelTimeFunction((u64, TTF<f64>)),
    /// The source and target are not connected.
    NotConnected,
}

/// Secondary output on a set of queries.
#[serde_as]
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct DetailedOutput {
    /// Number of queries run.
    pub nb_queries: usize,
    /// Total time spent for the pre-processing of the graph.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    #[schemars(with = "f64")]
    pub preprocessing_time: Duration,
    /// Total time spent on computing the queries.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    #[schemars(with = "f64")]
    pub query_time: Duration,
    /// Average time spent per query.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    #[schemars(with = "f64")]
    pub query_time_per_query: Duration,
    /// Total time spent on pre-processing and computing queries.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    #[schemars(with = "f64")]
    pub total_time: Duration,
    /// Average time spent per query (including pre-processing time).
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    #[schemars(with = "f64")]
    pub total_time_per_query: Duration,
}

/// Global output for a set of queries.
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct Output {
    /// Secondary results.
    pub details: DetailedOutput,
    /// Query results.
    pub results: Vec<QueryResult>,
}

/// Memory allocation to use for a Dijkstra run.
#[derive(Clone, Debug, Default)]
pub struct DijkstraAllocation {
    /// Memory allocation for an earliest-arrival query.
    pub ea_alloc: DefaultEarliestArrivalAllocation<f64>,
    /// Memory allocation for a profile query.
    pub profile_search: DefaultBidirectionalProfileSearch<f64>,
}

/// Memory allocation to use for a TCH query (earliest arrival or profile).
#[derive(Clone, Debug, Default)]
pub struct TCHAllocation {
    ea_alloc: DefaultEarliestArrivalAllocation<f64>,
    ea_candidate_map: HashMap<NodeIndex, (f64, f64)>,
    profile_alloc: DefaultTCHProfileAllocation<f64>,
    profile_candidate_map: HashMap<NodeIndex, f64>,
}

impl TCHAllocation {
    /// Returns the memory allocation for a TCHEA query.
    pub fn get_ea_variables(
        &mut self,
    ) -> (
        &mut DefaultEarliestArrivalAllocation<f64>,
        &mut HashMap<NodeIndex, (f64, f64)>,
    ) {
        (&mut self.ea_alloc, &mut self.ea_candidate_map)
    }

    /// Returns the memory allocation for a TCH profile query.
    pub fn get_profile_variables(
        &mut self,
    ) -> (
        &mut DefaultTCHProfileAllocation<f64>,
        &mut HashMap<NodeIndex, f64>,
    ) {
        (&mut self.profile_alloc, &mut self.profile_candidate_map)
    }
}
