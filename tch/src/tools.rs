// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs and functions for the command-line tool.

use std::{
    fs::File,
    io::{Read, Write},
    ops::{Deref, DerefMut},
    path::{Path, PathBuf},
    time::Duration,
};

use anyhow::{Context, Result};
use hashbrown::HashMap;
use petgraph::{
    graph::{node_index, EdgeIndex, NodeIndex},
    prelude::DiGraph,
};
use schemars::JsonSchema;
use serde::{de::DeserializeOwned, Deserialize, Deserializer, Serialize};
use serde_with::{serde_as, DurationSecondsWithFrac};
use ttf::TTF;

use crate::{
    ContractionParameters, DefaultBidirectionalProfileSearch, DefaultEarliestArrivalAllocation,
    DefaultTCHProfileAllocation,
};

/// Set of parameters.
#[derive(Clone, Debug, Default, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Parameters")]
#[schemars(description = "Set of parameters.")]
pub struct Parameters {
    /// Paths to the input files.
    pub input_files: InputFiles,
    /// Path to the file where the query results should be stored.
    /// Default is "output.csv" or "output.parquet".
    #[serde(default)]
    pub output_file: Option<PathBuf>,
    /// Path to the file where the node ordering should be stored (only for intersect and tch).
    /// If not specified, the node ordering is not saved.
    #[serde(default)]
    pub output_order: Option<PathBuf>,
    /// Path to the file where the hierarchy overlay should be stored (only for intersect and tch).
    /// If not specified, the hierarchy overlay is not saved.
    #[serde(default)]
    pub output_overlay: Option<PathBuf>,
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
    /// Format to use for saving the output files.
    #[serde(default)]
    pub saving_format: SavingFormat,
    /// [ContractionParameters] controlling how a [HierarchyOverlay] is built from a [RoadNetwork].
    #[serde(default)]
    #[schemars(
        description = "Parameters controlling how a hierarchy overlay is built from a road network graph."
    )]
    pub contraction: ContractionParameters,
}

/// Struct to store all the input file paths.
#[derive(Clone, Debug, Default, Deserialize, Serialize, JsonSchema)]
pub struct InputFiles {
    /// Path to the file where the queries to compute are stored.
    pub queries: PathBuf,
    /// Path to the file where the graph is stored.
    pub graph: PathBuf,
    /// Path to the file where the graph weights are stored.
    /// If not specified, the weights are read from the graph file (with key "weight").
    #[serde(default)]
    pub weights: Option<PathBuf>,
    /// Path to the file where the node ordering is stored (only for intersect and tch).
    /// If not specified, the node ordering is computing automatically.
    #[serde(default)]
    pub input_order: Option<PathBuf>,
}

/// Format to be used when saving files.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize, JsonSchema)]
pub enum SavingFormat {
    /// Parquet files.
    #[default]
    Parquet,
    /// CSV files.
    CSV,
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
#[derive(Clone, Debug)]
pub struct Graph {
    /// Directed graph where edges' weights are travel-time functions.
    pub graph: DiGraph<(), TTF<f64>>,
    /// Mapping from original node id to simulation NodeIndex.
    pub node_map: HashMap<u64, NodeIndex>,
}

impl Graph {
    /// Returns the NodeIndex of the node in the graph with the given original id.
    pub fn get_node_id(&self, original_id: u64) -> NodeIndex {
        *self
            .node_map
            .get(&original_id)
            .unwrap_or_else(|| panic!("No node with id {original_id} in the graph"))
    }
}

impl Deref for Graph {
    type Target = DiGraph<(), TTF<f64>>;
    fn deref(&self) -> &Self::Target {
        &self.graph
    }
}

impl DerefMut for Graph {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.graph
    }
}

impl<'de> Deserialize<'de> for Graph {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let deser_graph = DeserGraph::deserialize(deserializer)?;
        // The nodes in the DiGraph need to be ordered from 0 to n-1 so we create a map u32 ->
        // NodeIndex to re-index the nodes.
        let node_map: HashMap<u64, NodeIndex> = deser_graph
            .edges
            .iter()
            .map(|e| e.source)
            .chain(deser_graph.edges.iter().map(|e| e.target))
            .enumerate()
            .map(|(idx, id)| (id, node_index(idx)))
            .collect();
        let edges: Vec<_> = deser_graph
            .edges
            .into_iter()
            .map(|e| (node_map[&e.source], node_map[&e.target], e.weight))
            .collect();
        let graph = DiGraph::from_edges(edges);
        Ok(Graph { graph, node_map })
    }
}

/// Variant of [Graph] used for deserialization.
#[derive(Clone, Debug, Deserialize, JsonSchema)]
#[serde(rename = "Graph")]
#[serde(transparent)]
pub struct DeserGraph {
    /// Edges of the graph, represented as a tuple `(s, t, e)`, where `s` is the id of the source
    /// node, `t` is the id of the target node and `e` is the description of the edge.
    #[validate(length(min = 1))]
    edges: Vec<Edge>,
}

#[derive(Clone, Debug, Deserialize, JsonSchema)]
struct Edge {
    source: u64,
    target: u64,
    #[serde(default = "one")]
    weight: TTF<f64>,
}

/// Point-to-point query (earliest-arrival or profile).
#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize, JsonSchema)]
pub struct Query {
    /// Index of the query.
    pub id: u64,
    /// Index of the source node.
    pub source: u64,
    /// Index of the target node.
    pub target: u64,
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

// TODO: the functions below are shared with metropolis-core so they would be best in a dedicated
// crate.
/// Read some deserializable data from an uncompressed or a zstd-compressed JSON file.
pub fn read_json<D: DeserializeOwned>(filename: &Path) -> Result<D> {
    let mut bytes = Vec::new();
    File::open(filename)
        .with_context(|| format!("Unable to open file `{filename:?}`"))?
        .read_to_end(&mut bytes)
        .with_context(|| format!("Unable to read file `{filename:?}`"))?;
    let data = serde_json::from_slice(&bytes)
        .with_context(|| format!("Unable to parse file `{filename:?}`"))?;
    Ok(data)
}

/// Write some serializable data as an uncompressed JSON file.
///
/// The file is stored in the given directory, with filename "{name}.json".
pub fn write_json<D: Serialize>(data: D, filename: &Path) -> Result<()> {
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&data)?;
    writer.write_all(&buffer)?;
    Ok(())
}
