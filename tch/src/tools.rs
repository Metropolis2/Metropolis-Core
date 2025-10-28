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

//! Structs and functions for the command-line tool.

use std::env;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use hashbrown::{HashMap, HashSet};
use indicatif::{ProgressBar, ProgressStyle};
use log::{info, log_enabled, warn, Level, LevelFilter};
use object_pool::Pool;
use petgraph::graph::EdgeReference;
use petgraph::prelude::EdgeRef;
use petgraph::{
    graph::{edge_index, node_index, EdgeIndex, NodeIndex},
    prelude::DiGraph,
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use serde_with::{serde_as, DurationSecondsWithFrac};
use simplelog::{
    ColorChoice, CombinedLogger, Config, SharedLogger, TermLogger, TerminalMode, WriteLogger,
};
use ttf::TTF;

use crate::algo::{
    earliest_arrival_query, intersect_earliest_arrival_query, intersect_profile_query,
    profile_query,
};
use crate::bidirectional_ops::{BidirectionalProfileDijkstra, BidirectionalTCHEA};
use crate::query::BidirectionalPointToPointQuery;
use crate::HierarchyOverlay;
use crate::{
    ContractionParameters, DefaultBidirectionalProfileSearch, DefaultEarliestArrivalAllocation,
    DefaultTCHProfileAllocation,
};

/// Set of parameters.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct Parameters {
    /// Paths to the input files.
    pub input_files: InputFiles,
    /// Path to the output directory.
    #[serde(default)]
    pub output_directory: PathBuf,
    /// Algorithm type to use for the queries.
    #[serde(default)]
    pub algorithm: AlgorithmType,
    /// Format to use for saving the output files.
    #[serde(default)]
    pub saving_format: SavingFormat,
    /// If `true`, the node ordering is saved in the output directory (only for intersect and tch).
    #[serde(default)]
    pub output_order: bool,
    /// If `true`, the hierarchy overlay is saved in the output directory (only for intersect and
    /// tch).
    #[serde(default)]
    pub output_overlay: bool,
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
    pub contraction: ContractionParameters,
}

/// Struct to store all the input file paths.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct InputFiles {
    /// Path to the file where the queries to compute are stored.
    pub queries: PathBuf,
    /// Path to the file where the graph is stored.
    pub edges: PathBuf,
    /// Path to the file where the graph weights are stored.
    /// If not specified, the weights are read from the graph file (with key "weight").
    #[serde(default)]
    pub edge_ttfs: Option<PathBuf>,
    /// Path to the file where the node ordering is stored (only for intersect and tch).
    /// If not specified, the node ordering is computing automatically.
    #[serde(default)]
    pub input_order: Option<PathBuf>,
}

/// Algorithm type to use for the queries.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
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

/// Format to be used when saving files.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize)]
pub enum SavingFormat {
    /// Zstd-compressed JSON files.
    JSON,
    /// Parquet files.
    #[default]
    Parquet,
    /// CSV files.
    CSV,
}

/// A set of nodes connected through directed edges.
#[derive(Clone, Debug)]
pub struct Graph {
    /// Directed graph where edges' weights are travel-time functions.
    pub graph: DiGraph<(), TTF<f64>>,
    /// Mapping from original node id to simulation NodeIndex.
    pub node_map: HashMap<u64, NodeIndex>,
    /// Mapping from simulation NodeIndex to original node id.
    pub reverse_node_map: HashMap<NodeIndex, u64>,
    /// Mapping from simulation EdgeIndex to original edge id.
    pub reverse_edge_map: HashMap<EdgeIndex, u64>,
}

impl Graph {
    /// Creates a new [Graph] from a Vec of [Edge].
    pub(crate) fn from_edges(raw_edges: Vec<Edge>) -> Self {
        let reverse_edge_map = raw_edges
            .iter()
            .enumerate()
            .map(|(i, e)| (edge_index(i), e.edge_id))
            .collect();
        let node_set: HashSet<_> = raw_edges
            .iter()
            .map(|e| e.source)
            .chain(raw_edges.iter().map(|e| e.target))
            .collect();
        let node_map: HashMap<u64, NodeIndex> = node_set
            .iter()
            .enumerate()
            .map(|(i, &original_id)| (original_id, node_index(i)))
            .collect();
        let reverse_node_map: HashMap<NodeIndex, u64> = node_set
            .into_iter()
            .enumerate()
            .map(|(i, original_id)| (node_index(i), original_id))
            .collect();
        let edges: Vec<_> = raw_edges
            .into_iter()
            .map(|e| (node_map[&e.source], node_map[&e.target], e.travel_time))
            .collect();
        let graph = DiGraph::from_edges(edges);
        Self {
            graph,
            node_map,
            reverse_node_map,
            reverse_edge_map,
        }
    }

    /// Returns the NodeIndex of the node in the graph with the given original id.
    pub fn get_node_id(&self, original_id: u64) -> NodeIndex {
        *self
            .node_map
            .get(&original_id)
            .unwrap_or_else(|| panic!("No node with id {original_id} in the graph"))
    }

    /// Returns the original id of the node in the graph with the given NodeIndex.
    pub fn get_id_of_node(&self, id: NodeIndex) -> u64 {
        *self
            .reverse_node_map
            .get(&id)
            .unwrap_or_else(|| panic!("No node with id {id:?} in the graph"))
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

#[derive(Clone, Debug)]
pub(crate) struct Edge {
    pub(crate) edge_id: u64,
    pub(crate) source: u64,
    pub(crate) target: u64,
    pub(crate) travel_time: TTF<f64>,
}

/// Point-to-point query (earliest-arrival or profile).
#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize)]
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
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(untagged)]
pub enum QueryResult {
    /// Id, arrival time and route (for earliest-arrival queries).
    EarliestArrival((u64, Option<f64>, Option<Vec<u64>>)),
    /// Id and travel-time function (for profile queries).
    Profile((u64, Option<TTF<f64>>)),
}

/// Secondary output on a set of queries.
#[serde_as]
#[derive(Clone, Debug, Serialize)]
pub struct DetailedOutput {
    /// Number of queries run.
    pub nb_queries: usize,
    /// Total time spent for the pre-processing of the graph.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    pub preprocessing_time: Duration,
    /// Total time spent on computing the queries.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    pub query_time: Duration,
    /// Average time spent per query.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    pub query_time_per_query: Duration,
    /// Total time spent on pre-processing and computing queries.
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    pub total_time: Duration,
    /// Average time spent per query (including pre-processing time).
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    pub total_time_per_query: Duration,
}

/// Global output for a set of queries.
#[derive(Clone, Debug, Serialize)]
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

/// Initializes logging to terminal and an optional Writer.
pub fn initialize_logging<W: std::io::Write + Send + 'static>(
    maybe_writer: Option<W>,
) -> Result<()> {
    let mut loggers: Vec<Box<dyn SharedLogger>> = vec![TermLogger::new(
        LevelFilter::Info,
        Config::default(),
        TerminalMode::Mixed,
        ColorChoice::Auto,
    )];
    if let Some(writer) = maybe_writer {
        loggers.push(WriteLogger::new(
            LevelFilter::Info,
            Config::default(),
            writer,
        ));
    }
    CombinedLogger::init(loggers).context("Failed to initialize logging")
}

/// Reads [Parameters] from a filename and runs the corresponding queries.
pub fn run_queries(path: &Path) -> Result<()> {
    run_queries_imp(path, None::<std::io::Empty>)
}

/// Reads [Parameters] from a filename and runs the corresponding queries.
pub fn run_queries_with_writer<W: std::io::Write + Send + 'static>(
    path: &Path,
    writer: W,
) -> Result<()> {
    run_queries_imp(path, Some(writer))
}

fn run_queries_imp<W: std::io::Write + Send + 'static>(
    path: &Path,
    writer: Option<W>,
) -> Result<()> {
    info!("Reading parameters");
    let mut parameters: Parameters = crate::io::get_parameters_from_json(path)?;

    initialize_logging(writer).expect("Failed to initialize logging");

    let t0 = Instant::now();

    // Set the working directory to the directory of the `parameters.json` file so that the input
    // paths can be interpreted as being relative to this file.
    if let Some(parent_dir) = path.parent() {
        if parent_dir.to_str().map(|s| !s.is_empty()).unwrap_or(true) {
            env::set_current_dir(parent_dir)
                .with_context(|| format!("Failed to set working directory to `{parent_dir:?}`"))?;
        }
    }

    info!("Reading graph");
    let graph: Graph = crate::io::get_graph_from_files(
        &parameters.input_files.edges,
        parameters.input_files.edge_ttfs.as_deref(),
    )
    .context("Failed to read graph")?;

    let order: Option<HashMap<u64, usize>> =
        if let Some(filename) = parameters.input_files.input_order {
            info!("Reading node ordering");
            let order = crate::io::get_node_order_from_file(&filename)
                .context("Failed to read node ordering")?;
            Some(order)
        } else {
            None
        };

    info!("Reading queries");
    let queries: Vec<Query> = crate::io::get_queries_from_file(&parameters.input_files.queries)
        .context("Failed to read queries")?;

    if queries.is_empty() {
        warn!("No query to execute");
        return Ok(());
    }

    // Initialize the global rayon thread pool.
    rayon::ThreadPoolBuilder::new()
        .num_threads(parameters.nb_threads)
        .build_global()
        .unwrap();

    if parameters.algorithm == AlgorithmType::Best {
        // Guess the best algorithm to use.
        let nb_unique_sources = queries
            .iter()
            .map(|q| q.source)
            .collect::<HashSet<_>>()
            .len();
        let nb_unique_targets = queries
            .iter()
            .map(|q| q.target)
            .collect::<HashSet<_>>()
            .len();
        let nb_queries = queries.len();
        // TODO: Improve the values using simulation results.
        parameters.algorithm = if nb_queries <= 100 {
            AlgorithmType::Dijkstra
        } else if std::cmp::max(nb_unique_sources, nb_unique_targets) * 50 <= graph.node_count() {
            // Less than 2 % of the nodes are unique source or unique targets.
            AlgorithmType::Intersect
        } else {
            AlgorithmType::Tch
        };
    }

    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(&parameters.output_directory).with_context(|| {
        format!(
            "Failed to create output directory `{:?}`",
            parameters.output_directory
        )
    })?;

    let ttf_func_id = |edge_id: EdgeIndex| -> &TTF<f64> { &graph[edge_id] };
    let ttf_func_edge = |edge: EdgeReference<'_, TTF<f64>>| -> &TTF<f64> { ttf_func_id(edge.id()) };

    let mut results = Vec::with_capacity(queries.len());
    let mut preprocessing_time = Duration::default();
    let query_time;
    if parameters.algorithm == AlgorithmType::Dijkstra {
        info!("Running Dijkstra queries");
        let t1 = Instant::now();
        let pool: Pool<DijkstraAllocation> =
            Pool::new(rayon::current_num_threads(), Default::default);
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(queries.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        queries
            .par_iter()
            .map_init(
                || pool.pull(Default::default),
                |alloc, query| {
                    if let Some(td) = query.departure_time {
                        let bidir_query = BidirectionalPointToPointQuery::new(
                            graph.get_node_id(query.source),
                            graph.get_node_id(query.target),
                            td,
                            Default::default(),
                        );
                        let mut ops =
                            BidirectionalTCHEA::new(&graph.graph, ttf_func_edge, HashMap::new());
                        let result = earliest_arrival_query(
                            &mut alloc.ea_alloc,
                            &bidir_query,
                            &mut ops,
                            &graph.graph,
                            ttf_func_edge,
                        )
                        .unwrap();
                        bp.inc(1);
                        if let Some((ta, route)) = result {
                            if parameters.output_route {
                                // Convert the route from Vec<NodeIndex> to Vec<EdgeIndex>.
                                let mut edge_route = Vec::with_capacity(route.len() - 1);
                                for (&i, &j) in
                                    route[..(route.len() - 1)].iter().zip(route[1..].iter())
                                {
                                    let edge_index = graph
                                        .find_edge(i, j)
                                        .expect("Invalid Dijkstra route output");
                                    edge_route.push(graph.reverse_edge_map[&edge_index]);
                                }
                                QueryResult::EarliestArrival((query.id, Some(ta), Some(edge_route)))
                            } else {
                                QueryResult::EarliestArrival((query.id, Some(ta), None))
                            }
                        } else {
                            QueryResult::EarliestArrival((query.id, None, None))
                        }
                    } else {
                        let mut ops = BidirectionalProfileDijkstra::new(
                            &graph.graph,
                            ttf_func_edge,
                            HashMap::new(),
                        );
                        let bidir_query = BidirectionalPointToPointQuery::from_default(
                            graph.get_node_id(query.source),
                            graph.get_node_id(query.target),
                        );
                        let ttf_opt =
                            profile_query(&mut alloc.profile_search, &bidir_query, &mut ops);
                        bp.inc(1);
                        if let Some(ttf) = ttf_opt {
                            QueryResult::Profile((query.id, Some(ttf)))
                        } else {
                            QueryResult::Profile((query.id, None))
                        }
                    }
                },
            )
            .collect_into_vec(&mut results);
        bp.finish_and_clear();
        query_time = t1.elapsed();
    } else {
        let t1 = Instant::now();
        let overlay = if let Some(order) = order {
            info!("Contracting nodes");
            let node_order_func = |n| {
                *order.get(&graph.get_id_of_node(n)).unwrap_or_else(|| {
                    panic!(
                        "No order was given for node with id {}",
                        graph.get_id_of_node(n)
                    )
                })
            };
            HierarchyOverlay::construct(
                &graph,
                |e| ttf_func_id(e).clone(),
                node_order_func,
                parameters.contraction,
            )
        } else {
            info!("Ordering nodes");
            HierarchyOverlay::order(&graph, |e| ttf_func_id(e).clone(), parameters.contraction)
        };

        if parameters.output_order {
            let order_map: HashMap<u64, usize> = overlay
                .get_order()
                .iter()
                .enumerate()
                .map(|(i, order)| (graph.get_id_of_node(node_index(i)), *order))
                .collect();
            match parameters.saving_format {
                SavingFormat::Parquet => {
                    crate::io::parquet::write_parquet(&order_map, &parameters.output_directory)
                        .context("Failed to write node order")?;
                }
                SavingFormat::CSV => {
                    crate::io::csv::write_csv(&order_map, &parameters.output_directory)
                        .context("Failed to write node order")?;
                }
                SavingFormat::JSON => {
                    crate::io::json::write_json(
                        &order_map,
                        &parameters.output_directory,
                        "node_order",
                    )
                    .context("Failed to write node order")?;
                }
            }
        }

        if parameters.output_overlay {
            crate::io::json::write_json(&overlay, &parameters.output_directory, "overlay")
                .context("Cannot write overlay")?;
        }

        if parameters.algorithm == AlgorithmType::Intersect {
            info!("Computing search spaces");
            let (sources, targets): (HashSet<NodeIndex>, HashSet<NodeIndex>) = queries
                .iter()
                .map(|q| (graph.get_node_id(q.source), graph.get_node_id(q.target)))
                .unzip();
            let search_spaces = overlay.get_search_spaces(&sources, &targets);

            preprocessing_time = t1.elapsed();
            let t2 = Instant::now();

            info!("Running intersect queries");
            let bp = if log_enabled!(Level::Info) {
                ProgressBar::new(queries.len() as u64)
            } else {
                ProgressBar::hidden()
            };
            bp.set_style(
                ProgressStyle::default_bar()
                    .template("{bar:60} ETA: {eta}")
                    .unwrap(),
            );
            queries
                .par_iter()
                .map(|query| {
                    // Unwraping here is safe because we know that the source and target are both in
                    // the search spaces.
                    if let Some(td) = query.departure_time {
                        let ta_opt = intersect_earliest_arrival_query(
                            graph.get_node_id(query.source),
                            graph.get_node_id(query.target),
                            td,
                            &search_spaces,
                        )
                        .unwrap();
                        bp.inc(1);
                        if let Some(ta) = ta_opt {
                            QueryResult::EarliestArrival((query.id, Some(ta), None))
                        } else {
                            QueryResult::EarliestArrival((query.id, None, None))
                        }
                    } else {
                        let ttf_opt = intersect_profile_query(
                            graph.get_node_id(query.source),
                            graph.get_node_id(query.target),
                            &search_spaces,
                        )
                        .unwrap();
                        bp.inc(1);
                        if let Some(ttf) = ttf_opt {
                            QueryResult::Profile((query.id, Some(ttf)))
                        } else {
                            QueryResult::Profile((query.id, None))
                        }
                    }
                })
                .collect_into_vec(&mut results);
            bp.finish_and_clear();
            query_time = t2.elapsed();
        } else {
            preprocessing_time = t1.elapsed();
            let t2 = Instant::now();
            assert_eq!(
                parameters.algorithm,
                AlgorithmType::Tch,
                "Invalid algorithm mode"
            );
            info!("Running TCH queries");
            let pool: Pool<TCHAllocation> =
                Pool::new(rayon::current_num_threads(), Default::default);
            let bp = if log_enabled!(Level::Info) {
                ProgressBar::new(queries.len() as u64)
            } else {
                ProgressBar::hidden()
            };
            bp.set_style(
                ProgressStyle::default_bar()
                    .template("{bar:60} ETA: {eta}")
                    .unwrap(),
            );
            queries
                .par_iter()
                .map_init(
                    || pool.pull(Default::default),
                    |alloc, query| {
                        if let Some(td) = query.departure_time {
                            let (ea_alloc, ea_candidate_map) = alloc.get_ea_variables();
                            let result = overlay
                                .earliest_arrival_query(
                                    graph.get_node_id(query.source),
                                    graph.get_node_id(query.target),
                                    td,
                                    ea_alloc,
                                    ea_candidate_map,
                                )
                                .unwrap();
                            bp.inc(1);
                            if let Some((ta, route)) = result {
                                if parameters.output_route {
                                    let route = route
                                        .into_iter()
                                        .map(|node_idx| graph.reverse_edge_map[&node_idx])
                                        .collect();
                                    QueryResult::EarliestArrival((query.id, Some(ta), Some(route)))
                                } else {
                                    QueryResult::EarliestArrival((query.id, Some(ta), None))
                                }
                            } else {
                                QueryResult::EarliestArrival((query.id, None, None))
                            }
                        } else {
                            let (profile_alloc, profile_candidate_map) =
                                alloc.get_profile_variables();
                            let ttf_opt = overlay.profile_query(
                                graph.get_node_id(query.source),
                                graph.get_node_id(query.target),
                                &mut profile_alloc.interval_search,
                                &mut profile_alloc.profile_search,
                                profile_candidate_map,
                            );
                            bp.inc(1);
                            if let Some(ttf) = ttf_opt {
                                QueryResult::Profile((query.id, Some(ttf)))
                            } else {
                                QueryResult::Profile((query.id, None))
                            }
                        }
                    },
                )
                .collect_into_vec(&mut results);
            bp.finish_and_clear();
            query_time = t2.elapsed();
        }
    };

    let total_time = t0.elapsed();
    let details = DetailedOutput {
        nb_queries: queries.len(),
        preprocessing_time,
        query_time,
        query_time_per_query: query_time / queries.len() as u32,
        total_time,
        total_time_per_query: total_time / queries.len() as u32,
    };

    info!("Saving results");
    match parameters.saving_format {
        SavingFormat::Parquet => {
            crate::io::parquet::write_parquet(&results, &parameters.output_directory)
                .context("Failed to write results")?;
        }
        SavingFormat::CSV => {
            crate::io::csv::write_csv(&results, &parameters.output_directory)
                .context("Failed to write results")?;
        }
        SavingFormat::JSON => {
            crate::io::json::write_json(&results, &parameters.output_directory, "results")
                .context("Failed to write results")?;
        }
    }
    crate::io::json::write_json(details, &parameters.output_directory, "details")
        .context("Failed to write details")?;
    Ok(())
}
