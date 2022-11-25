// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Result};
use clap::{Parser, ValueEnum};
use either::Either;
use env_logger::Env;
use hashbrown::{HashMap, HashSet};
use indicatif::{ProgressBar, ProgressStyle};
use log::{info, log_enabled, warn, Level};
use object_pool::Pool;
use petgraph::graph::{DiGraph, EdgeIndex, EdgeReference, NodeIndex};
use petgraph::visit::EdgeRef;
use rayon::prelude::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use serde_with::{serde_as, DurationSecondsWithFrac};
use tch::algo::{
    earliest_arrival_query, intersect_earliest_arrival_query, intersect_profile_query,
    profile_query,
};
use tch::bidirectional_ops::{BidirectionalProfileDijkstra, BidirectionalTCHEA};
use tch::query::BidirectionalPointToPointQuery;
use tch::{
    ContractionParameters, DefaultBidirectionalProfileSearch, DefaultEarliestArrivalAllocation,
    DefaultTCHProfileAllocation, HierarchyOverlay,
};
use ttf::{TTFSimplification, TTF};

/// Compute (potentially) time-dependent travel times for a set of source-target pairs.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Which algorithm to use
    #[clap(value_enum, value_parser)]
    algorithm: Algorithm,
    /// Path to the file where the source-target pairs are stored.
    #[clap(long)]
    pairs: PathBuf,
    /// Path to the file where the graph is stored.
    #[clap(long)]
    graph: PathBuf,
    /// Path to the file where the graph weights are stored.
    /// If not specified, the weights are read from the graph file (with key "weight").
    #[clap(long)]
    weights: Option<PathBuf>,
    /// Path to the file where the parameters are stored.
    #[clap(long)]
    parameters: Option<PathBuf>,
    /// Path to the file where the results of the queries should be stored.
    #[clap(long)]
    output: PathBuf,
    /// Path to the file where the node ordering is stored (only for intersect and tch).
    /// If not specified, the node ordering is computing automatically.
    #[clap(long)]
    input_order: Option<PathBuf>,
    /// Path to the file where the node ordering should be stored (only for intersect and tch).
    /// If not specified, the node ordering is not saved.
    #[clap(long)]
    output_order: Option<PathBuf>,
    /// Path to the file where the hierarchy overlay should be stored (only for intersect and tch).
    /// If not specified, the hierarchy overlay is not saved.
    #[clap(long)]
    output_overlay: Option<PathBuf>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum)]
enum Algorithm {
    /// Many-to-many TCH: Longest pre-processing time, fastest queries.
    Intersect,
    /// Time-dependent contraction hierarchies (TCH): long pre-processing time, fast queries.
    Tch,
    /// Dijkstra algorithm: no pre-processing, slow queries.
    Dijkstra,
}

/// Set of parameters.
#[derive(Clone, Debug, Default, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Parameters")]
#[schemars(description = "Set of parameters.")]
struct Parameters<T> {
    /// [ContractionParameters] controlling how a [HierarchyOverlay] is built from a [RoadNetwork].
    #[serde(default)]
    #[schemars(
        description = "Parameters controlling how a hierarchy overlay is built from a road network graph."
    )]
    pub contraction: ContractionParameters,
    /// [TTFSimplification] describing how the edges' TTFs are simplified after the
    /// HierarchyOverlay is built.
    #[serde(default = "TTFSimplification::<T>::default")]
    #[schemars(
        description = "How to simplify the edges TTFs after the hierarchy overlay is built."
    )]
    pub edge_simplification: TTFSimplification<T>,
    /// [TTFSimplification] describing how the TTFs of the forward and backward search spaces
    /// are simplified.
    #[serde(default = "TTFSimplification::<T>::default")]
    #[schemars(
        description = "How to simplify the TTFs of the forward and backward search spaces."
    )]
    pub search_space_simplification: TTFSimplification<T>,
    /// [TTFSimplification] describing how the TTFs resuling from the queries are simplified.
    /// beginning of the iteration.
    #[serde(default = "TTFSimplification::<T>::default")]
    #[schemars(description = "How to simplify the TTFs resulting from the queries.")]
    pub result_simplification: TTFSimplification<T>,
}

type Weights = HashMap<EdgeIndex, TTF<f64>>;

#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize)]
struct Node {}

const fn infinite_travel_time() -> TTF<f64> {
    TTF::Constant(f64::INFINITY)
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
struct Edge {
    #[serde(default = "infinite_travel_time")]
    weight: TTF<f64>,
}

#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize)]
struct ODPair {
    source: NodeIndex,
    target: NodeIndex,
    #[serde(default)]
    departure_time: Option<f64>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(transparent)]
struct QueryResult {
    #[serde(with = "either::serde_untagged")]
    inner: Either<Option<f64>, Option<TTF<f64>>>,
}

#[serde_as]
#[derive(Clone, Debug, Deserialize, Serialize)]
struct DetailedOutput {
    nb_queries: usize,
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    preprocessing_time: Duration,
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    query_time: Duration,
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    query_time_per_query: Duration,
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    total_time: Duration,
    #[serde_as(as = "DurationSecondsWithFrac<f64>")]
    total_time_per_query: Duration,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct Output {
    details: DetailedOutput,
    results: Vec<QueryResult>,
}

#[derive(Clone, Debug, Default)]
struct DijkstraAllocation {
    ea_alloc: DefaultEarliestArrivalAllocation<f64>,
    profile_search: DefaultBidirectionalProfileSearch<f64>,
}

#[derive(Clone, Debug, Default)]
struct TCHAllocation {
    ea_alloc: DefaultEarliestArrivalAllocation<f64>,
    ea_candidate_map: HashMap<NodeIndex, (f64, f64)>,
    profile_alloc: DefaultTCHProfileAllocation<f64>,
    profile_candidate_map: HashMap<NodeIndex, f64>,
}

impl TCHAllocation {
    fn get_ea_variables(
        &mut self,
    ) -> (
        &mut DefaultEarliestArrivalAllocation<f64>,
        &mut HashMap<NodeIndex, (f64, f64)>,
    ) {
        (&mut self.ea_alloc, &mut self.ea_candidate_map)
    }

    fn get_profile_variables(
        &mut self,
    ) -> (
        &mut DefaultTCHProfileAllocation<f64>,
        &mut HashMap<NodeIndex, f64>,
    ) {
        (&mut self.profile_alloc, &mut self.profile_candidate_map)
    }
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Default log level is _info_.
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let t0 = Instant::now();

    info!("Reading graph");
    let mut bytes = Vec::new();
    File::open(args.graph)
        .expect("Unable to open graph file")
        .read_to_end(&mut bytes)?;
    let graph: DiGraph<Node, Edge> = serde_json::from_slice(&bytes).expect("Unable to parse graph");

    let weights: Option<Weights> = if let Some(filename) = args.weights {
        info!("Reading graph weights");
        let mut bytes = Vec::new();
        File::open(filename)
            .expect("Unable to open graph weights file")
            .read_to_end(&mut bytes)?;
        Some(serde_json::from_slice(&bytes).expect("Unable to parse graph weights"))
    } else {
        None
    };

    let order: Option<Vec<usize>> = if let Some(filename) = args.input_order {
        info!("Reading node ordering");
        let mut bytes = Vec::new();
        File::open(filename)
            .expect("Unable to open node ordering file")
            .read_to_end(&mut bytes)?;
        Some(serde_json::from_slice(&bytes).expect("Unable to parse node ordering"))
    } else {
        None
    };

    info!("Reading source-target pairs");
    let mut bytes = Vec::new();
    File::open(args.pairs)
        .expect("Unable to open source-target pairs file")
        .read_to_end(&mut bytes)?;
    let pairs: Vec<ODPair> =
        serde_json::from_slice(&bytes).expect("Unable to parse source-target pairs");

    if pairs.is_empty() {
        warn!("No query to execute");
        return Ok(());
    }

    let parameters: Parameters<f64> = if let Some(filename) = args.parameters {
        info!("Reading parameters");
        let mut bytes = Vec::new();
        File::open(filename)
            .expect("Unable to open parameters file")
            .read_to_end(&mut bytes)?;
        serde_json::from_slice(&bytes).expect("Unable to parse parameters")
    } else {
        Default::default()
    };

    // Check that all sources and targets are in the graph.
    let max_source_id = pairs.iter().map(|p| p.source).max().unwrap();
    let max_target_id = pairs.iter().map(|p| p.target).max().unwrap();
    if max_source_id.index() >= graph.node_count() || max_target_id.index() >= graph.node_count() {
        return Err(anyhow!("Invalid query found. The source or target id is larger than the number of nodes in the graph."));
    }

    let ttf_func_id = |edge_id| {
        if let Some(w) = &weights {
            w.get(&edge_id)
                .unwrap_or_else(|| panic!("No weight for edge id {}", edge_id.index()))
        } else {
            &graph[edge_id].weight
        }
    };
    let ttf_func_edge = |edge: EdgeReference<'_, Edge>| ttf_func_id(edge.id());

    // TODO: Choose best algorithm automatically.
    let mut results = Vec::with_capacity(pairs.len());
    let mut preprocessing_time = Duration::default();
    let query_time;
    if args.algorithm == Algorithm::Dijkstra {
        info!("Running Dijkstra queries");
        let t1 = Instant::now();
        let pool: Pool<DijkstraAllocation> =
            Pool::new(rayon::current_num_threads(), Default::default);
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(pairs.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        pairs
            .par_iter()
            .map_init(
                || pool.pull(Default::default),
                |alloc, pair| {
                    if let Some(td) = pair.departure_time {
                        let query = BidirectionalPointToPointQuery::new(
                            pair.source,
                            pair.target,
                            td,
                            Default::default(),
                        );
                        let mut ops =
                            BidirectionalTCHEA::new(&graph, ttf_func_edge, HashMap::new());
                        let result = earliest_arrival_query(
                            &mut alloc.ea_alloc,
                            &query,
                            &mut ops,
                            &graph,
                            ttf_func_edge,
                        )
                        .unwrap();
                        bp.inc(1);
                        QueryResult {
                            inner: Either::Left(result.map(|r| r.0)),
                        }
                    } else {
                        let mut ops = BidirectionalProfileDijkstra::new(
                            &graph,
                            ttf_func_edge,
                            HashMap::new(),
                        );
                        let query =
                            BidirectionalPointToPointQuery::from_default(pair.source, pair.target);
                        let mut ttf_opt =
                            profile_query(&mut alloc.profile_search, &query, &mut ops);
                        if let Some(ref mut ttf) = &mut ttf_opt {
                            parameters.result_simplification.simplify(ttf);
                        }
                        bp.inc(1);
                        QueryResult {
                            inner: Either::Right(ttf_opt),
                        }
                    }
                },
            )
            .collect_into_vec(&mut results);
        bp.finish_and_clear();
        query_time = t1.elapsed();
    } else {
        let t1 = Instant::now();
        let mut overlay = if let Some(order) = order {
            info!("Contracting nodes");
            HierarchyOverlay::construct(
                &graph,
                |e| ttf_func_id(e).clone(),
                |n| order[n.index()],
                parameters.contraction,
            )
        } else {
            info!("Ordering nodes");
            HierarchyOverlay::order(&graph, |e| ttf_func_id(e).clone(), parameters.contraction)
        };

        if let Some(filename) = args.output_order {
            let mut writer = File::create(filename).unwrap();
            writer
                .write_all(&serde_json::to_vec(&overlay.get_order()).unwrap())
                .unwrap();
        }

        if let Some(filename) = args.output_overlay {
            let mut writer = File::create(filename).unwrap();
            writer
                .write_all(&serde_json::to_vec(&overlay).unwrap())
                .unwrap();
        }

        info!("Simplifying hierarchy overlay");
        overlay.simplify(parameters.edge_simplification);

        if args.algorithm == Algorithm::Intersect {
            info!("Computing search spaces");
            let (sources, targets): (HashSet<NodeIndex>, HashSet<NodeIndex>) =
                pairs.iter().map(|p| (p.source, p.target)).unzip();
            let mut search_spaces = overlay.get_search_spaces(&sources, &targets);

            info!("Simplifying search spaces");
            search_spaces.simplify(parameters.search_space_simplification);

            preprocessing_time = t1.elapsed();
            let t2 = Instant::now();

            info!("Running intersect queries");
            let bp = if log_enabled!(Level::Info) {
                ProgressBar::new(pairs.len() as u64)
            } else {
                ProgressBar::hidden()
            };
            bp.set_style(
                ProgressStyle::default_bar()
                    .template("{bar:60} ETA: {eta}")
                    .unwrap(),
            );
            pairs
                .par_iter()
                .map(|pair| {
                    // Unwraping here is safe because we know that the source and target are both in the
                    // search spaces.
                    if let Some(td) = pair.departure_time {
                        let ta = intersect_earliest_arrival_query(
                            pair.source,
                            pair.target,
                            td,
                            &search_spaces,
                        )
                        .unwrap();
                        bp.inc(1);
                        QueryResult {
                            inner: Either::Left(ta),
                        }
                    } else {
                        let mut ttf_opt =
                            intersect_profile_query(pair.source, pair.target, &search_spaces)
                                .unwrap();
                        if let Some(ref mut ttf) = &mut ttf_opt {
                            parameters.result_simplification.simplify(ttf);
                        }
                        bp.inc(1);
                        QueryResult {
                            inner: Either::Right(ttf_opt),
                        }
                    }
                })
                .collect_into_vec(&mut results);
            bp.finish_and_clear();
            query_time = t2.elapsed();
        } else {
            preprocessing_time = t1.elapsed();
            let t2 = Instant::now();
            assert_eq!(args.algorithm, Algorithm::Tch, "Invalid algorithm mode");
            info!("Running TCH queries");
            let pool: Pool<TCHAllocation> =
                Pool::new(rayon::current_num_threads(), Default::default);
            let bp = if log_enabled!(Level::Info) {
                ProgressBar::new(pairs.len() as u64)
            } else {
                ProgressBar::hidden()
            };
            bp.set_style(
                ProgressStyle::default_bar()
                    .template("{bar:60} ETA: {eta}")
                    .unwrap(),
            );
            pairs
                .par_iter()
                .map_init(
                    || pool.pull(Default::default),
                    |alloc, pair| {
                        if let Some(td) = pair.departure_time {
                            let (ea_alloc, ea_candidate_map) = alloc.get_ea_variables();
                            let result = overlay
                                .earliest_arrival_query(
                                    pair.source,
                                    pair.target,
                                    td,
                                    ea_alloc,
                                    ea_candidate_map,
                                )
                                .unwrap();
                            bp.inc(1);
                            QueryResult {
                                inner: Either::Left(result.map(|r| r.0)),
                            }
                        } else {
                            let (profile_alloc, profile_candidate_map) =
                                alloc.get_profile_variables();
                            let mut ttf_opt = overlay.profile_query(
                                pair.source,
                                pair.target,
                                &mut profile_alloc.interval_search,
                                &mut profile_alloc.profile_search,
                                profile_candidate_map,
                            );
                            if let Some(ref mut ttf) = &mut ttf_opt {
                                parameters.result_simplification.simplify(ttf);
                            }
                            bp.inc(1);
                            QueryResult {
                                inner: Either::Right(ttf_opt),
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
        nb_queries: pairs.len(),
        preprocessing_time,
        query_time,
        query_time_per_query: query_time / pairs.len() as u32,
        total_time,
        total_time_per_query: total_time / pairs.len() as u32,
    };
    let output = Output { details, results };

    info!("Saving results");
    let mut writer = File::create(args.output).unwrap();
    writer
        .write_all(&serde_json::to_vec(&output).unwrap())
        .unwrap();
    Ok(())
}
