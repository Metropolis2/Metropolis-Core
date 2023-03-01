// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Result};
use clap::Parser;
use hashbrown::{HashMap, HashSet};
use indicatif::{ProgressBar, ProgressStyle};
use log::{info, log_enabled, warn, Level, LevelFilter};
use object_pool::Pool;
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::EdgeRef;
use rayon::prelude::*;
use simplelog::{ColorChoice, Config, TermLogger, TerminalMode};
use tch::algo::{
    earliest_arrival_query, intersect_earliest_arrival_query, intersect_profile_query,
    profile_query,
};
use tch::bidirectional_ops::{BidirectionalProfileDijkstra, BidirectionalTCHEA};
use tch::query::BidirectionalPointToPointQuery;
use tch::tools::*;
use tch::HierarchyOverlay;
use ttf::TTF;

/// Compute efficiently earliest-arrival or profile queries
#[derive(Parser, Debug)]
#[command(author, version, about, long_about)]
struct Args {
    /// Path to the file where the queries to compute are stored.
    #[arg(long)]
    queries: PathBuf,
    /// Path to the file where the graph is stored.
    #[arg(long)]
    graph: PathBuf,
    /// Path to the file where the graph weights are stored.
    /// If not specified, the weights are read from the graph file (with key "weight").
    #[arg(long)]
    weights: Option<PathBuf>,
    /// Path to the file where the parameters are stored.
    #[arg(long)]
    parameters: Option<PathBuf>,
    /// Path to the file where the output should be stored.
    #[arg(long)]
    output: PathBuf,
    /// Path to the file where the node ordering is stored (only for intersect and tch).
    /// If not specified, the node ordering is computing automatically.
    #[arg(long)]
    input_order: Option<PathBuf>,
    /// Path to the file where the node ordering should be stored (only for intersect and tch).
    /// If not specified, the node ordering is not saved.
    #[arg(long)]
    output_order: Option<PathBuf>,
    /// Path to the file where the hierarchy overlay should be stored (only for intersect and tch).
    /// If not specified, the hierarchy overlay is not saved.
    #[arg(long)]
    output_overlay: Option<PathBuf>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    TermLogger::init(
        LevelFilter::Info,
        Config::default(),
        TerminalMode::Mixed,
        ColorChoice::Auto,
    )
    .expect("Failed to initialize logging");

    let t0 = Instant::now();

    info!("Reading graph");
    let mut bytes = Vec::new();
    File::open(args.graph)
        .expect("Unable to open graph file")
        .read_to_end(&mut bytes)?;
    let mut graph: Graph = serde_json::from_slice(&bytes).expect("Unable to parse graph");

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

    info!("Reading queries");
    let mut bytes = Vec::new();
    File::open(args.queries)
        .expect("Unable to open queries file")
        .read_to_end(&mut bytes)?;
    let queries: Vec<Query> = serde_json::from_slice(&bytes).expect("Unable to parse queries");

    if queries.is_empty() {
        warn!("No query to execute");
        return Ok(());
    }

    let mut parameters: Parameters = if let Some(filename) = args.parameters {
        info!("Reading parameters");
        let mut bytes = Vec::new();
        File::open(filename)
            .expect("Unable to open parameters file")
            .read_to_end(&mut bytes)?;
        serde_json::from_slice(&bytes).expect("Unable to parse parameters")
    } else {
        Default::default()
    };

    // Initialize the global rayon thread pool.
    rayon::ThreadPoolBuilder::new()
        .num_threads(parameters.nb_threads)
        .build_global()
        .unwrap();

    // Check that all sources and targets are in the graph.
    let max_source_id = queries.iter().map(|q| q.source).max().unwrap();
    let max_target_id = queries.iter().map(|q| q.target).max().unwrap();
    if max_source_id.index() >= graph.node_count() || max_target_id.index() >= graph.node_count() {
        let max = std::cmp::max(max_source_id.index(), max_target_id.index());
        return Err(anyhow!(
            "Invalid query found. There is no node with id {}",
            max
        ));
    }

    // Set the weights of the graph from the weights HashMap (if any).
    if let Some(w) = weights {
        for (edge_id, ttf) in w.into_iter() {
            graph[edge_id] = ttf
        }
    }

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
                            query.source,
                            query.target,
                            td,
                            Default::default(),
                        );
                        let mut ops =
                            BidirectionalTCHEA::new(&graph.0, ttf_func_edge, HashMap::new());
                        let result = earliest_arrival_query(
                            &mut alloc.ea_alloc,
                            &bidir_query,
                            &mut ops,
                            &graph.0,
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
                                    edge_route.push(
                                        graph
                                            .find_edge(i, j)
                                            .expect("Invalid Dijkstra route output"),
                                    );
                                }
                                QueryResult::ArrivalTimeAndRoute((query.id, ta, edge_route))
                            } else {
                                QueryResult::ArrivalTime((query.id, ta))
                            }
                        } else {
                            QueryResult::NotConnected
                        }
                    } else {
                        let mut ops = BidirectionalProfileDijkstra::new(
                            &graph.0,
                            ttf_func_edge,
                            HashMap::new(),
                        );
                        let bidir_query = BidirectionalPointToPointQuery::from_default(
                            query.source,
                            query.target,
                        );
                        let ttf_opt =
                            profile_query(&mut alloc.profile_search, &bidir_query, &mut ops);
                        bp.inc(1);
                        if let Some(ttf) = ttf_opt {
                            QueryResult::TravelTimeFunction((query.id, ttf))
                        } else {
                            QueryResult::NotConnected
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

        if parameters.algorithm == AlgorithmType::Intersect {
            info!("Computing search spaces");
            let (sources, targets): (HashSet<NodeIndex>, HashSet<NodeIndex>) =
                queries.iter().map(|q| (q.source, q.target)).unzip();
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
                            query.source,
                            query.target,
                            td,
                            &search_spaces,
                        )
                        .unwrap();
                        bp.inc(1);
                        if let Some(ta) = ta_opt {
                            QueryResult::ArrivalTime((query.id, ta))
                        } else {
                            QueryResult::NotConnected
                        }
                    } else {
                        let ttf_opt =
                            intersect_profile_query(query.source, query.target, &search_spaces)
                                .unwrap();
                        bp.inc(1);
                        if let Some(ttf) = ttf_opt {
                            QueryResult::TravelTimeFunction((query.id, ttf))
                        } else {
                            QueryResult::NotConnected
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
                                    query.source,
                                    query.target,
                                    td,
                                    ea_alloc,
                                    ea_candidate_map,
                                )
                                .unwrap();
                            bp.inc(1);
                            if let Some((ta, route)) = result {
                                if parameters.output_route {
                                    QueryResult::ArrivalTimeAndRoute((query.id, ta, route))
                                } else {
                                    QueryResult::ArrivalTime((query.id, ta))
                                }
                            } else {
                                QueryResult::NotConnected
                            }
                        } else {
                            let (profile_alloc, profile_candidate_map) =
                                alloc.get_profile_variables();
                            let ttf_opt = overlay.profile_query(
                                query.source,
                                query.target,
                                &mut profile_alloc.interval_search,
                                &mut profile_alloc.profile_search,
                                profile_candidate_map,
                            );
                            bp.inc(1);
                            if let Some(ttf) = ttf_opt {
                                QueryResult::TravelTimeFunction((query.id, ttf))
                            } else {
                                QueryResult::NotConnected
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
    let output = Output { details, results };

    info!("Saving results");
    let mut writer = File::create(args.output).unwrap();
    writer
        .write_all(&serde_json::to_vec(&output).unwrap())
        .unwrap();
    Ok(())
}
