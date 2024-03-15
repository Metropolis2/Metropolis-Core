// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Binary to compute earliest-arrival or profile queries from input files.
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
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

/// Compute earliest-arrival or profile queries using time-dependent Contraction Hierarchies
#[derive(Parser, Debug)]
#[command(author, version, about, long_about)]
struct Args {
    /// Path to the JSON file with the parameters
    #[arg(required = true)]
    parameters: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    compute_travel_times(&args.parameters)
}

fn compute_travel_times(path: &Path) -> Result<()> {
    // TODO: Allow logging to file / GUI.
    TermLogger::init(
        LevelFilter::Info,
        Config::default(),
        TerminalMode::Mixed,
        ColorChoice::Auto,
    )
    .expect("Failed to initialize logging");

    let t0 = Instant::now();

    info!("Reading parameters");
    let mut parameters: Parameters = read_json(path).context("Failed to read parameters")?;

    info!("Reading graph");
    let mut graph: Graph =
        read_json(&parameters.input_files.graph).context("Failed to read graph")?;

    let weights: Option<Weights> = if let Some(filename) = parameters.input_files.weights {
        info!("Reading graph weights");
        Some(read_json(&filename).context("Failed to read weights")?)
    } else {
        None
    };

    let order: Option<Vec<usize>> = if let Some(filename) = parameters.input_files.input_order {
        info!("Reading node ordering");
        Some(read_json(&filename).context("Failed to read node ordering")?)
    } else {
        None
    };

    info!("Reading queries");
    let queries: Vec<Query> =
        read_json(&parameters.input_files.queries).context("Failed to read queries")?;

    if queries.is_empty() {
        warn!("No query to execute");
        return Ok(());
    }

    // Initialize the global rayon thread pool.
    rayon::ThreadPoolBuilder::new()
        .num_threads(parameters.nb_threads)
        .build_global()
        .unwrap();

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

        if let Some(filename) = parameters.output_order {
            write_json(&overlay.get_order(), &filename)?;
        }

        if let Some(filename) = parameters.output_overlay {
            write_json(&overlay, &filename)?;
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
                            QueryResult::ArrivalTime((query.id, ta))
                        } else {
                            QueryResult::NotConnected
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
                                graph.get_node_id(query.source),
                                graph.get_node_id(query.target),
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
    let filename = parameters
        .output_file
        .unwrap_or_else(|| PathBuf::from("output.json"));
    write_json(&output, &filename)?;
    Ok(())
}
