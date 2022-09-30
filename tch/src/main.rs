// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::convert::TryFrom;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::path::Path;
use std::time::Instant;

use anyhow::Result;
use geojson::{FeatureCollection, GeoJson};
use hashbrown::HashMap;
use petgraph::graph::{node_index, DiGraph, EdgeIndex, NodeIndex};
use petgraph::visit::EdgeRef;
use priority_queue::PriorityQueue;
use tch::*;
use ttf::{PwlTTF, TTFSimplification, TTF};

#[allow(dead_code)]
enum Input {
    Ordering,
    Construction,
    Import,
}

pub fn main() -> Result<()> {
    rayon::ThreadPoolBuilder::new()
        .num_threads(8)
        .build_global()
        .unwrap();
    let full = false;
    let (graph, _node_map, edge_map) = read_network(full);
    // New CH implementation.
    println!("Reading link references.");
    let link_refs = read_link_patterns(&edge_map, full);
    println!("Done.");
    println!("Reading traffic patterns.");
    let traffic_patterns = read_traffic_patterns(&graph, &link_refs);
    println!("Done.");

    let input = Input::Import;

    let now = Instant::now();
    let ch: HierarchyOverlay<f64> = match input {
        Input::Ordering => {
            println!("Ordering.");
            let parameters = ContractionParameters::default();
            let ch = HierarchyOverlay::order(
                &graph,
                // |e| traffic_patterns.get(&e).cloned().unwrap(),
                |e| TTF::Constant(traffic_patterns.get(&e).cloned().unwrap().eval(0.)),
                parameters,
            );
            println!("Time taken for ordering: {}ms.", now.elapsed().as_millis());
            if false {
                // Save node order and CH.
                let path =
                    Path::new("/home/ljavaudin/GitRepositories/metrolib/hierarchy_overlay.bin");
                let buffer = File::create(path).unwrap();
                bincode::serialize_into(buffer, &ch).unwrap();
                serde_json::to_writer(&File::create("node_order.json").unwrap(), &ch.get_order())
                    .unwrap();
            }
            ch
        }
        Input::Construction => {
            println!("Construction.");
            let order = read_order_from("/home/ljavaudin/GitRepositories/metrolib/node_order.json");
            let parameters = ContractionParameters::default();
            let ch = HierarchyOverlay::construct(
                &graph,
                |e| traffic_patterns.get(&e).cloned().unwrap(),
                // |e| TTF::Constant(traffic_patterns.get(&e).cloned().unwrap().eval(0.)),
                |n| order[&n],
                parameters,
            );
            println!(
                "Time taken for construction: {}ms.",
                now.elapsed().as_millis()
            );
            ch
        }
        Input::Import => {
            let path = Path::new("/home/ljavaudin/GitRepositories/metrolib/hierarchy_overlay.bin");
            let file = File::open(path).expect("Unable to open file");
            let reader = BufReader::new(file);
            bincode::deserialize_from(reader).expect("Unable to parse hierarchy overlay")
        }
    };

    println!("Number of breakpoints: {}", ch.complexity());
    let approx_ch = if true {
        let now = Instant::now();
        let mut approx_ch = ch;
        println!("Approximating TTFs");
        approx_ch.simplify(TTFSimplification::Bound(10.0));
        println!(
            "Time taken for approximation: {}ms.",
            now.elapsed().as_millis()
        );
        println!("Number of breakpoints: {}", approx_ch.complexity());
        approx_ch
    } else {
        panic!();
    };

    if false {
        let n = 100;
        println!("Running {} EA queries", n * n);
        let now = Instant::now();
        let step = 1000;
        let dt = 8. * 3600.;
        let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let ea_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        let downward_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let mut ea_alloc = algo::EarliestArrivalAllocation::new(ea_search, downward_search);
        let mut candidate_map = HashMap::new();
        let mut results = Vec::with_capacity(n);
        // let mut abs_errors = Vec::new();
        // let mut rel_errors = Vec::new();
        for i in 0..n {
            println!("{i}");
            for j in 0..n {
                if let Some((ta, _path)) = approx_ch.earliest_arrival_query(
                    node_index(i * step),
                    node_index(j * step),
                    dt,
                    &mut ea_alloc,
                    &mut candidate_map,
                )? {
                    // let (true_ta, _path) = ch
                    // .earliest_arrival_query(
                    // node_index(i * step),
                    // node_index(j * step),
                    // dt,
                    // &mut ea_alloc,
                    // &mut candidate_map,
                    // )?
                    // .unwrap();
                    // let (tt, true_tt) = (ta - dt, true_ta - dt);
                    // abs_errors.push((tt - true_tt).abs());
                    // let rel_e = (tt - true_tt).abs() / true_tt;
                    // rel_errors.push(if !rel_e.is_nan() { rel_e } else { 0.0 });
                    results.push(((i * step, j * step), ta));
                }
            }
        }
        // print_mean_max_errors(abs_errors, rel_errors);
        println!(
            "Time taken per query: {}μs.",
            now.elapsed().as_micros() / (n * n) as u128
        );
        if false {
            write_results(dt, results)?;
        }
    }

    if false {
        let n = 20;
        println!("Running {} profile queries", n * n);
        let now = Instant::now();
        let step = 5000;
        let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let mut interval_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        let mut profile_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        let mut candidate_map = HashMap::new();
        // let mut abs_errors = Vec::new();
        // let mut rel_errors = Vec::new();
        for i in 0..n {
            println!("{i}");
            for j in 0..n {
                let approx_label = approx_ch.profile_query(
                    node_index(i * step),
                    node_index(j * step),
                    &mut interval_search,
                    &mut profile_search,
                    &mut candidate_map,
                );
                // let true_label = ch.profile_query(
                // node_index(i * step),
                // node_index(j * step),
                // &mut interval_search,
                // &mut profile_search,
                // &mut candidate_map,
                // );
                if approx_label.is_none() {
                    println!("Invalid query, from node {} to node {}", i * step, j * step,);
                    // } else {
                    // let (abs_e, rel_e) =
                    // get_abs_and_rel_error(approx_label.unwrap(), true_label.unwrap());
                    // abs_errors.push(abs_e);
                    // rel_errors.push(rel_e);
                }
            }
        }
        // print_mean_max_errors(abs_errors, rel_errors);
        println!(
            "Time taken per query: {}μs.",
            now.elapsed().as_micros() / (n * n) as u128
        );
        println!("End");
    }

    if false {
        let n = 1000;
        let step = 100;
        let nodes: Vec<_> = (0..n).into_iter().map(|i| node_index(i * step)).collect();
        let now = Instant::now();
        println!("Computing search spaces for {n} nodes");
        let mut search_spaces = approx_ch.get_search_spaces(&nodes, &nodes);
        println!("Time taken: {}ms.", now.elapsed().as_millis());
        let now = Instant::now();
        println!("Approximating TTFs for search spaces");
        search_spaces.simplify(TTFSimplification::Bound(10.0));
        println!(
            "Time taken for approximation: {}ms.",
            now.elapsed().as_millis()
        );
        // let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        // let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        // let mut interval_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        // let forw_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        // let back_search = DijkstraSearch::new(HashMap::new(), PriorityQueue::new());
        // let mut profile_search = BidirectionalDijkstraSearch::new(forw_search, back_search);
        // let mut candidate_map = HashMap::new();
        // let mut abs_errors = Vec::new();
        // let mut rel_errors = Vec::new();
        let m = 10;
        println!("Computing {} profile queries", n * n / (m * m));
        for i in 0..(n / m) {
            println!("{i}");
            for j in 0..(n / m) {
                let approx_label = algo::intersect_profile_query(
                    node_index(i * step),
                    node_index(j * step),
                    &search_spaces,
                )?;
                if approx_label.is_none() {
                    println!("Invalid query from {} to {}", i * step, j * step);
                }
                // let true_label = ch
                // .profile_query(
                // node_index(i * step),
                // node_index(j * step),
                // &mut interval_search,
                // &mut profile_search,
                // &mut candidate_map,
                // )
                // .unwrap();
                // let (abs_e, rel_e) = get_abs_and_rel_error(approx_label, true_label);
                // abs_errors.push(abs_e);
                // rel_errors.push(rel_e);
            }
        }
        // print_mean_max_errors(abs_errors, rel_errors);
        println!(
            "Time taken per query: {}μs.",
            now.elapsed().as_micros() / ((n * n) / (m * m)) as u128
        );
    }

    Ok(())
}

#[allow(dead_code)]
fn get_abs_and_rel_error<T: ttf::TTFNum>(ttf1: TTF<T>, ttf2: TTF<T>) -> (T, T) {
    let m1 = match &ttf1 {
        TTF::Piecewise(pwl_ttf1) => pwl_ttf1
            .iter()
            .map(|p| (p.y - ttf2.eval(p.x)).abs())
            .max_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap(),
        TTF::Constant(c1) => (*c1 - ttf2.eval(T::zero())).abs(),
    };
    let m2 = match &ttf2 {
        TTF::Piecewise(pwl_ttf2) => pwl_ttf2
            .iter()
            .map(|p| (p.y - ttf1.eval(p.x)).abs())
            .max_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap(),
        TTF::Constant(c2) => (*c2 - ttf1.eval(T::zero())).abs(),
    };
    let m = m1.max(m2);
    let rel_error = if ttf2.get_max() > T::zero() {
        m / ttf2.get_max()
    } else {
        T::zero()
    };
    (m, rel_error)
}

#[allow(dead_code)]
fn print_mean_max_errors(abs_errors: Vec<f64>, rel_errors: Vec<f64>) {
    println!(
        "Mean absolute error: {}",
        abs_errors.iter().sum::<f64>() / abs_errors.len() as f64
    );
    println!(
        "Max absolute error: {}",
        abs_errors
            .iter()
            .max_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap()
    );
    println!(
        "Mean relative error: {}",
        rel_errors.iter().sum::<f64>() / abs_errors.len() as f64
    );
    println!(
        "Max relative error: {}",
        rel_errors
            .iter()
            .max_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap()
    );
}

#[allow(dead_code)]
fn write_results(dt: f64, tas: Vec<((usize, usize), f64)>) -> std::io::Result<()> {
    let nb_queries = tas.len() as u32;
    let mut file = File::create("here.demands")?;
    file.write_all(b"demands\r\n")?;
    file.write_all(&nb_queries.to_ne_bytes())?;
    for ((s, t), ta) in tas.into_iter() {
        file.write_all(&(s as u32).to_ne_bytes())?;
        file.write_all(&(t as u32).to_ne_bytes())?;
        file.write_all(&(10. * dt).to_ne_bytes())?;
        file.write_all(&(10. * ta).to_ne_bytes())?;
        file.write_all(&0u32.to_ne_bytes())?;
    }
    file.write_all(&118891828u32.to_ne_bytes())?;
    Ok(())
}

#[allow(dead_code)]
fn read_geojson(path_str: &str) -> GeoJson {
    let path = Path::new(path_str);
    let display = path.display();

    // Open file.
    let mut file = match File::open(&path) {
        Err(why) => panic!("Cannot open {}: {}", display, why),
        Ok(file) => file,
    };

    // Read file.
    let mut s = String::new();
    file.read_to_string(&mut s)
        .unwrap_or_else(|why| panic!("Cannot read {}: {}", display, why));

    // Parse GeoJson.
    s.parse()
        .unwrap_or_else(|why| panic!("Cannot parse Geojson {}: {}", display, why))
}

type NodeMap = HashMap<u64, NodeIndex>;
type EdgeMap = HashMap<(u64, String), EdgeIndex>;

#[allow(dead_code)]
fn process_nodes<E>(gj: GeoJson, graph: &mut DiGraph<u64, E>) -> NodeMap {
    let fc =
        FeatureCollection::try_from(gj).expect("Could not read node file as FeatureCollection.");
    let mut node_map = NodeMap::new();
    for feature in fc.features.into_iter() {
        let id_value = feature
            .property("id")
            .expect("All features' properties must have an id.");
        let id = id_value
            .as_u64()
            .unwrap_or_else(|| panic!("Feature has invalid id property: {:?}", id_value));
        let node_id = graph.add_node(id);
        node_map.insert(id, node_id);
    }
    node_map
}

#[allow(dead_code)]
fn process_edges(gj: GeoJson, graph: &mut DiGraph<u64, f64>, node_map: &NodeMap) -> EdgeMap {
    let mut edge_map = EdgeMap::new();
    let fc =
        FeatureCollection::try_from(gj).expect("Could not read edge file as FeatureCollection.");
    for feature in fc.features {
        let source_value = feature
            .property("source")
            .expect("All features' properties must have a source.");
        let source = source_value
            .as_u64()
            .unwrap_or_else(|| panic!("Feature has invalid source property: {:?}", source_value));
        let &source_id = node_map
            .get(&source)
            .unwrap_or_else(|| panic!("Source is not in the nodes: {}", source));
        let target_value = feature
            .property("target")
            .expect("All features' properties must have a target.");
        let target = target_value
            .as_u64()
            .unwrap_or_else(|| panic!("Feature has invalid target property: {:?}", target_value));
        let &target_id = node_map
            .get(&target)
            .unwrap_or_else(|| panic!("Target is not in the nodes: {}", target));
        let id_value = feature
            .property("LINK_ID")
            .expect("All features' properties must have an id.");
        let id = id_value
            .as_u64()
            .unwrap_or_else(|| panic!("Feature has invalid id property: {:?}", id_value));
        let length_value = feature
            .property("length")
            .expect("All features' properties must have a specified length.");
        let length = length_value
            .as_f64()
            .unwrap_or_else(|| panic!("Feature has invalid length property: {:?}", length_value));
        // let speed_value = feature
        // .property("speed")
        // .expect("All features' properties must have a specified speed.");
        // let speed = speed_value
        // .as_f64()
        // .unwrap_or_else(|| panic!("Feature has invalid speed property: {:?}", speed_value));
        let travel_dir_value = feature
            .property("DIR_TRAVEL")
            .expect("All features' properties must have a specific direction.");
        let travel_dir = travel_dir_value.as_str().unwrap_or_else(|| {
            panic!(
                "Feature has invalid travel direction: {:?}",
                travel_dir_value
            )
        });
        let edge_id = graph.add_edge(source_id, target_id, length);
        edge_map.insert((id, travel_dir.to_owned()), edge_id);
    }
    edge_map
}

#[allow(dead_code)]
fn read_network(full: bool) -> (DiGraph<u64, f64>, NodeMap, EdgeMap) {
    println!("Reading nodes GeoJSON");
    let nodes: GeoJson;
    let edges: GeoJson;
    if full {
        nodes = read_geojson(
            "/home/ljavaudin/GitRepositories/mode_choice_reg/output/here_nodes_full.geojson",
        );
        println!("Reading edges GeoJSON");
        edges = read_geojson(
            "/home/ljavaudin/GitRepositories/mode_choice_reg/output/here_edges_full.geojson",
        );
    } else {
        nodes = read_geojson(
            "/home/ljavaudin/GitRepositories/mode_choice_reg/output/here_nodes.geojson",
        );
        println!("Reading edges GeoJSON");
        edges = read_geojson(
            "/home/ljavaudin/GitRepositories/mode_choice_reg/output/here_edges.geojson",
        );
    }
    println!("Processing nodes");
    let mut graph = DiGraph::new();
    let node_map = process_nodes(nodes, &mut graph);
    println!("Processing edges");
    let edge_map = process_edges(edges, &mut graph, &node_map);
    println!("Number of nodes: {}", graph.node_count());
    println!("Number of edges: {}", graph.edge_count());
    (graph, node_map, edge_map)
}

#[allow(dead_code)]
fn read_traffic_patterns(
    graph: &DiGraph<u64, f64>,
    link_refs: &HashMap<EdgeIndex, u64>,
) -> HashMap<EdgeIndex, TTF<f64>> {
    let path = Path::new(
        "/home/ljavaudin/GitRepositories/mode_choice_reg/data/2016_Q4_s161r3/europe_middleeast_africa/additional_content_europe_middle_east_africa/traffic_patterns_link_europe_s161_g0/NTP_SPD_EU_15MIN_KPH_161G0.csv"
    );
    let display = path.display();

    // Open file.
    let file = match File::open(&path) {
        Err(why) => panic!("Cannot open {}: {}", display, why),
        Ok(file) => file,
    };

    let mut rdr = csv::Reader::from_reader(file);

    let mut speeds = HashMap::new();

    for record in rdr.records().flatten() {
        assert!(record.len() >= 97, "Invalid row: {:?}", record);
        let pattern_id: u64 = record[0].parse().expect("Invalid id");
        let speed: Vec<f64> = record
            .iter()
            .skip(1)
            .take(96)
            .map(|v| v.parse().unwrap())
            .collect();
        speeds.insert(pattern_id, speed);
    }

    let mut traffic_patterns = HashMap::new();
    let mut departure_times = Vec::new();
    for i in 0..96 {
        departure_times.push(i as f64 * 15.0 * 60.0);
    }

    let mut n = 0;
    let mut nb_constants = 0;
    for edge in graph.edge_references() {
        if let Some(pattern_id) = link_refs.get(&edge.id()) {
            if let Some(speed) = speeds.get(pattern_id) {
                let ttf = if speed.iter().all(|&s| s == speed[0]) {
                    nb_constants += 1;
                    let tt = 3.6 * edge.weight() / speed[0];
                    TTF::Constant(tt as f64)
                } else {
                    let travel_times: Vec<_> = speed
                        .iter()
                        .map(|s| (3.6 * edge.weight() / s) as f64)
                        .collect();
                    let mut ttf = PwlTTF::from_x_and_y(departure_times.clone(), travel_times);
                    ttf.ensure_fifo();
                    TTF::Piecewise(ttf)
                };
                n += ttf.complexity();
                traffic_patterns.insert(edge.id(), ttf);
            }
        } else {
            panic!("Edge with no traffic pattern: {:?}", edge);
        }
    }
    println!("Initial number of breakpoints: {}", 96 * graph.edge_count());
    println!("Final number of breakpoints: {}", n);
    println!(
        "Share of edges with a constant TTF: {}",
        nb_constants as f64 / graph.edge_count() as f64
    );

    traffic_patterns
}

#[allow(dead_code)]
fn read_link_patterns(edge_map: &EdgeMap, full: bool) -> HashMap<EdgeIndex, u64> {
    let mut link_patterns = HashMap::new();

    let path = Path::new(
        "/home/ljavaudin/GitRepositories/mode_choice_reg/data/2016_Q4_s161r3/europe_middleeast_africa/additional_content_europe_middle_east_africa/traffic_patterns_link_europe_s161_g0/NTP_REF_EU_LINK_FC1-4_161G0.csv"
    );
    let display = path.display();

    // Open file.
    let file = match File::open(&path) {
        Err(why) => panic!("Cannot open {}: {}", display, why),
        Ok(file) => file,
    };

    let mut rdr = csv::Reader::from_reader(file);

    for record in rdr.records().flatten() {
        let link_id = record[1].parse().unwrap();
        let travel_direction = &record[2];
        let pattern_id = record[5].parse().unwrap(); // 5 => Tuesday.
        if let Some(&edge_id) = edge_map.get(&(link_id, travel_direction.to_owned())) {
            link_patterns.insert(edge_id, pattern_id);
        }
    }

    if full {
        let path = Path::new(
            "/home/ljavaudin/GitRepositories/mode_choice_reg/data/2016_Q4_s161r3/europe_middleeast_africa/additional_content_europe_middle_east_africa/traffic_patterns_link_europe_s161_g0/NTP_REF_EU_LINK_FC5_161G0.csv"
        );
        let display = path.display();

        // Open file.
        let file = match File::open(&path) {
            Err(why) => panic!("Cannot open {}: {}", display, why),
            Ok(file) => file,
        };

        let mut rdr = csv::Reader::from_reader(file);

        for record in rdr.records().flatten() {
            let link_id = record[0].parse().unwrap();
            let travel_direction = &record[1];
            let pattern_id = record[4].parse().unwrap(); // 5 => Tuesday.
            if let Some(&edge_id) = edge_map.get(&(link_id, travel_direction.to_owned())) {
                link_patterns.insert(edge_id, pattern_id);
            }
        }
    }

    link_patterns
}

#[allow(dead_code)]
fn read_order() -> HashMap<NodeIndex, usize> {
    let path = Path::new("/home/ljavaudin/GitRepositories/metrolib/node_order.txt");
    let display = path.display();

    // Open file.
    let file = match File::open(&path) {
        Err(why) => panic!("Cannot open {}: {}", display, why),
        Ok(file) => file,
    };

    let mut rdr = csv::ReaderBuilder::new()
        .has_headers(false)
        .from_reader(file);

    let mut order = HashMap::new();

    for (i, record) in rdr.records().flatten().enumerate() {
        let node: u64 = record[0].parse().expect("Invalid node");
        order.insert(node_index(node as usize), i);
    }

    order
}

#[allow(dead_code)]
fn read_order_from(filename: &str) -> HashMap<NodeIndex, usize> {
    let path = Path::new(filename);
    let file = File::open(path).expect("Unable to open file");
    let reader = BufReader::new(file);
    let order: Vec<usize> = serde_json::from_reader(reader).expect("Unable to parse node ordering");
    let mut map = HashMap::with_capacity(order.len());
    for (i, o) in order.into_iter().enumerate() {
        map.insert(node_index(i), o);
    }
    map
}
