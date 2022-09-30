// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::fs;
use std::io::BufReader;
use std::path::PathBuf;

use anyhow::Result;
use clap::Parser;
use log::info;
use metropolis::agent::Agent;
use metropolis::network::road_network::RoadNetwork;
use metropolis::network::Network;
use metropolis::parameters::Parameters;
use metropolis::simulation::{results::SimulationResults, Simulation};

/// METROPOLIS simulator.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Path of the input JSON file with the agents' data
    #[clap(short, long)]
    #[clap(parse(from_os_str))]
    agents: PathBuf,
    /// Path of the input JSON file with the road-network's data
    #[clap(short, long)]
    #[clap(parse(from_os_str))]
    road_network: Option<PathBuf>,
    /// Path of the input JSON file with the parameters' data
    #[clap(short, long)]
    #[clap(parse(from_os_str))]
    parameters: PathBuf,
    /// Output directory
    #[clap(short, long, default_value = ".")]
    #[clap(parse(from_os_str))]
    output: PathBuf,
    /// Only write the report, without running the simulator (the output directory must contain the
    /// results of a previous run)
    #[clap(long)]
    report: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    env_logger::init();

    // Read input files.
    info!("Reading input files");
    let file = fs::File::open(args.agents).expect("Unable to open agents file");
    let reader = BufReader::new(file);
    let agents: Vec<Agent<f64>> = serde_json::from_reader(reader).expect("Unable to parse agents");

    let file = fs::File::open(args.parameters).expect("Unable to open parameters file");
    let reader = BufReader::new(file);
    let parameters: Parameters<f64> =
        serde_json::from_reader(reader).expect("Unable to parse parameters");

    let road_network: Option<RoadNetwork<f64>> = if let Some(rn) = args.road_network {
        let file = fs::File::open(rn).expect("Unable to open road-network file");
        let reader = BufReader::new(file);
        Some(serde_json::from_reader(reader).expect("Unable to parse road network"))
    } else {
        None
    };

    let network = Network::new(road_network);
    let simulation = Simulation::new(agents, network, parameters);

    if args.report {
        // Write the report.
        info!("Reading output files");
        let results: SimulationResults<f64> = SimulationResults::from_output_dir(&args.output);
        info!("Writing report");
        metropolis::write_report(&results, &args.output)
    } else {
        // Run the simulation.
        simulation.run(&args.output)
    }
}
