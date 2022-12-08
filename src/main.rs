// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use anyhow::Result;
use clap::Parser;
use log::{info, LevelFilter};
use log4rs::append::console::ConsoleAppender;
use log4rs::append::file::FileAppender;
use log4rs::config::{Appender, Root};
use log4rs::encode::pattern::PatternEncoder;
use log4rs::filter::threshold::ThresholdFilter;
use log4rs::Config;
use metropolis::agent::Agent;
use metropolis::network::road_network::RoadNetwork;
use metropolis::network::Network;
use metropolis::parameters::Parameters;
use metropolis::simulation::Simulation;

/// METROPOLIS simulator.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Path of the input JSON file with the agents' data
    #[clap(short, long)]
    agents: PathBuf,
    /// Path of the input JSON file with the road-network's data
    #[clap(short, long)]
    road_network: Option<PathBuf>,
    /// Path of the input JSON file with the parameters' data
    #[clap(short, long)]
    parameters: PathBuf,
    /// Output directory
    #[clap(short, long, default_value = ".")]
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let stdout = ConsoleAppender::builder()
        .encoder(Box::new(PatternEncoder::new(
            "{h([{d(%Y-%m-%d %H:%M:%S)} {l}] {m}{n})}",
        )))
        .build();
    let log_filename: PathBuf = [args.output.to_str().unwrap(), "log.txt"].iter().collect();
    let log_file = FileAppender::builder()
        .encoder(Box::new(PatternEncoder::new(
            "[{d(%Y-%m-%d %H:%M:%S)} {l}] {m}{n}",
        )))
        .build(log_filename)
        .expect("Failed to initialize log file");
    let log_config = Config::builder()
        .appender(Appender::builder().build("stdout", Box::new(stdout)))
        .appender(
            Appender::builder()
                .filter(Box::new(ThresholdFilter::new(LevelFilter::Info)))
                .build("log_file", Box::new(log_file)),
        )
        .build(
            Root::builder()
                .appender("stdout")
                .appender("log_file")
                .build(LevelFilter::Debug),
        )
        .expect("Failed to create log config");
    log4rs::init_config(log_config).expect("Failed to initialize log");

    // Read input files.
    info!("Reading input files");
    let mut bytes = Vec::new();
    File::open(args.agents)
        .expect("Unable to open agents file")
        .read_to_end(&mut bytes)
        .expect("Unable to read agents file");
    let agents: Vec<Agent<f64>> = serde_json::from_slice(&bytes).expect("Unable to parse agents");

    let mut bytes = Vec::new();
    File::open(args.parameters)
        .expect("Unable to open parameters file")
        .read_to_end(&mut bytes)
        .expect("Unable to read parameters file");
    let parameters: Parameters<f64> =
        serde_json::from_slice(&bytes).expect("Unable to parse parameters");

    let road_network: Option<RoadNetwork<f64>> = if let Some(rn) = args.road_network {
        let mut bytes = Vec::new();
        File::open(rn)
            .expect("Unable to open road-network file")
            .read_to_end(&mut bytes)
            .expect("Unable to read road-network file");
        Some(serde_json::from_slice(&bytes).expect("Unable to parse road network"))
    } else {
        None
    };

    let network = Network::new(road_network);
    let simulation = Simulation::new(agents, network, parameters);

    std::fs::create_dir_all(&args.output)?;
    // Run the simulation.
    simulation.run(&args.output)
}
