// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::path::PathBuf;

use anyhow::Result;
use clap::Parser;

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
    /// Path of the input JSON file with the network weights to use when initializing the
    /// simulation (if empty, free-flow network weights are used)
    #[clap(short, long)]
    weights: Option<PathBuf>,
    /// Output directory
    #[clap(short, long, default_value = ".")]
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    metropolis::run_simulation_from_json_files(
        &args.agents,
        &args.parameters,
        args.road_network.as_deref(),
        args.weights.as_deref(),
        &args.output,
    )
}
