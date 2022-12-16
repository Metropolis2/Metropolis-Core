// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use anyhow::Result;
use clap::Parser;
use log::{info, LevelFilter};
use metropolis::agent::Agent;
use metropolis::network::road_network::RoadNetwork;
use metropolis::network::{NetworkSkim, NetworkWeights};
use metropolis::parameters::Parameters;
use metropolis::simulation::results::{AgentResults, AggregateResults};
use schemars::gen::SchemaSettings;
use simplelog::{ColorChoice, Config, TermLogger, TerminalMode};

/// Generate the JSON Schemas for the input and output files of METROPOLIS
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// The directory where the JSON Schemas should be stored
    path: PathBuf,
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

    info!("Generating JSON Schemas");
    let settings = SchemaSettings::draft07().with(|s| {
        s.option_nullable = true;
        s.option_add_null_type = false;
    });
    let gen = settings.into_generator();

    // Agents.
    let schema = gen.clone().into_root_schema_for::<Vec<Agent<f64>>>();
    let filename = args.path.join("schema-agents.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Road network.
    let schema = gen.clone().into_root_schema_for::<RoadNetwork<f64>>();
    let filename = args.path.join("schema-roadnetwork.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Parameters.
    let schema = gen.clone().into_root_schema_for::<Parameters<f64>>();
    let filename = args.path.join("schema-parameters.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Aggregate results.
    let schema = gen.clone().into_root_schema_for::<AggregateResults<f64>>();
    let filename = args.path.join("schema-aggregate-results.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Agent-specific results.
    let schema = gen.clone().into_root_schema_for::<AgentResults<f64>>();
    let filename = args.path.join("schema-agent-results.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Network weights results.
    let schema = gen.clone().into_root_schema_for::<NetworkWeights<f64>>();
    let filename = args.path.join("schema-weight-results.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Network skim results.
    let schema = gen.into_root_schema_for::<NetworkSkim<f64>>();
    let filename = args.path.join("schema-skim-results.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    info!("Done");

    Ok(())
}
