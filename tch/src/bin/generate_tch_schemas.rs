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
use schemars::gen::SchemaSettings;
use simplelog::{ColorChoice, Config, TermLogger, TerminalMode};
use tch::tools::DeserGraph;
use tch::tools::{Output, Parameters, Query};
use ttf::TTF;

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

    std::fs::create_dir_all(&args.path)?;

    info!("Generating JSON Schemas");
    let settings = SchemaSettings::draft07().with(|s| {
        s.option_nullable = true;
        s.option_add_null_type = false;
    });
    let gen = settings.into_generator();

    // Queries.
    let schema = gen.clone().into_root_schema_for::<Vec<Query>>();
    let filename = args.path.join("queries.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Graph.
    let schema = gen.clone().into_root_schema_for::<DeserGraph>();
    let filename = args.path.join("graph.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Weights.
    #[allow(clippy::disallowed_types)]
    let schema = gen
        .clone()
        .into_root_schema_for::<std::collections::HashMap<usize, TTF<f64>>>();
    let filename = args.path.join("weights.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Parameters.
    let schema = gen.clone().into_root_schema_for::<Parameters>();
    let filename = args.path.join("parameters.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Node order.
    let schema = gen.clone().into_root_schema_for::<Vec<usize>>();
    let filename = args.path.join("node-order.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Output.
    let schema = gen.into_root_schema_for::<Output>();
    let filename = args.path.join("output.json");
    let mut file = File::create(filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    info!("Done");

    Ok(())
}
