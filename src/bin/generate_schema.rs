use anyhow::Result;
use clap::Parser;
use log::info;
use schemars::gen::SchemaSettings;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use metropolis::agent::Agent;
use metropolis::network::road_network::RoadNetwork;
use metropolis::parameters::Parameters;

/// Generate the JSON Schemas for the input and output files of METROPOLIS
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// The directory where the JSON Schemas should be stored
    #[clap(parse(from_os_str))]
    path: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();

    env_logger::init();

    info!("Generating JSON Schemas");
    let settings = SchemaSettings::draft07().with(|s| {
        s.option_nullable = true;
        s.option_add_null_type = false;
    });
    let gen = settings.into_generator();

    // Agents.
    let schema = gen.clone().into_root_schema_for::<Vec<Agent<f64>>>();
    let filename = args.path.join("schema-agents.json");
    let mut file = File::create(&filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Road network.
    let schema = gen.clone().into_root_schema_for::<RoadNetwork<f64>>();
    let filename = args.path.join("schema-roadnetwork.json");
    let mut file = File::create(&filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    // Parameters.
    let schema = gen.into_root_schema_for::<Parameters<f64>>();
    let filename = args.path.join("schema-parameters.json");
    let mut file = File::create(&filename)?;
    write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;

    info!("Done");

    Ok(())
}
