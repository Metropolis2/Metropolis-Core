use anyhow::Result;
use clap::Parser;
use log::info;
use schemars::gen::SchemaSettings;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use std::{fs, path::PathBuf};

use simulation::simulation::{read_output, Simulation, SimulationResults};

/// METROPOLIS simulator.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Path of the input JSON file
    #[clap(short, long, default_value = "none")]
    input: String,
    /// Output directory
    #[clap(short, long, default_value = ".")]
    output: String,
    /// Only write the report, without running the simulator
    #[clap(long)]
    report: bool,
    /// Generate the JSON Schema of the input JSON file.
    #[clap(long)]
    schema: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    env_logger::init();

    // Create the output directory if it does not exist yet.
    let output_dir = Path::new(&args.output);
    if !output_dir.is_dir() {
        fs::create_dir(output_dir)?;
    }

    if args.schema {
        // Generate the JSON Schema for Simulation.
        info!("Generating JSON Schema");
        let settings = SchemaSettings::draft07().with(|s| {
            s.option_nullable = true;
            s.option_add_null_type = false;
        });
        let gen = settings.into_generator();
        let schema = gen.into_root_schema_for::<Simulation<f64>>();
        let filename: PathBuf = [output_dir.to_str().unwrap(), "schema.json"]
            .iter()
            .collect();
        let mut file = File::create(&filename)?;
        info!(
            "Writing JSON Schema to {}",
            filename.file_name().unwrap().to_str().unwrap()
        );
        write!(file, "{}", serde_json::to_string_pretty(&schema)?)?;
        return Ok(());
    }

    // Read input file.
    info!("Reading input file");
    let file = fs::File::open(args.input).expect("Unable to open input file");
    let reader = BufReader::new(file);
    let sim: Simulation<f64> = serde_json::from_reader(reader).expect("Unable to parse simulation");

    if args.report {
        // Write the report.
        info!("Reading output files");
        let results: SimulationResults<f64> = read_output(output_dir);
        info!("Writing report");
        sim.write_report(&results, output_dir)
    } else {
        // Run the simulation.
        sim.run(output_dir)
    }
}
