use anyhow::Result;
use clap::Parser;
use log::info;
use std::fs;
use std::io::BufReader;
use std::path::Path;

use simulation::simulation::{read_output, Simulation, SimulationResults};

/// METROPOLIS simulator.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Path of the input JSON file
    #[clap(short, long)]
    input: String,
    /// Output directory
    #[clap(short, long, default_value = ".")]
    output: String,
    /// Only write the report, without running the simulator
    #[clap(long)]
    report: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    env_logger::init();

    // Read input file.
    info!("Reading input file");
    let file = fs::File::open(args.input).expect("Unable to open input file");
    let reader = BufReader::new(file);
    let sim: Simulation<f64> = serde_json::from_reader(reader).expect("Unable to parse simulation");

    // Create the output directory if it does not exist yet.
    let output_dir = Path::new(&args.output);
    if !output_dir.is_dir() {
        fs::create_dir(output_dir)?;
    }

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
