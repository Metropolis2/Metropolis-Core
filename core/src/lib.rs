// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Library for Metropolis: a dynamic multi-modal traffic-assignment simulator.
#![doc(html_no_source)]

pub mod agent;
pub mod event;
pub mod io;
pub mod learning;
pub mod logging;
pub mod mode;
pub mod network;
pub mod parameters;
pub mod progress_bar;
pub mod report;
pub mod schedule_utility;
mod serialization;
pub mod simulation;
pub mod travel_utility;
pub mod units;

use std::env;
use std::path::Path;

use anyhow::{Context, Result};
// Dependencies only used in the bins.
use clap as _;
// Re-exports.
pub use report::write_report;

/// Deserializes a simulation, runs it and stores the results to a given output directory.
///
/// This function takes as argument the path to the `parameters.json` file.
pub fn run_simulation(path: &Path) -> Result<()> {
    run_simulation_imp(path, None::<std::io::Empty>)
}

/// Deserializes a simulation, runs it and stores the results to a given output directory.
///
/// This function takes as argument the path to the `parameters.json` file and a writer for the
/// logs.
pub fn run_simulation_with_writer<W: std::io::Write + Send + 'static>(
    path: &Path,
    writer: W,
) -> Result<()> {
    run_simulation_imp(path, Some(writer))
}

fn run_simulation_imp<W: std::io::Write + Send + 'static>(
    path: &Path,
    writer: Option<W>,
) -> Result<()> {
    // Read parameters.
    let parameters = io::json::get_parameters_from_json(path)?;

    // Set the working directory to the directory of the `parameters.json` file so that the input
    // paths can be interpreted as being relative to this file.
    if let Some(parent_dir) = path.parent() {
        env::set_current_dir(parent_dir)
            .with_context(|| format!("Failed to set working directory to `{parent_dir:?}`"))?;
    }

    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(&parameters.output_directory).with_context(|| {
        format!(
            "Failed to create output directory `{:?}`",
            parameters.output_directory
        )
    })?;

    logging::initialize_logging(&parameters.output_directory, writer)?;

    let simulation = io::read_simulation(parameters)?;

    // Run the simulation.
    simulation.run()
}
