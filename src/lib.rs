// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Library for Metropolis: a dynamic multi-modal traffic-assignment simulator.
#![doc(html_no_source)]

pub mod agent;
pub mod event;
pub mod gui;
pub mod io;
pub mod learning;
pub mod logging;
pub mod mode;
pub mod network;
pub mod parameters;
pub mod progress_bar;
pub mod report;
pub mod schedule_utility;
mod schema;
mod serialization;
pub mod simulation;
pub mod travel_utility;
pub mod units;

use std::env;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use log::warn;
use parameters::SavingFormat;
// Re-exports.
pub use report::write_report;

#[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
/// Displays statistics on allocated and resident memory.
pub fn show_stats() {
    jemalloc_ctl::epoch::advance().unwrap();

    let allocated = jemalloc_ctl::stats::allocated::read().unwrap();
    let resident = jemalloc_ctl::stats::resident::read().unwrap();
    log::debug!(
        "{} bytes allocated/{} bytes resident",
        indicatif::HumanBytes(allocated as u64).to_string(),
        indicatif::HumanBytes(resident as u64).to_string()
    );
}

#[cfg(any(not(feature = "jemalloc"), target_env = "msvc"))]
/// Displays statistics on allocated and resident memory.
pub fn show_stats() {}

// Dependencies only used in the bins.
use clap as _;

/// Deserializes a simulation, runs it and stores the results to a given output directory.
///
/// This function takes as argument the path to the `parameters.json` file.
pub fn run_simulation(path: &Path) -> Result<()> {
    // Read parameters.
    let parameters = io::json::get_parameters_from_json(path)?;

    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(&parameters.output_directory).with_context(|| {
        format!(
            "Failed to create output directory `{:?}`",
            parameters.output_directory
        )
    })?;

    logging::initialize_logging(&parameters.output_directory)?;

    let simulation = io::read_simulation(parameters)?;

    // The previous iteration_results file need to be removed if it exists.
    let extension = match simulation.get_parameters().saving_format {
        SavingFormat::JSON => "json",
        SavingFormat::Parquet => "parquet",
        SavingFormat::CSV => "csv",
    };
    let filename: PathBuf = [
        simulation
            .get_parameters()
            .output_directory
            .to_str()
            .unwrap(),
        &format!("iteration_results.{extension}"),
    ]
    .iter()
    .collect();
    if filename.is_file() {
        warn!("Removing already existing file `{filename:?}`");
        std::fs::remove_file(&filename)
            .with_context(|| format!("Failed to remove file: `{filename:?}`"))?;
    }

    let weights = simulation
        .get_parameters()
        .input_files
        .weights
        .as_deref()
        .map(io::json::read_json)
        .transpose()?;

    // Run the simulation.
    simulation.run_from_weights(weights)
}

/// Deserializes a simulation from JSON input files, computes the pre-day choices and stores them
/// in the given output directory.
pub fn get_choices_from_json_files(
    agents: &Path,
    parameters: &Path,
    road_network: Option<&Path>,
    weights: Option<&Path>,
    output: &Path,
) -> Result<()> {
    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(output)?;

    logging::initialize_logging(output)?;

    let simulation = io::json::get_simulation_from_json_files(agents, parameters, road_network)?;

    let weights = weights.map(io::json::read_json).transpose()?;

    // Run the simulation.
    simulation.compute_and_store_choices(weights, output)
}
