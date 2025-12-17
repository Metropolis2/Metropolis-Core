// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//!  Metropolis-Core: the Rust-based core of the METROPOLIS2 simulator.
#![doc(html_no_source)]

pub mod event;
pub mod io;
pub mod learning;
pub mod logging;
pub mod mode;
pub mod network;
pub mod parameters;
pub mod population;
pub mod progress_bar;
pub mod report;
pub mod schedule_utility;
pub mod simulation;
pub mod travel_utility;
pub mod units;

use std::env;
use std::path::Path;

use anyhow::{anyhow, Context, Result};
// Dependencies only used in the bins.
use clap as _;
use log::{error, log_enabled};

/// Deserializes a simulation, runs it and stores the results to a given output directory.
///
/// This function takes as argument the path to the `parameters.json` file.
pub fn run_simulation(path: &Path) -> Result<()> {
    let res = run_simulation_imp(path, None::<std::io::Empty>);
    if let Err(err) = res {
        if log_enabled!(log::Level::Error) {
            // Use the `error` macro so that the error is logged to all the loggers.
            error!("{err:?}");
            Ok(())
        } else {
            // Return the error so that it is printed to console or GUI.
            Err(anyhow!(err))
        }
    } else {
        Ok(())
    }
}

/// Deserializes a simulation, runs it and stores the results to a given output directory.
///
/// This function takes as argument the path to the `parameters.json` file and a writer for the
/// logs.
pub fn run_simulation_with_writer<W: std::io::Write + Send + 'static>(
    path: &Path,
    writer: W,
) -> Result<()> {
    let res = run_simulation_imp(path, Some(writer));
    if let Err(err) = res {
        if log_enabled!(log::Level::Error) {
            // Use the `error` macro so that the error is logged to all the loggers.
            error!("{err:?}");
            Ok(())
        } else {
            // Return the error so that it is printed to console or GUI.
            Err(anyhow!(err))
        }
    } else {
        Ok(())
    }
}

fn run_simulation_imp<W: std::io::Write + Send + 'static>(
    path: &Path,
    writer: Option<W>,
) -> Result<()> {
    println!(
        "
        Metropolis-Core v{}
        Copyright (C) 2022-2025 André de Palma, Lucas Javaudin
        This program comes with ABSOLUTELY NO WARRANTY.
        This is free software, and you are welcome to redistribute it
        under certain conditions; see `https://www.gnu.org/licenses/' for details.
        ",
        env!("CARGO_PKG_VERSION")
    );
    // Read parameters.
    let params = io::json::get_parameters_from_json(path)?;
    parameters::init(params)?;

    // Set the working directory to the directory of the `parameters.json` file so that the input
    // paths can be interpreted as being relative to this file.
    if let Some(parent_dir) = path.parent() {
        // Fix a bug when trying to set the current directory from an empty path.
        if parent_dir.to_str().map(|s| !s.is_empty()).unwrap_or(true) {
            env::set_current_dir(parent_dir)
                .with_context(|| format!("Failed to set working directory to `{parent_dir:?}`"))?;
        }
    }

    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(parameters::output_directory()).with_context(|| {
        format!(
            "Failed to create output directory `{:?}`",
            parameters::output_directory()
        )
    })?;

    logging::initialize_logging(parameters::output_directory(), writer)?;

    let agents = io::read_population(parameters::input_files())?;
    population::init(agents)?;

    let network = io::read_network(parameters::input_files())?;
    network::init(network)?;

    // Run the simulation.
    simulation::run()
}
