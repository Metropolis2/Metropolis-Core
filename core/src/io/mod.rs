// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to import / export of simulation data.

mod arrow;
pub mod csv;
pub mod json;
pub mod parquet;
mod polars;

use std::path::Path;

use anyhow::{bail, Context, Result};

use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::RoadNetworkWeights;
use crate::network::Network;
use crate::parameters::InputFiles;
use crate::population::Agent;

pub(crate) fn read_population(input_files: &InputFiles) -> Result<Vec<Agent>> {
    arrow::get_agents_from_files(
        &input_files.agents,
        &input_files.alternatives,
        input_files.trips.as_deref(),
    )
    .context("Failed to read population")
}

pub(crate) fn read_network(input_files: &InputFiles) -> Result<Network> {
    let road_network = match (
        input_files.edges.as_ref(),
        input_files.vehicle_types.as_ref(),
    ) {
        (Some(edges_path), Some(vehicle_path)) => Some(
            arrow::get_road_network_from_files(edges_path, vehicle_path)
                .context("Failed to read road-network")?,
        ),
        (Some(_), None) => {
            bail!("Vehicle types input file is mandatory when edges file is specified");
        }
        (None, Some(_)) => {
            bail!("Edges input file is mandatory when vehicle-types file is specified");
        }
        (None, None) => None,
    };
    Ok(Network::new(road_network))
}

pub(crate) fn read_rn_weights(
    filename: &Path,
    unique_vehicles: &UniqueVehicles,
) -> Result<RoadNetworkWeights> {
    arrow::get_road_network_weights_from_file(filename, unique_vehicles)
}
