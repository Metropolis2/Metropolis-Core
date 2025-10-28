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
