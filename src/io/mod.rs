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
use ttf::TTFNum;

use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::{RoadNetwork, RoadNetworkWeights};
use crate::network::Network;
use crate::parameters::Parameters;
use crate::simulation::Simulation;
use crate::units::{Interval, Time};

pub(crate) fn read_simulation<T: TTFNum>(parameters: Parameters<T>) -> Result<Simulation<T>> {
    let agents = arrow::get_agents_from_files(
        &parameters.input_files.agents,
        &parameters.input_files.alternatives,
        parameters.input_files.trips.as_deref(),
    )
    .context("Failed to read population")?;
    let road_network = match (
        parameters.input_files.edges.as_ref(),
        parameters.input_files.vehicle_types.as_ref(),
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
    let network = Network::new(road_network);
    Ok(Simulation::new(agents, network, parameters))
}

pub(crate) fn read_rn_weights<T: TTFNum>(
    filename: &Path,
    period: Interval<T>,
    interval: Time<T>,
    road_network: &RoadNetwork<T>,
    unique_vehicles: &UniqueVehicles,
) -> Result<RoadNetworkWeights<T>> {
    arrow::get_road_network_weights_from_file(
        filename,
        period,
        interval,
        road_network,
        unique_vehicles,
    )
}
