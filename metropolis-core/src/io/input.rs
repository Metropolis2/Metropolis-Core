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

//! Functions to read the input files of the simulation.

use std::path::Path;

use anyhow::{bail, Context, Result};
use arrow::record_batch::RecordBatch;
use log::info;
use metro_io::read::{read_batch, required, Columns, GetValue};

use crate::calibration::{EdgeFactor, TargetRoute};
use crate::hash::{HashMap, HashSet};
use crate::mode::trip::Leg;
use crate::mode::Mode;
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::vehicle::Vehicle;
use crate::network::road_network::{OriginalEdgeId, RoadEdge, RoadNetwork, RoadNetworkWeights};
use crate::population::Agent;
use crate::units::*;

/// Reads a road network from the filename of edges and vehicle types.
pub(crate) fn get_road_network_from_files(
    edges_path: &Path,
    vehicle_path: &Path,
) -> Result<RoadNetwork> {
    // Read edges parquet file.
    info!("Reading edges");
    let edge_batch = read_batch(edges_path)?;
    let (edges, edge_ids) = read_edges(edge_batch).context("Cannot parse edges")?;
    // Read vehicles parquet file.
    info!("Reading vehicle types");
    let vehicle_batch = read_batch(vehicle_path)?;
    let vehicles = read_vehicles(vehicle_batch, edge_ids).context("Cannot parse vehicles")?;
    Ok(RoadNetwork::from_edges(edges, vehicles))
}

/// Reads agents from the filename of agents, alternatives and trips.
pub(crate) fn get_agents_from_files(
    agents_path: &Path,
    alts_path: &Path,
    trips_path: Option<&Path>,
) -> Result<Vec<Agent>> {
    let trips = if let Some(filename) = trips_path {
        // Read trip file.
        info!("Reading trips");
        let trip_batch = read_batch(filename)?;
        read_trips(trip_batch).context("Cannot parse trips")?
    } else {
        Default::default()
    };
    // Read alternatives parquet file.
    info!("Reading alternatives");
    let alt_batch = read_batch(alts_path)?;
    let alternatives = read_alternatives(alt_batch, trips).context("Cannot parse alternatives")?;
    // Read agent parquet file.
    info!("Reading agents");
    let agent_batch = read_batch(agents_path)?;
    let agents = read_agents(agent_batch, alternatives).context("Cannot parse agents")?;
    Ok(agents)
}

/// Reads [RoadNetworkWeights] from a filename.
pub(crate) fn get_road_network_weights_from_file(
    path: &Path,
    unique_vehicles: &UniqueVehicles,
) -> Result<RoadNetworkWeights> {
    info!("Reading road-network conditions");
    let batch = read_batch(path)?;
    let rn_weights_vec = read_rn_weights(batch).context("Cannot parse road-network conditions")?;
    let rn_weights = RoadNetworkWeights::from_values(rn_weights_vec, unique_vehicles)
        .context("Invalid road-network conditions")?;
    Ok(rn_weights)
}

/// Reads the [TargetRoute]s of the capacity calibration from a filename.
pub(crate) fn get_target_routes_from_file(path: &Path) -> Result<Vec<TargetRoute>> {
    info!("Reading target routes");
    let batch = read_batch(path)?;
    read_target_routes(batch).context("Cannot parse target routes")
}

/// Reads the [EdgeFactor]s of the capacity calibration from a filename.
pub(crate) fn get_capacity_factors_from_file(path: &Path) -> Result<Vec<EdgeFactor>> {
    info!("Reading capacity factors");
    let batch = read_batch(path)?;
    read_capacity_factors(batch).context("Cannot parse capacity factors")
}

type LegMap = HashMap<(MetroId, MetroId), Vec<Leg>>;
type AltMap = HashMap<MetroId, Vec<Mode>>;

/// Reads an arrow `RecordBatch` and returns a `HashMap` that maps `(agent_id, alt_id)` to a `Trip`.
fn read_trips(batch: RecordBatch) -> Result<LegMap> {
    let mut columns = Columns::new(batch);
    let agent_id = columns.id(&["agent_id"])?;
    let alt_id = columns.id(&["alt_id"])?;
    let trip_id = columns.id(&["trip_id"])?;
    let class_type = columns.str(&["class", "type"])?;
    let class_origin = columns.id(&["class", "origin"])?;
    let class_destination = columns.id(&["class", "destination"])?;
    let class_vehicle = columns.id(&["class", "vehicle"])?;
    let class_route = columns.id_list(&["class", "route"])?;
    let class_travel_time = columns.f64(&["class", "travel_time"])?;
    let stopping_time = columns.f64(&["stopping_time"])?;
    let constant_utility = columns.f64(&["constant_utility"])?;
    let alpha = columns.f64(&["alpha"])?;
    let travel_utility_one = columns.f64(&["travel_utility", "one"])?;
    let travel_utility_two = columns.f64(&["travel_utility", "two"])?;
    let travel_utility_three = columns.f64(&["travel_utility", "three"])?;
    let travel_utility_four = columns.f64(&["travel_utility", "four"])?;
    let schedule_utility_type = columns.str(&["schedule_utility", "type"])?;
    let schedule_utility_tstar = columns.f64(&["schedule_utility", "tstar"])?;
    let schedule_utility_beta = columns.f64(&["schedule_utility", "beta"])?;
    let schedule_utility_gamma = columns.f64(&["schedule_utility", "gamma"])?;
    let schedule_utility_delta = columns.f64(&["schedule_utility", "delta"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut trips: LegMap = HashMap::with_capacity_and_hasher(n, Default::default());
    let mut unique_tuples = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let agent_id = required(agent_id.get(i), "agent_id")?;
        let alt_id = required(alt_id.get(i), "alt_id")?;
        let trip_id = required(trip_id.get(i), "trip_id")?;
        let trip = Leg::from_values(
            trip_id,
            class_type.get(i),
            class_origin.get(i),
            class_destination.get(i),
            class_vehicle.get(i),
            class_route.get(i),
            class_travel_time.get(i),
            stopping_time.get(i),
            constant_utility.get(i),
            alpha.get(i),
            travel_utility_one.get(i),
            travel_utility_two.get(i),
            travel_utility_three.get(i),
            travel_utility_four.get(i),
            schedule_utility_type.get(i),
            schedule_utility_tstar.get(i),
            schedule_utility_beta.get(i),
            schedule_utility_gamma.get(i),
            schedule_utility_delta.get(i),
        )
        .with_context(|| {
            format!(
            "Failed to parse trip (`agent_id`={agent_id}, `alt_id`={alt_id}, `trip_id`={trip_id})"
        )
        })?;
        if !unique_tuples.insert((agent_id, alt_id, trip.id)) {
            bail!(
                "Found duplicate trip: (`agent_id`={agent_id}, `alt_id`={alt_id}, `trip_id`={})",
                trip.id
            );
        }
        trips.entry((agent_id, alt_id)).or_default().push(trip);
    }
    Ok(trips)
}

/// Reads an arrow `RecordBatch` and returns a `HashMap` that maps `agent_id` to an `Alt`.
fn read_alternatives(batch: RecordBatch, mut trips: LegMap) -> Result<AltMap> {
    let mut columns = Columns::new(batch);
    let agent_id = columns.id(&["agent_id"])?;
    let alt_id = columns.id(&["alt_id"])?;
    let origin_delay = columns.f64(&["origin_delay"])?;
    let dt_choice_type = columns.str(&["dt_choice", "type"])?;
    let dt_choice_departure_time = columns.f64(&["dt_choice", "departure_time"])?;
    let dt_choice_period = columns.list_f64(&["dt_choice", "period"])?;
    let dt_choice_interval = columns.f64(&["dt_choice", "interval"])?;
    let dt_choice_offset = columns.f64(&["dt_choice", "offset"])?;
    let dt_choice_model_type = columns.str(&["dt_choice", "model", "type"])?;
    let dt_choice_model_u = columns.f64(&["dt_choice", "model", "u"])?;
    let dt_choice_model_mu = columns.f64(&["dt_choice", "model", "mu"])?;
    let dt_choice_model_constants = columns.list_f64(&["dt_choice", "model", "constants"])?;
    let constant_utility = columns.f64(&["constant_utility"])?;
    let alpha = columns.f64(&["alpha"])?;
    let total_travel_utility_one = columns.f64(&["total_travel_utility", "one"])?;
    let total_travel_utility_two = columns.f64(&["total_travel_utility", "two"])?;
    let total_travel_utility_three = columns.f64(&["total_travel_utility", "three"])?;
    let total_travel_utility_four = columns.f64(&["total_travel_utility", "four"])?;
    let origin_utility_type = columns.str(&["origin_utility", "type"])?;
    let origin_utility_tstar = columns.f64(&["origin_utility", "tstar"])?;
    let origin_utility_beta = columns.f64(&["origin_utility", "beta"])?;
    let origin_utility_gamma = columns.f64(&["origin_utility", "gamma"])?;
    let origin_utility_delta = columns.f64(&["origin_utility", "delta"])?;
    let destination_utility_type = columns.str(&["destination_utility", "type"])?;
    let destination_utility_tstar = columns.f64(&["destination_utility", "tstar"])?;
    let destination_utility_beta = columns.f64(&["destination_utility", "beta"])?;
    let destination_utility_gamma = columns.f64(&["destination_utility", "gamma"])?;
    let destination_utility_delta = columns.f64(&["destination_utility", "delta"])?;
    let pre_compute_route = columns.bool(&["pre_compute_route"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut alternatives: AltMap = HashMap::with_capacity_and_hasher(n, Default::default());
    let mut unique_pairs = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let agent_id = required(agent_id.get(i), "agent_id")?;
        let alt_id = required(alt_id.get(i), "alt_id")?;
        let legs = trips.remove(&(agent_id, alt_id));
        let alt = Mode::from_values(
            alt_id,
            origin_delay.get(i),
            dt_choice_type.get(i),
            dt_choice_departure_time.get(i),
            dt_choice_period.get(i),
            dt_choice_interval.get(i),
            dt_choice_offset.get(i),
            dt_choice_model_type.get(i),
            dt_choice_model_u.get(i),
            dt_choice_model_mu.get(i),
            dt_choice_model_constants.get(i),
            constant_utility.get(i),
            alpha.get(i),
            total_travel_utility_one.get(i),
            total_travel_utility_two.get(i),
            total_travel_utility_three.get(i),
            total_travel_utility_four.get(i),
            origin_utility_type.get(i),
            origin_utility_tstar.get(i),
            origin_utility_beta.get(i),
            origin_utility_gamma.get(i),
            origin_utility_delta.get(i),
            destination_utility_type.get(i),
            destination_utility_tstar.get(i),
            destination_utility_beta.get(i),
            destination_utility_gamma.get(i),
            destination_utility_delta.get(i),
            pre_compute_route.get(i),
            legs,
        )
        .with_context(|| {
            format!("Failed to parse alternative (`agent_id`={agent_id}, `alt_id`={alt_id})")
        })?;
        if !unique_pairs.insert((agent_id, alt.id())) {
            bail!(
                "Found duplicate alternative: (`agent_id`={agent_id}, `alt_id`={})",
                alt.id()
            );
        }
        alternatives.entry(agent_id).or_default().push(alt);
    }
    Ok(alternatives)
}

/// Reads an arrow `RecordBatch` and returns a `Vec` of `Agent`.
fn read_agents(batch: RecordBatch, mut alternatives: AltMap) -> Result<Vec<Agent>> {
    let mut columns = Columns::new(batch);
    let agent_id = columns.id(&["agent_id"])?;
    let alt_choice_type = columns.str(&["alt_choice", "type"])?;
    let alt_choice_u = columns.f64(&["alt_choice", "u"])?;
    let alt_choice_mu = columns.f64(&["alt_choice", "mu"])?;
    let alt_choice_constants = columns.list_f64(&["alt_choice", "constants"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut agents = Vec::with_capacity(n);
    let mut unique_agent_ids = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let agent_id = required(agent_id.get(i), "agent_id")?;
        if !unique_agent_ids.insert(agent_id) {
            // agent_id value was already inserted.
            bail!("Found duplicate `agent_id`: {agent_id}",);
        }
        let alts = alternatives.remove(&agent_id);
        let agent = Agent::from_values(
            agent_id,
            alt_choice_type.get(i),
            alt_choice_u.get(i),
            alt_choice_mu.get(i),
            alt_choice_constants.get(i),
            alts,
        )
        .with_context(|| format!("Failed to parse agent {agent_id}"))?;
        agents.push(agent);
    }
    Ok(agents)
}

type EdgeVec = Vec<(OriginalEdgeId, OriginalEdgeId, RoadEdge)>;

/// Reads an arrow `RecordBatch` with edges data and returns a `Vec` of `RoadEdge` and a `HashSet`
/// of unique edge ids.
fn read_edges(batch: RecordBatch) -> Result<(EdgeVec, HashSet<MetroId>)> {
    let mut columns = Columns::new(batch);
    let edge_id = columns.id(&["edge_id"])?;
    let source = columns.id(&["source"])?;
    let target = columns.id(&["target"])?;
    let speed = columns.f64(&["speed"])?;
    let length = columns.f64(&["length"])?;
    let lanes = columns.f64(&["lanes"])?;
    let speed_density_type = columns.str(&["speed_density", "type"])?;
    let speed_density_capacity = columns.f64(&["speed_density", "capacity"])?;
    let speed_density_min_density = columns.f64(&["speed_density", "min_density"])?;
    let speed_density_jam_density = columns.f64(&["speed_density", "jam_density"])?;
    let speed_density_jam_speed = columns.f64(&["speed_density", "jam_speed"])?;
    let speed_density_beta = columns.f64(&["speed_density", "beta"])?;
    let bottleneck_flow = columns.f64(&["bottleneck_flow"])?;
    let bottleneck_flows = columns.list_f64(&["bottleneck_flows"])?;
    let bottleneck_times = columns.list_f64(&["bottleneck_times"])?;
    let constant_travel_time = columns.f64(&["constant_travel_time"])?;
    let overtaking = columns.bool(&["overtaking"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut edges = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let edge_id = required(edge_id.get(i), "edge_id")?;
        let source = required(source.get(i), "source")?;
        let target = required(target.get(i), "target")?;
        let edge = RoadEdge::from_values(
            edge_id,
            speed.get(i),
            length.get(i),
            lanes.get(i),
            speed_density_type.get(i),
            speed_density_capacity.get(i),
            speed_density_min_density.get(i),
            speed_density_jam_density.get(i),
            speed_density_jam_speed.get(i),
            speed_density_beta.get(i),
            bottleneck_flow.get(i),
            bottleneck_flows.get(i),
            bottleneck_times.get(i),
            constant_travel_time.get(i),
            overtaking.get(i),
        )
        .with_context(|| format!("Failed to parse edge {edge_id}"))?;
        if !unique_ids.insert(edge_id) {
            bail!("Found duplicate `edge_id`: {edge_id}",);
        }
        edges.push((source, target, edge));
    }
    Ok((edges, unique_ids))
}

/// Reads an arrow `RecordBatch` with vehicles data and returns a `Vec` of `Vehicle`.
fn read_vehicles(batch: RecordBatch, edge_ids: HashSet<MetroId>) -> Result<Vec<Vehicle>> {
    let mut columns = Columns::new(batch);
    let vehicle_id = columns.id(&["vehicle_id"])?;
    let headway = columns.f64(&["headway"])?;
    let pce = columns.f64(&["pce"])?;
    let speed_function_type = columns.str(&["speed_function", "type"])?;
    let speed_function_upper_bound = columns.f64(&["speed_function", "upper_bound"])?;
    let speed_function_coef = columns.f64(&["speed_function", "coef"])?;
    let speed_function_x = columns.list_f64(&["speed_function", "x"])?;
    let speed_function_y = columns.list_f64(&["speed_function", "y"])?;
    let allowed_edges = columns.id_list(&["allowed_edges"])?;
    let restricted_edges = columns.id_list(&["restricted_edges"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut vehicles = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let vehicle_id = required(vehicle_id.get(i), "vehicle_id")?;
        let vehicle = Vehicle::from_values(
            vehicle_id,
            headway.get(i),
            pce.get(i),
            speed_function_type.get(i),
            speed_function_upper_bound.get(i),
            speed_function_coef.get(i),
            speed_function_x.get(i),
            speed_function_y.get(i),
            allowed_edges.get(i),
            restricted_edges.get(i),
            &edge_ids,
        )
        .with_context(|| format!("Failed to parse vehicle {vehicle_id}"))?;
        if !unique_ids.insert(vehicle_id) {
            bail!("Found duplicate `vehicle_id`: {vehicle_id}",);
        }
        vehicles.push(vehicle);
    }
    Ok(vehicles)
}

type RnWeightsVec = Vec<(
    MetroId,
    OriginalEdgeId,
    NonNegativeSeconds,
    NonNegativeSeconds,
)>;

/// Reads an arrow `RecordBatch` with road-network weights data and returns a [RnWeightsVec].
fn read_rn_weights(batch: RecordBatch) -> Result<RnWeightsVec> {
    let mut columns = Columns::new(batch);
    let vehicle_id = columns.id(&["vehicle_id"])?;
    let edge_id = columns.id(&["edge_id"])?;
    let departure_time = columns.f64(&["departure_time"])?;
    let travel_time = columns.f64(&["travel_time"])?;
    columns.warn_unused();
    (0..columns.len())
        .map(|i| {
            let vehicle_id = required(vehicle_id.get(i), "vehicle_id")?;
            let edge_id = required(edge_id.get(i), "edge_id")?;
            let departure_time =
                NonNegativeSeconds::try_from(required(departure_time.get(i), "departure_time")?)
                    .context("Value `departure_time` does not satisfy the constraints")?;
            let travel_time =
                NonNegativeSeconds::try_from(required(travel_time.get(i), "travel_time")?)
                    .context("Value `travel_time` does not satisfy the constraints")?;
            Ok((vehicle_id, edge_id, departure_time, travel_time))
        })
        .collect()
}

/// Reads an arrow `RecordBatch` with target routes data and returns a `Vec` of [TargetRoute].
fn read_target_routes(batch: RecordBatch) -> Result<Vec<TargetRoute>> {
    let mut columns = Columns::new(batch);
    let route_id = columns.id(&["route_id"])?;
    let departure_time = columns.f64(&["departure_time"])?;
    let target_delay = columns.f64(&["target_delay"])?;
    let path = columns.id_list(&["path"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut routes = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let route_id = required(route_id.get(i), "route_id")?;
        let route = TargetRoute::from_values(
            route_id,
            departure_time.get(i),
            target_delay.get(i),
            path.get(i),
        )
        .with_context(|| format!("Failed to parse target route {route_id}"))?;
        if !unique_ids.insert(route_id) {
            bail!("Found duplicate `route_id`: {route_id}",);
        }
        routes.push(route);
    }
    Ok(routes)
}

/// Reads an arrow `RecordBatch` with capacity-factors data and returns a `Vec` of [EdgeFactor].
fn read_capacity_factors(batch: RecordBatch) -> Result<Vec<EdgeFactor>> {
    let mut columns = Columns::new(batch);
    let edge_id = columns.id(&["edge_id"])?;
    let factor = columns.id(&["factor"])?;
    columns.warn_unused();
    (0..columns.len())
        .map(|i| {
            Ok(EdgeFactor {
                edge_id: required(edge_id.get(i), "edge_id")?,
                factor: required(factor.get(i), "factor")?,
            })
        })
        .collect()
}
