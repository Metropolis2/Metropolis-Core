// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Utility functions to work with arrow format.

use std::path::Path;
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use arrow::array::{
    new_null_array, Array, ArrayRef, AsArray, BooleanArray, BooleanBuilder, Float64Array,
    Float64Builder, ListArray, StringArray, StructArray, UInt64Array, UInt64Builder,
};
use arrow::compute::{cast_with_options, CastOptions};
use arrow::datatypes::{DataType, Field, FieldRef, Schema};
use arrow::record_batch::RecordBatch;
use hashbrown::{HashMap, HashSet};
use log::{info, warn};
use num_traits::{FromPrimitive, ToPrimitive};
use ttf::{TTFNum, TTF};

use crate::agent::Agent;
use crate::mode::trip::results::{LegTypeResults, PreDayLegTypeResults};
use crate::mode::trip::Leg;
use crate::mode::{Mode, ModeResults, PreDayModeResults};
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::vehicle::{OriginalVehicleId, Vehicle};
use crate::network::road_network::{OriginalEdgeId, RoadEdge, RoadNetwork, RoadNetworkWeights};
use crate::network::NetworkWeights;
use crate::simulation::results::{
    AgentResult, AgentResults, PreDayAgentResult, PreDayAgentResults,
};
use crate::units::{Interval, Time};

pub trait ToArrow<const J: usize> {
    fn to_arrow(data: &Self) -> Result<[Option<RecordBatch>; J]>;
    fn names() -> [&'static str; J];
}

/// Reads a road network from the filename of edges and vehicle types.
pub(crate) fn get_road_network_from_files<T: TTFNum>(
    edges_path: &Path,
    vehicle_path: &Path,
) -> Result<RoadNetwork<T>> {
    // Read edges parquet file.
    info!("Reading edges");
    let edge_batch = filename_to_batch_record(edges_path)?;
    let (edges, edge_ids) = read_edges(edge_batch).context("Cannot parse edges")?;
    // Read vehicles parquet file.
    info!("Reading vehicle types");
    let vehicle_batch = filename_to_batch_record(vehicle_path)?;
    let vehicles = read_vehicles(vehicle_batch, edge_ids).context("Cannot parse vehicles")?;
    Ok(RoadNetwork::from_edges(edges, vehicles))
}

/// Reads agents from the filename of agents, alternatives and trips.
pub(crate) fn get_agents_from_files<T: TTFNum>(
    agents_path: &Path,
    alts_path: &Path,
    trips_path: Option<&Path>,
) -> Result<Vec<Agent<T>>> {
    let trips = if let Some(filename) = trips_path {
        // Read trip file.
        info!("Reading trips");
        let trip_batch = filename_to_batch_record(filename)?;
        read_trips(trip_batch).context("Cannot parse trips")?
    } else {
        Default::default()
    };
    // Read alternatives parquet file.
    info!("Reading alternatives");
    let alt_batch = filename_to_batch_record(alts_path)?;
    let alternatives = read_alternatives(alt_batch, trips).context("Cannot parse alternatives")?;
    // Read agent parquet file.
    info!("Reading agents");
    let agent_batch = filename_to_batch_record(agents_path)?;
    let agents = read_agents(agent_batch, alternatives).context("Cannot parse agents")?;
    Ok(agents)
}

/// Reads [RoadNetworkWeights] from a filename.
pub(crate) fn get_road_network_weights_from_file<T: TTFNum>(
    path: &Path,
    period: Interval<T>,
    interval: Time<T>,
    road_network: &RoadNetwork<T>,
    unique_vehicles: &UniqueVehicles,
) -> Result<RoadNetworkWeights<T>> {
    info!("Reading road-network conditions");
    let batch = filename_to_batch_record(path)?;
    let rn_weights_vec = read_rn_weights(batch).context("Cannot parse road-network conditions")?;
    let rn_weights = RoadNetworkWeights::from_values(
        rn_weights_vec,
        period,
        interval,
        road_network,
        unique_vehicles,
    )
    .context("Invalid road-network conditions")?;
    Ok(rn_weights)
}

/// Reads a CSV or Parquet file as a [RecordBatch].
fn filename_to_batch_record(filename: &Path) -> Result<RecordBatch> {
    match filename.extension().and_then(|e| e.to_str()) {
        Some("parquet") => super::parquet::get_batch_record(filename),
        Some("csv") => super::csv::get_batch_record(filename),
        Some(_) | None => Err(anyhow!("Unrecognised file format: `{filename:?}`")),
    }
}

/// Returns a reference to the array corresponding to the column that matches the given names.
///
/// Returns `None` if the column cannot be found.
///
/// If `names` is `["a", "b"]`, the function searches for the columns with name `"a.b"` and `"a_b"`
/// or for a Struct column with name `"a"` and a subcolumn named `"b"`.
fn get_column(array: &StructArray, names: &[&str]) -> Option<ArrayRef> {
    debug_assert!(!names.is_empty());
    if let Some(array) = array.column_by_name(names[0]) {
        if names.len() == 1 {
            return Some(array.clone());
        }
        // Nested structure.
        if let Some(struct_array) = array.as_struct_opt() {
            if let Some(array) = get_column(struct_array, &names[1..]) {
                return Some(array);
            }
        } else {
            warn!(
                "Column `{}` exists but it is not of type `Struct`",
                names[0]
            );
        }
    }
    if names.len() == 1 {
        return None;
    }
    // Try to find the nested column as an non-nested column with a separator.
    let full_name = names.join(".");
    if let Some(array) = get_column(array, &[full_name.as_str()]) {
        return Some(array);
    }
    None
}

/// Casts the given array to a new data type, returning an error if the cast failed.
fn cast_column(array: &dyn Array, to_type: &DataType, names: &[&str]) -> Result<ArrayRef> {
    cast_with_options(
        array,
        to_type,
        &CastOptions {
            safe: false,
            ..Default::default()
        },
    )
    .with_context(|| {
        format!(
            "Cannot cast column `{}` from {} to {}",
            names.join("."),
            array.data_type(),
            to_type
        )
    })
}

/// Macro to get a column by name from an array and cast it to a specific datatype.
macro_rules! get_column {
    ([$($name:literal),+] in $array:ident as $ty:tt) => {
        get_column_inner!([$($name),+] in $array as type_to_array!($ty) | type_to_dtype!($ty))
    };
    ([$($name:literal),+] in $array:ident as List of $ty:tt) => {
        get_column_inner!([$($name),+] in $array as ListArray | get_list_dtype!($ty))
    };
}

macro_rules! type_to_dtype {
    (u64) => {
        DataType::UInt64
    };
    (f64) => {
        DataType::Float64
    };
    (str) => {
        DataType::Utf8
    };
    (bool) => {
        DataType::Boolean
    };
}

macro_rules! type_to_array {
    (u64) => {
        UInt64Array
    };
    (f64) => {
        Float64Array
    };
    (str) => {
        StringArray
    };
    (bool) => {
        BooleanArray
    };
}

macro_rules! get_list_dtype {
    ($ty:tt) => {
        DataType::new_list(type_to_dtype!($ty), false)
    };
}

macro_rules! get_column_inner {
    ([$($name:literal),+] in $array:ident as $out_array:ty | $dtype:expr) => {
        {
            let column = get_column(&$array, &[$($name),+])
                .unwrap_or_else(|| new_null_array(&$dtype, $array.len()));
            let casted_column = cast_column(&column, &$dtype, &[$($name),+])?;
            casted_column.as_any().downcast_ref::<$out_array>().unwrap().clone()
        }
    };
}

/// Macro to get a value at a given position from an array, or `None` if the value is `null`.
macro_rules! get_value {
    ($array:ident[$i:ident]) => {
        if $array.is_null($i) {
            None
        } else {
            Some($array.value($i))
        }
    };
}

/// Macro to get a list of values at a given position from a list array, or `None` if the list is
/// `null`.
macro_rules! get_list_values {
    ($array:ident[$i:ident] as $inner:tt) => {
        if $array.is_null($i) {
            None
        } else {
            // This downcast should be safe because the array was successfully casted to a List
            // of the inner data type?
            let list = $array.value($i);
            let list = list
                .as_any()
                .downcast_ref::<type_to_array!($inner)>()
                .unwrap();
            let values: Option<Vec<_>> = list.iter().collect();
            values
        }
    };
}

type LegMap<T> = HashMap<(usize, usize), Vec<Leg<T>>>;
type AltMap<T> = HashMap<usize, Vec<Mode<T>>>;

const TRIP_COLUMNS: [&str; 20] = [
    "agent_id",
    "alt_id",
    "trip_id",
    "class.type",
    "class.origin",
    "class.destination",
    "class.vehicle",
    "class.route",
    "class.travel_time",
    "stopping_time",
    "constant_utility",
    "travel_utility.one",
    "travel_utility.two",
    "travel_utility.three",
    "travel_utility.four",
    "schedule_utility.type",
    "schedule_utility.tstar",
    "schedule_utility.beta",
    "schedule_utility.gamma",
    "schedule_utility.delta",
];

/// Reads an arrow `RecordBatch` and returns a `HashMap` that maps `(agent_id, alt_id)` to a `Trip`.
pub(crate) fn read_trips<T: TTFNum>(batch: RecordBatch) -> Result<LegMap<T>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &TRIP_COLUMNS);
    let agent_id_values = get_column!(["agent_id"] in struct_array as u64);
    let alt_id_values = get_column!(["alt_id"] in struct_array as u64);
    let trip_id_values = get_column!(["trip_id"] in struct_array as u64);
    let class_type_values = get_column!(["class", "type"] in struct_array as str);
    let class_origin_values = get_column!(["class", "origin"] in struct_array as u64);
    let class_destination_values = get_column!(["class", "destination"] in struct_array as u64);
    let class_vehicle_values = get_column!(["class", "vehicle"] in struct_array as u64);
    let class_route_values = get_column!(["class", "route"] in struct_array as List of u64);
    let class_travel_time_values = get_column!(["class", "travel_time"] in struct_array as f64);
    let stopping_time_values = get_column!(["stopping_time"] in struct_array as f64);
    let constant_utility_values = get_column!(["constant_utility"] in struct_array as f64);
    let travel_utility_one_values = get_column!(["travel_utility", "one"] in struct_array as f64);
    let travel_utility_two_values = get_column!(["travel_utility", "two"] in struct_array as f64);
    let travel_utility_three_values =
        get_column!(["travel_utility", "three"] in struct_array as f64);
    let travel_utility_four_values = get_column!(["travel_utility", "four"] in struct_array as f64);
    let schedule_utility_type_values =
        get_column!(["schedule_utility", "type"] in struct_array as str);
    let schedule_utility_tstar_values =
        get_column!(["schedule_utility", "tstar"] in struct_array as f64);
    let schedule_utility_beta_values =
        get_column!(["schedule_utility", "beta"] in struct_array as f64);
    let schedule_utility_gamma_values =
        get_column!(["schedule_utility", "gamma"] in struct_array as f64);
    let schedule_utility_delta_values =
        get_column!(["schedule_utility", "delta"] in struct_array as f64);
    let n = struct_array.len();
    let mut trips: LegMap<T> = HashMap::with_capacity(n);
    let mut unique_tuples = HashSet::with_capacity(n);
    for i in 0..n {
        let agent_id = get_value!(agent_id_values[i]);
        let alt_id = get_value!(alt_id_values[i]);
        let trip_id = get_value!(trip_id_values[i]);
        let class_type = get_value!(class_type_values[i]);
        let class_origin = get_value!(class_origin_values[i]);
        let class_destination = get_value!(class_destination_values[i]);
        let class_vehicle = get_value!(class_vehicle_values[i]);
        let class_route = get_list_values!(class_route_values[i] as u64);
        let class_travel_time = get_value!(class_travel_time_values[i]);
        let stopping_time = get_value!(stopping_time_values[i]);
        let constant_utility = get_value!(constant_utility_values[i]);
        let travel_utility_one = get_value!(travel_utility_one_values[i]);
        let travel_utility_two = get_value!(travel_utility_two_values[i]);
        let travel_utility_three = get_value!(travel_utility_three_values[i]);
        let travel_utility_four = get_value!(travel_utility_four_values[i]);
        let schedule_utility_type = get_value!(schedule_utility_type_values[i]);
        let schedule_utility_tstar = get_value!(schedule_utility_tstar_values[i]);
        let schedule_utility_beta = get_value!(schedule_utility_beta_values[i]);
        let schedule_utility_gamma = get_value!(schedule_utility_gamma_values[i]);
        let schedule_utility_delta = get_value!(schedule_utility_delta_values[i]);
        let agent_id = agent_id
            .map(|id| id as usize)
            .ok_or_else(|| anyhow!("Value `agent_id` is mandatory"))?;
        let alt_id = alt_id
            .map(|id| id as usize)
            .ok_or_else(|| anyhow!("Value `alt_id` is mandatory"))?;
        let trip_id = trip_id
            .map(|id| id as usize)
            .ok_or_else(|| anyhow!("Value `trip_id` is mandatory"))?;
        let trip = Leg::from_values(
            trip_id,
            class_type,
            class_origin,
            class_destination,
            class_vehicle,
            class_route,
            class_travel_time,
            stopping_time,
            constant_utility,
            travel_utility_one,
            travel_utility_two,
            travel_utility_three,
            travel_utility_four,
            schedule_utility_type,
            schedule_utility_tstar,
            schedule_utility_beta,
            schedule_utility_gamma,
            schedule_utility_delta,
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

const ALTERNATIVE_COLUMNS: [&str; 28] = [
    "agent_id",
    "alt_id",
    "origin_delay",
    "dt_choice.type",
    "dt_choice.departure_time",
    "dt_choice.period",
    "dt_choice.interval",
    "dt_choice.offset",
    "dt_choice.model.type",
    "dt_choice.model.u",
    "dt_choice.model.mu",
    "dt_choice.model.constants",
    "constant_utility",
    "total_travel_utility.one",
    "total_travel_utility.two",
    "total_travel_utility.three",
    "total_travel_utility.four",
    "origin_utility.type",
    "origin_utility.tstar",
    "origin_utility.beta",
    "origin_utility.gamma",
    "origin_utility.delta",
    "destination_utility.type",
    "destination_utility.tstar",
    "destination_utility.beta",
    "destination_utility.gamma",
    "destination_utility.delta",
    "pre_compute_route",
];

/// Reads an arrow `RecordBatch` and returns a `HashMap` that maps `agent_id` to an `Alt`.
pub(crate) fn read_alternatives<T: TTFNum>(
    batch: RecordBatch,
    mut trips: LegMap<T>,
) -> Result<AltMap<T>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &ALTERNATIVE_COLUMNS);
    let agent_id_values = get_column!(["agent_id"] in struct_array as u64);
    let alt_id_values = get_column!(["alt_id"] in struct_array as u64);
    let origin_delay_values = get_column!(["origin_delay"] in struct_array as f64);
    let dt_choice_type_values = get_column!(["dt_choice", "type"] in struct_array as str);
    let dt_choice_departure_time_values =
        get_column!(["dt_choice", "departure_time"] in struct_array as f64);
    let dt_choice_period_values =
        get_column!(["dt_choice", "period"] in struct_array as List of f64);
    let dt_choice_interval_values = get_column!(["dt_choice", "interval"] in struct_array as f64);
    let dt_choice_offset_values = get_column!(["dt_choice", "offset"] in struct_array as f64);
    let dt_choice_model_type_values =
        get_column!(["dt_choice", "model", "type"] in struct_array as str);
    let dt_choice_model_u_values = get_column!(["dt_choice", "model", "u"] in struct_array as f64);
    let dt_choice_model_mu_values =
        get_column!(["dt_choice", "model", "mu"] in struct_array as f64);
    let dt_choice_model_constants_values =
        get_column!(["dt_choice", "model", "constants"] in struct_array as List of f64);
    let constant_utility_values = get_column!(["constant_utility"] in struct_array as f64);
    let total_travel_utility_one_values =
        get_column!(["total_travel_utility", "one"] in struct_array as f64);
    let total_travel_utility_two_values =
        get_column!(["total_travel_utility", "two"] in struct_array as f64);
    let total_travel_utility_three_values =
        get_column!(["total_travel_utility", "three"] in struct_array as f64);
    let total_travel_utility_four_values =
        get_column!(["total_travel_utility", "four"] in struct_array as f64);
    let origin_utility_type_values = get_column!(["origin_utility", "type"] in struct_array as str);
    let origin_utility_tstar_values =
        get_column!(["origin_utility", "tstar"] in struct_array as f64);
    let origin_utility_beta_values = get_column!(["origin_utility", "beta"] in struct_array as f64);
    let origin_utility_gamma_values =
        get_column!(["origin_utility", "gamma"] in struct_array as f64);
    let origin_utility_delta_values =
        get_column!(["origin_utility", "delta"] in struct_array as f64);
    let destination_utility_type_values =
        get_column!(["destination_utility", "type"] in struct_array as str);
    let destination_utility_tstar_values =
        get_column!(["destination_utility", "tstar"] in struct_array as f64);
    let destination_utility_beta_values =
        get_column!(["destination_utility", "beta"] in struct_array as f64);
    let destination_utility_gamma_values =
        get_column!(["destination_utility", "gamma"] in struct_array as f64);
    let destination_utility_delta_values =
        get_column!(["destination_utility", "delta"] in struct_array as f64);
    let pre_compute_route_values = get_column!(["pre_compute_route"] in struct_array as bool);
    let n = struct_array.len();
    let mut alternatives: AltMap<T> = HashMap::with_capacity(n);
    let mut unique_pairs = HashSet::with_capacity(n);
    for i in 0..n {
        let agent_id = get_value!(agent_id_values[i]);
        let alt_id = get_value!(alt_id_values[i]);
        let origin_delay = get_value!(origin_delay_values[i]);
        let dt_choice_type = get_value!(dt_choice_type_values[i]);
        let dt_choice_departure_time = get_value!(dt_choice_departure_time_values[i]);
        let dt_choice_period = get_list_values!(dt_choice_period_values[i] as f64);
        let dt_choice_interval = get_value!(dt_choice_interval_values[i]);
        let dt_choice_offset = get_value!(dt_choice_offset_values[i]);
        let dt_choice_model_type = get_value!(dt_choice_model_type_values[i]);
        let dt_choice_model_u = get_value!(dt_choice_model_u_values[i]);
        let dt_choice_model_mu = get_value!(dt_choice_model_mu_values[i]);
        let dt_choice_model_constants =
            get_list_values!(dt_choice_model_constants_values[i] as f64);
        let constant_utility = get_value!(constant_utility_values[i]);
        let total_travel_utility_one = get_value!(total_travel_utility_one_values[i]);
        let total_travel_utility_two = get_value!(total_travel_utility_two_values[i]);
        let total_travel_utility_three = get_value!(total_travel_utility_three_values[i]);
        let total_travel_utility_four = get_value!(total_travel_utility_four_values[i]);
        let origin_utility_type = get_value!(origin_utility_type_values[i]);
        let origin_utility_tstar = get_value!(origin_utility_tstar_values[i]);
        let origin_utility_beta = get_value!(origin_utility_beta_values[i]);
        let origin_utility_gamma = get_value!(origin_utility_gamma_values[i]);
        let origin_utility_delta = get_value!(origin_utility_delta_values[i]);
        let destination_utility_type = get_value!(destination_utility_type_values[i]);
        let destination_utility_tstar = get_value!(destination_utility_tstar_values[i]);
        let destination_utility_beta = get_value!(destination_utility_beta_values[i]);
        let destination_utility_gamma = get_value!(destination_utility_gamma_values[i]);
        let destination_utility_delta = get_value!(destination_utility_delta_values[i]);
        let pre_compute_route = get_value!(pre_compute_route_values[i]);
        let agent_id = agent_id
            .map(|id| id as usize)
            .ok_or_else(|| anyhow!("Value `agent_id` is mandatory"))?;
        let alt_id = alt_id
            .map(|id| id as usize)
            .ok_or_else(|| anyhow!("Value `alt_id` is mandatory"))?;
        let legs = trips.remove(&(agent_id, alt_id));
        let alt = Mode::from_values(
            alt_id,
            origin_delay,
            dt_choice_type,
            dt_choice_departure_time,
            dt_choice_period,
            dt_choice_interval,
            dt_choice_offset,
            dt_choice_model_type,
            dt_choice_model_u,
            dt_choice_model_mu,
            dt_choice_model_constants,
            constant_utility,
            total_travel_utility_one,
            total_travel_utility_two,
            total_travel_utility_three,
            total_travel_utility_four,
            origin_utility_type,
            origin_utility_tstar,
            origin_utility_beta,
            origin_utility_gamma,
            origin_utility_delta,
            destination_utility_type,
            destination_utility_tstar,
            destination_utility_beta,
            destination_utility_gamma,
            destination_utility_delta,
            pre_compute_route,
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

const AGENT_COLUMNS: [&str; 5] = [
    "agent_id",
    "alt_choice.type",
    "alt_choice.u",
    "alt_choice.mu",
    "alt_choice.constants",
];

/// Reads an arrow `RecordBatch` and returns a `Vec` of `Agent`.
pub(crate) fn read_agents<T: TTFNum>(
    batch: RecordBatch,
    mut alternatives: AltMap<T>,
) -> Result<Vec<Agent<T>>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &AGENT_COLUMNS);
    let agent_id_values = get_column!(["agent_id"] in struct_array as u64);
    let alt_choice_type_values = get_column!(["alt_choice", "type"] in struct_array as str);
    let alt_choice_u_values = get_column!(["alt_choice", "u"] in struct_array as f64);
    let alt_choice_mu_values = get_column!(["alt_choice", "mu"] in struct_array as f64);
    let alt_choice_constants_values =
        get_column!(["alt_choice", "constants"] in struct_array as List of f64);
    let n = struct_array.len();
    let mut agents = Vec::with_capacity(n);
    let mut unique_agent_ids = HashSet::with_capacity(n);
    for i in 0..n {
        let agent_id = get_value!(agent_id_values[i]);
        let alt_choice_type = get_value!(alt_choice_type_values[i]);
        let alt_choice_u = get_value!(alt_choice_u_values[i]);
        let alt_choice_mu = get_value!(alt_choice_mu_values[i]);
        let alt_choice_constants = get_list_values!(alt_choice_constants_values[i] as f64);
        let agent_id = agent_id
            .map(|id| id as usize)
            .ok_or_else(|| anyhow!("Value `agent_id` is mandatory"))?;
        let alts = alternatives.remove(&agent_id);
        let agent = Agent::from_values(
            agent_id,
            alt_choice_type,
            alt_choice_u,
            alt_choice_mu,
            alt_choice_constants,
            alts,
        )
        .with_context(|| format!("Failed to parse agent {agent_id}"))?;
        agents.push(agent);
        if !unique_agent_ids.insert(agent_id) {
            // agent_id value was already inserted.
            bail!("Found duplicate `agent_id`: {agent_id}",);
        }
    }
    Ok(agents)
}

const EDGE_COLUMNS: [&str; 15] = [
    "edge_id",
    "source",
    "target",
    "speed",
    "length",
    "lanes",
    "speed_density.type",
    "speed_density.capacity",
    "speed_density.min_density",
    "speed_density.jam_density",
    "speed_density.jam_speed",
    "speed_density.beta",
    "bottleneck_flow",
    "constant_travel_time",
    "overtaking",
];

type EdgeVec<T> = Vec<(u64, u64, RoadEdge<T>)>;

/// Reads an arrow `RecordBatch` with edges data and returns a `Vec` of `RoadEdge` and a `HashSet`
/// of unique edge ids.
pub(crate) fn read_edges<T: TTFNum>(batch: RecordBatch) -> Result<(EdgeVec<T>, HashSet<u64>)> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &EDGE_COLUMNS);
    let edge_id_values = get_column!(["edge_id"] in struct_array as u64);
    let source_values = get_column!(["source"] in struct_array as u64);
    let target_values = get_column!(["target"] in struct_array as u64);
    let speed_values = get_column!(["speed"] in struct_array as f64);
    let length_values = get_column!(["length"] in struct_array as f64);
    let lanes_values = get_column!(["lanes"] in struct_array as f64);
    let speed_density_type_values = get_column!(["speed_density", "type"] in struct_array as str);
    let speed_density_capacity_values =
        get_column!(["speed_density", "capacity"] in struct_array as f64);
    let speed_density_min_density_values =
        get_column!(["speed_density", "min_density"] in struct_array as f64);
    let speed_density_jam_density_values =
        get_column!(["speed_density", "jam_density"] in struct_array as f64);
    let speed_density_jam_speed_values =
        get_column!(["speed_density", "jam_speed"] in struct_array as f64);
    let speed_density_beta_values = get_column!(["speed_density", "beta"] in struct_array as f64);
    let bottleneck_flow_values = get_column!(["bottleneck_flow"] in struct_array as f64);
    let constant_travel_time_values = get_column!(["constant_travel_time"] in struct_array as f64);
    let overtaking_values = get_column!(["overtaking"] in struct_array as bool);
    let n = struct_array.len();
    let mut edges = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity(n);
    for i in 0..n {
        let edge_id = get_value!(edge_id_values[i]);
        let source = get_value!(source_values[i]);
        let target = get_value!(target_values[i]);
        let speed = get_value!(speed_values[i]);
        let length = get_value!(length_values[i]);
        let lanes = get_value!(lanes_values[i]);
        let speed_density_type = get_value!(speed_density_type_values[i]);
        let speed_density_capacity = get_value!(speed_density_capacity_values[i]);
        let speed_density_min_density = get_value!(speed_density_min_density_values[i]);
        let speed_density_jam_density = get_value!(speed_density_jam_density_values[i]);
        let speed_density_jam_speed = get_value!(speed_density_jam_speed_values[i]);
        let speed_density_beta = get_value!(speed_density_beta_values[i]);
        let bottleneck_flow = get_value!(bottleneck_flow_values[i]);
        let constant_travel_time = get_value!(constant_travel_time_values[i]);
        let overtaking = get_value!(overtaking_values[i]);
        let edge_id = edge_id.ok_or_else(|| anyhow!("Value `edge_id` is mandatory"))?;
        let source = source.ok_or_else(|| anyhow!("Value `source` is mandatory"))?;
        let target = target.ok_or_else(|| anyhow!("Value `target` is mandatory"))?;
        let edge = RoadEdge::from_values(
            edge_id,
            speed,
            length,
            lanes,
            speed_density_type,
            speed_density_capacity,
            speed_density_min_density,
            speed_density_jam_density,
            speed_density_jam_speed,
            speed_density_beta,
            bottleneck_flow,
            constant_travel_time,
            overtaking,
        )
        .with_context(|| format!("Failed to parse edge {edge_id}"))?;
        if !unique_ids.insert(edge_id) {
            bail!("Found duplicate `edge_id`: {edge_id}",);
        }
        edges.push((source, target, edge));
    }
    Ok((edges, unique_ids))
}

const VEHICLE_COLUMNS: [&str; 9] = [
    "vehicle_id",
    "headway",
    "pce",
    "speed_function.type",
    "speed_function.coef",
    "speed_function.x",
    "speed_function.y",
    "allowed_edges",
    "restricted_edges",
];

/// Reads an arrow `RecordBatch` with vehicles data and returns a `Vec` of `Vehicle`.
pub(crate) fn read_vehicles<T: TTFNum>(
    batch: RecordBatch,
    edge_ids: HashSet<u64>,
) -> Result<Vec<Vehicle<T>>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &VEHICLE_COLUMNS);
    let vehicle_id_values = get_column!(["vehicle_id"] in struct_array as u64);
    let headway_values = get_column!(["headway"] in struct_array as f64);
    let pce_values = get_column!(["pce"] in struct_array as f64);
    let speed_function_type_values = get_column!(["speed_function", "type"] in struct_array as str);
    let speed_function_coef_values = get_column!(["speed_function", "coef"] in struct_array as f64);
    let speed_function_x_values =
        get_column!(["speed_function", "x"] in struct_array as List of f64);
    let speed_function_y_values =
        get_column!(["speed_function", "y"] in struct_array as List of f64);
    let allowed_edges_values = get_column!(["allowed_edges"] in struct_array as List of u64);
    let restricted_edges_values = get_column!(["restricted_edges"] in struct_array as List of u64);
    let n = struct_array.len();
    let mut vehicles = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity(n);
    for i in 0..n {
        let vehicle_id = get_value!(vehicle_id_values[i]);
        let headway = get_value!(headway_values[i]);
        let pce = get_value!(pce_values[i]);
        let speed_function_type = get_value!(speed_function_type_values[i]);
        let speed_function_coef = get_value!(speed_function_coef_values[i]);
        let speed_function_x = get_list_values!(speed_function_x_values[i] as f64);
        let speed_function_y = get_list_values!(speed_function_y_values[i] as f64);
        let allowed_edges = get_list_values!(allowed_edges_values[i] as u64);
        let restricted_edges = get_list_values!(restricted_edges_values[i] as u64);
        let vehicle_id = vehicle_id.ok_or_else(|| anyhow!("Value `vehicle_id` is mandatory"))?;
        let vehicle = Vehicle::from_values(
            vehicle_id,
            headway,
            pce,
            speed_function_type,
            speed_function_coef,
            speed_function_x,
            speed_function_y,
            allowed_edges,
            restricted_edges,
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

const RN_WEIGHTS_COLUMNS: [&str; 4] = ["vehicle_id", "edge_id", "departure_time", "travel_time"];

type RnWeightsVec<T> = Vec<(OriginalVehicleId, OriginalEdgeId, Time<T>, Time<T>)>;

/// Reads an arrow `RecordBatch` with road-network weights data and returns a [RoadNetworkWeights].
pub(crate) fn read_rn_weights<T: TTFNum>(batch: RecordBatch) -> Result<RnWeightsVec<T>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &RN_WEIGHTS_COLUMNS);
    let vehicle_id_values = get_column!(["vehicle_id"] in struct_array as u64);
    let edge_id_values = get_column!(["edge_id"] in struct_array as u64);
    let departure_time_values = get_column!(["departure_time"] in struct_array as f64);
    let travel_time_values = get_column!(["travel_time"] in struct_array as f64);
    let n = struct_array.len();
    let mut weights = Vec::with_capacity(n);
    for i in 0..n {
        let vehicle_id = get_value!(vehicle_id_values[i]);
        let edge_id = get_value!(edge_id_values[i]);
        let departure_time = get_value!(departure_time_values[i]);
        let travel_time = get_value!(travel_time_values[i]);
        let vehicle_id = vehicle_id.ok_or_else(|| anyhow!("Value `vehicle_id` is mandatory"))?;
        let edge_id = edge_id.ok_or_else(|| anyhow!("Value `edge_id` is mandatory"))?;
        let departure_time = Time::from_f64(
            departure_time.ok_or_else(|| anyhow!("Value `departure_time` is mandatory"))?,
        )
        .unwrap();
        let travel_time =
            Time::from_f64(travel_time.ok_or_else(|| anyhow!("Value `travel_time` is mandatory"))?)
                .unwrap();
        weights.push((vehicle_id, edge_id, departure_time, travel_time));
    }
    Ok(weights)
}

/// Sends warnings for unused columns.
fn warn_unused_columns(array: &StructArray, columns: &[&str]) {
    let columns_set: HashSet<&str> = columns.iter().copied().collect();
    for field in array.fields() {
        check_unused_column(field, &columns_set, vec![]);
    }
}

fn check_unused_column(field: &FieldRef, columns: &HashSet<&str>, mut prefix: Vec<String>) {
    match field.data_type() {
        DataType::Struct(struct_field) => {
            prefix.push(field.name().to_owned());
            for subfield in struct_field {
                check_unused_column(subfield, columns, prefix.clone())
            }
        }
        _ => {
            let full_name = if prefix.is_empty() {
                field.name().to_owned()
            } else {
                format!("{}.{}", prefix.join("."), field.name())
            };
            if !columns.contains(full_name.as_str()) {
                warn!("Unknown column `{}`", full_name);
            }
        }
    }
}

#[derive(Debug, Default)]
struct AgentResultsBuilder {
    // Values at the agent level.
    id: UInt64Builder,
    mode_id: UInt64Builder,
    expected_utility: Float64Builder,
    shifted_mode: BooleanBuilder,
    departure_time: Float64Builder,
    arrival_time: Float64Builder,
    total_travel_time: Float64Builder,
    utility: Float64Builder,
    mode_expected_utility: Float64Builder,
    departure_time_shift: Float64Builder,
    nb_road_legs: UInt64Builder,
    nb_virtual_legs: UInt64Builder,
    // Values at the leg level.
    leg_agent_id: UInt64Builder,
    leg_id: UInt64Builder,
    leg_index: UInt64Builder,
    leg_departure_time: Float64Builder,
    leg_arrival_time: Float64Builder,
    leg_travel_utility: Float64Builder,
    leg_schedule_utility: Float64Builder,
    leg_departure_time_shift: Float64Builder,
    leg_road_time: Float64Builder,
    leg_in_bottleneck_time: Float64Builder,
    leg_out_bottleneck_time: Float64Builder,
    leg_route_free_flow_travel_time: Float64Builder,
    leg_global_free_flow_travel_time: Float64Builder,
    leg_length: Float64Builder,
    leg_length_diff: Float64Builder,
    leg_pre_exp_departure_time: Float64Builder,
    leg_pre_exp_arrival_time: Float64Builder,
    leg_exp_arrival_time: Float64Builder,
    leg_nb_edges: UInt64Builder,
    // Values at the route level.
    route_agent_id: UInt64Builder,
    route_leg_id: UInt64Builder,
    route_leg_index: UInt64Builder,
    route_edge_id: UInt64Builder,
    route_entry_time: Float64Builder,
    route_exit_time: Float64Builder,
}

impl AgentResultsBuilder {
    fn append<T: ToPrimitive>(&mut self, agent_result: &AgentResult<T>) {
        self.id.append_value(agent_result.id as u64);
        self.mode_id.append_value(agent_result.mode_id as u64);
        self.expected_utility
            .append_value(agent_result.expected_utility.to_f64().unwrap());
        self.shifted_mode.append_value(agent_result.shifted_mode);
        match &agent_result.mode_results {
            ModeResults::Trip(trip) => {
                self.departure_time
                    .append_value(trip.departure_time.to_f64().unwrap());
                self.arrival_time
                    .append_value(trip.arrival_time.to_f64().unwrap());
                self.total_travel_time
                    .append_value(trip.total_travel_time.to_f64().unwrap());
                self.utility.append_value(trip.utility.to_f64().unwrap());
                self.mode_expected_utility
                    .append_value(trip.expected_utility.to_f64().unwrap());
                if let Some(dts) = trip.departure_time_shift.as_ref() {
                    self.departure_time_shift
                        .append_value(dts.to_f64().unwrap());
                } else {
                    self.departure_time_shift.append_null()
                }
                let mut nb_road_legs = 0;
                let mut nb_virtual_legs = 0;
                for (i, leg) in trip.legs.iter().enumerate() {
                    self.leg_agent_id.append_value(agent_result.id as u64);
                    self.leg_id.append_value(leg.id as u64);
                    self.leg_index.append_value(i as u64);
                    self.leg_departure_time
                        .append_value(leg.departure_time.to_f64().unwrap());
                    self.leg_arrival_time
                        .append_value(leg.arrival_time.to_f64().unwrap());
                    self.leg_travel_utility
                        .append_value(leg.travel_utility.to_f64().unwrap());
                    self.leg_schedule_utility
                        .append_value(leg.schedule_utility.to_f64().unwrap());
                    if let Some(dts) = leg.departure_time_shift.as_ref() {
                        self.leg_departure_time_shift
                            .append_value(dts.to_f64().unwrap());
                    } else {
                        self.leg_departure_time_shift.append_null();
                    }
                    if let LegTypeResults::Road(road_leg) = &leg.class {
                        nb_road_legs += 1;
                        self.leg_road_time
                            .append_value(road_leg.road_time.to_f64().unwrap());
                        self.leg_in_bottleneck_time
                            .append_value(road_leg.in_bottleneck_time.to_f64().unwrap());
                        self.leg_out_bottleneck_time
                            .append_value(road_leg.out_bottleneck_time.to_f64().unwrap());
                        self.leg_route_free_flow_travel_time
                            .append_value(road_leg.route_free_flow_travel_time.to_f64().unwrap());
                        self.leg_global_free_flow_travel_time
                            .append_value(road_leg.global_free_flow_travel_time.to_f64().unwrap());
                        self.leg_length
                            .append_value(road_leg.length.to_f64().unwrap());
                        if let Some(ld) = road_leg.length_diff.as_ref() {
                            self.leg_length_diff.append_value(ld.to_f64().unwrap());
                        } else {
                            self.leg_length_diff.append_null();
                        }
                        self.leg_pre_exp_departure_time
                            .append_value(road_leg.pre_exp_departure_time.to_f64().unwrap());
                        self.leg_pre_exp_arrival_time
                            .append_value(road_leg.pre_exp_arrival_time.to_f64().unwrap());
                        self.leg_exp_arrival_time
                            .append_value(road_leg.exp_arrival_time.to_f64().unwrap());
                        self.leg_nb_edges.append_value(road_leg.route.len() as u64);
                        for window in road_leg.route.windows(2) {
                            let event = &window[0];
                            let next_event = &window[1];
                            self.route_agent_id.append_value(agent_result.id as u64);
                            self.route_leg_id.append_value(leg.id as u64);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(event.edge);
                            self.route_entry_time
                                .append_value(event.entry_time.to_f64().unwrap());
                            self.route_exit_time
                                .append_value(next_event.entry_time.to_f64().unwrap());
                        }
                        // The last event is not added by the previous for loop.
                        if let Some(last_event) = road_leg.route.last() {
                            self.route_agent_id.append_value(agent_result.id as u64);
                            self.route_leg_id.append_value(leg.id as u64);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(last_event.edge);
                            self.route_entry_time
                                .append_value(last_event.entry_time.to_f64().unwrap());
                            self.route_exit_time
                                .append_value(leg.arrival_time.to_f64().unwrap());
                        }
                    } else {
                        nb_virtual_legs += 1;
                        self.leg_road_time.append_null();
                        self.leg_in_bottleneck_time.append_null();
                        self.leg_out_bottleneck_time.append_null();
                        self.leg_route_free_flow_travel_time.append_null();
                        self.leg_global_free_flow_travel_time.append_null();
                        self.leg_length.append_null();
                        self.leg_length_diff.append_null();
                        self.leg_pre_exp_departure_time.append_null();
                        self.leg_pre_exp_arrival_time.append_null();
                        self.leg_exp_arrival_time.append_null();
                        self.leg_nb_edges.append_null();
                    }
                }
                self.nb_road_legs.append_value(nb_road_legs);
                self.nb_virtual_legs.append_value(nb_virtual_legs);
            }
            ModeResults::Constant(utility) => {
                self.departure_time.append_null();
                self.arrival_time.append_null();
                self.total_travel_time.append_null();
                self.utility.append_value(utility.to_f64().unwrap());
                self.mode_expected_utility
                    .append_value(utility.to_f64().unwrap());
                self.departure_time_shift.append_null();
                self.nb_road_legs.append_null();
                self.nb_virtual_legs.append_null();
            }
        }
    }

    fn finish(&mut self) -> Result<[Option<RecordBatch>; 3]> {
        let agent_schema = Schema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("selected_alt_id", DataType::UInt64, false),
            Field::new("expected_utility", DataType::Float64, false),
            Field::new("shifted_alt", DataType::Boolean, false),
            Field::new("departure_time", DataType::Float64, true),
            Field::new("arrival_time", DataType::Float64, true),
            Field::new("total_travel_time", DataType::Float64, true),
            Field::new("utility", DataType::Float64, true),
            Field::new("alt_expected_utility", DataType::Float64, true),
            Field::new("departure_time_shift", DataType::Float64, true),
            Field::new("nb_road_trips", DataType::UInt64, true),
            Field::new("nb_virtual_trips", DataType::UInt64, true),
        ]);
        let agent_batch = RecordBatch::try_new(
            Arc::new(agent_schema),
            vec![
                Arc::new(self.id.finish()),
                Arc::new(self.mode_id.finish()),
                Arc::new(self.expected_utility.finish()),
                Arc::new(self.shifted_mode.finish()),
                Arc::new(self.departure_time.finish()),
                Arc::new(self.arrival_time.finish()),
                Arc::new(self.total_travel_time.finish()),
                Arc::new(self.utility.finish()),
                Arc::new(self.mode_expected_utility.finish()),
                Arc::new(self.departure_time_shift.finish()),
                Arc::new(self.nb_road_legs.finish()),
                Arc::new(self.nb_virtual_legs.finish()),
            ],
        )?;
        let leg_schema = Schema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("trip_id", DataType::UInt64, false),
            Field::new("trip_index", DataType::UInt64, false),
            Field::new("departure_time", DataType::Float64, false),
            Field::new("arrival_time", DataType::Float64, false),
            Field::new("travel_utility", DataType::Float64, false),
            Field::new("schedule_utility", DataType::Float64, false),
            Field::new("departure_time_shift", DataType::Float64, true),
            Field::new("road_time", DataType::Float64, true),
            Field::new("in_bottleneck_time", DataType::Float64, true),
            Field::new("out_bottleneck_time", DataType::Float64, true),
            Field::new("route_free_flow_travel_time", DataType::Float64, true),
            Field::new("global_free_flow_travel_time", DataType::Float64, true),
            Field::new("length", DataType::Float64, true),
            Field::new("length_diff", DataType::Float64, true),
            Field::new("pre_exp_departure_time", DataType::Float64, true),
            Field::new("pre_exp_arrival_time", DataType::Float64, true),
            Field::new("exp_arrival_time", DataType::Float64, true),
            Field::new("nb_edges", DataType::UInt64, true),
        ]);
        let leg_batch = RecordBatch::try_new(
            Arc::new(leg_schema),
            vec![
                Arc::new(self.leg_agent_id.finish()),
                Arc::new(self.leg_id.finish()),
                Arc::new(self.leg_index.finish()),
                Arc::new(self.leg_departure_time.finish()),
                Arc::new(self.leg_arrival_time.finish()),
                Arc::new(self.leg_travel_utility.finish()),
                Arc::new(self.leg_schedule_utility.finish()),
                Arc::new(self.leg_departure_time_shift.finish()),
                Arc::new(self.leg_road_time.finish()),
                Arc::new(self.leg_in_bottleneck_time.finish()),
                Arc::new(self.leg_out_bottleneck_time.finish()),
                Arc::new(self.leg_route_free_flow_travel_time.finish()),
                Arc::new(self.leg_global_free_flow_travel_time.finish()),
                Arc::new(self.leg_length.finish()),
                Arc::new(self.leg_length_diff.finish()),
                Arc::new(self.leg_pre_exp_departure_time.finish()),
                Arc::new(self.leg_pre_exp_arrival_time.finish()),
                Arc::new(self.leg_exp_arrival_time.finish()),
                Arc::new(self.leg_nb_edges.finish()),
            ],
        )?;
        let route_schema = Schema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("trip_id", DataType::UInt64, false),
            Field::new("trip_index", DataType::UInt64, false),
            Field::new("edge_id", DataType::UInt64, false),
            Field::new("entry_time", DataType::Float64, false),
            Field::new("exit_time", DataType::Float64, false),
        ]);
        let route_batch = RecordBatch::try_new(
            Arc::new(route_schema),
            vec![
                Arc::new(self.route_agent_id.finish()),
                Arc::new(self.route_leg_id.finish()),
                Arc::new(self.route_leg_index.finish()),
                Arc::new(self.route_edge_id.finish()),
                Arc::new(self.route_entry_time.finish()),
                Arc::new(self.route_exit_time.finish()),
            ],
        )?;
        let batch0 = if agent_batch.num_rows() == 0 {
            None
        } else {
            Some(agent_batch)
        };
        let batch1 = if leg_batch.num_rows() == 0 {
            None
        } else {
            Some(leg_batch)
        };
        let batch2 = if route_batch.num_rows() == 0 {
            None
        } else {
            Some(route_batch)
        };
        Ok([batch0, batch1, batch2])
    }
}

impl<T: ToPrimitive> ToArrow<3> for AgentResults<T> {
    fn to_arrow(data: &AgentResults<T>) -> Result<[Option<RecordBatch>; 3]> {
        let mut builder = AgentResultsBuilder::default();
        data.0.iter().for_each(|row| builder.append(row));
        builder.finish()
    }
    fn names() -> [&'static str; 3] {
        ["agent_results", "trip_results", "route_results"]
    }
}

#[derive(Debug, Default)]
struct PreDayAgentResultsBuilder {
    // Values at the agent level.
    id: UInt64Builder,
    mode_id: UInt64Builder,
    expected_utility: Float64Builder,
    departure_time: Float64Builder,
    mode_expected_utility: Float64Builder,
    nb_road_legs: UInt64Builder,
    nb_virtual_legs: UInt64Builder,
    // Values at the leg level.
    leg_agent_id: UInt64Builder,
    leg_id: UInt64Builder,
    leg_index: UInt64Builder,
    leg_route_free_flow_travel_time: Float64Builder,
    leg_global_free_flow_travel_time: Float64Builder,
    leg_length: Float64Builder,
    leg_pre_exp_departure_time: Float64Builder,
    leg_pre_exp_arrival_time: Float64Builder,
    leg_nb_edges: UInt64Builder,
    // Values at the route level.
    route_agent_id: UInt64Builder,
    route_leg_id: UInt64Builder,
    route_leg_index: UInt64Builder,
    route_edge_id: UInt64Builder,
    route_entry_time: Float64Builder,
    route_exit_time: Float64Builder,
}

impl PreDayAgentResultsBuilder {
    fn append<T: ToPrimitive>(&mut self, agent_result: &PreDayAgentResult<T>) {
        self.id.append_value(agent_result.id as u64);
        self.mode_id.append_value(agent_result.mode_id as u64);
        self.expected_utility
            .append_value(agent_result.expected_utility.to_f64().unwrap());
        match &agent_result.mode_results {
            PreDayModeResults::Trip(trip) => {
                self.departure_time
                    .append_value(trip.departure_time.to_f64().unwrap());
                self.mode_expected_utility
                    .append_value(trip.expected_utility.to_f64().unwrap());
                let mut nb_road_legs = 0;
                let mut nb_virtual_legs = 0;
                for (i, leg) in trip.legs.iter().enumerate() {
                    self.leg_agent_id.append_value(agent_result.id as u64);
                    self.leg_id.append_value(leg.id as u64);
                    self.leg_index.append_value(i as u64);
                    if let PreDayLegTypeResults::Road(road_leg) = &leg.class {
                        nb_road_legs += 1;
                        self.leg_route_free_flow_travel_time
                            .append_value(road_leg.route_free_flow_travel_time.to_f64().unwrap());
                        self.leg_global_free_flow_travel_time
                            .append_value(road_leg.global_free_flow_travel_time.to_f64().unwrap());
                        self.leg_length
                            .append_value(road_leg.length.to_f64().unwrap());
                        self.leg_pre_exp_departure_time
                            .append_value(road_leg.pre_exp_departure_time.to_f64().unwrap());
                        self.leg_pre_exp_arrival_time
                            .append_value(road_leg.pre_exp_arrival_time.to_f64().unwrap());
                        self.leg_nb_edges.append_value(road_leg.route.len() as u64);
                        for window in road_leg.route.windows(2) {
                            let event = &window[0];
                            let next_event = &window[1];
                            self.route_agent_id.append_value(agent_result.id as u64);
                            self.route_leg_id.append_value(leg.id as u64);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(event.edge);
                            self.route_entry_time
                                .append_value(event.entry_time.to_f64().unwrap());
                            self.route_exit_time
                                .append_value(next_event.entry_time.to_f64().unwrap());
                        }
                        // The last event is not added by the previous for loop.
                        if let Some(last_event) = road_leg.route.last() {
                            self.route_agent_id.append_value(agent_result.id as u64);
                            self.route_leg_id.append_value(leg.id as u64);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(last_event.edge);
                            self.route_entry_time
                                .append_value(last_event.entry_time.to_f64().unwrap());
                            self.route_exit_time
                                .append_value(road_leg.pre_exp_arrival_time.to_f64().unwrap());
                        }
                    } else {
                        nb_virtual_legs += 1;
                        self.leg_route_free_flow_travel_time.append_null();
                        self.leg_global_free_flow_travel_time.append_null();
                        self.leg_length.append_null();
                        self.leg_pre_exp_departure_time.append_null();
                        self.leg_pre_exp_arrival_time.append_null();
                        self.leg_nb_edges.append_null();
                    }
                }
                self.nb_road_legs.append_value(nb_road_legs);
                self.nb_virtual_legs.append_value(nb_virtual_legs);
            }
            PreDayModeResults::Constant(utility) => {
                self.departure_time.append_null();
                self.mode_expected_utility
                    .append_value(utility.to_f64().unwrap());
                self.nb_road_legs.append_null();
                self.nb_virtual_legs.append_null();
            }
        }
    }

    fn finish(&mut self) -> Result<[Option<RecordBatch>; 3]> {
        let agent_schema = Schema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("selected_alt_id", DataType::UInt64, false),
            Field::new("expected_utility", DataType::Float64, false),
            Field::new("departure_time", DataType::Float64, true),
            Field::new("alt_expected_utility", DataType::Float64, true),
            Field::new("nb_road_trips", DataType::UInt64, true),
            Field::new("nb_virtual_trips", DataType::UInt64, true),
        ]);
        let agent_batch = RecordBatch::try_new(
            Arc::new(agent_schema),
            vec![
                Arc::new(self.id.finish()),
                Arc::new(self.mode_id.finish()),
                Arc::new(self.expected_utility.finish()),
                Arc::new(self.departure_time.finish()),
                Arc::new(self.mode_expected_utility.finish()),
                Arc::new(self.nb_road_legs.finish()),
                Arc::new(self.nb_virtual_legs.finish()),
            ],
        )?;
        let leg_schema = Schema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("leg_id", DataType::UInt64, false),
            Field::new("leg_index", DataType::UInt64, false),
            Field::new("route_free_flow_travel_time", DataType::Float64, true),
            Field::new("global_free_flow_travel_time", DataType::Float64, true),
            Field::new("length", DataType::Float64, true),
            Field::new("pre_exp_departure_time", DataType::Float64, true),
            Field::new("pre_exp_arrival_time", DataType::Float64, true),
            Field::new("nb_edges", DataType::UInt64, true),
        ]);
        let leg_batch = RecordBatch::try_new(
            Arc::new(leg_schema),
            vec![
                Arc::new(self.leg_agent_id.finish()),
                Arc::new(self.leg_id.finish()),
                Arc::new(self.leg_index.finish()),
                Arc::new(self.leg_route_free_flow_travel_time.finish()),
                Arc::new(self.leg_global_free_flow_travel_time.finish()),
                Arc::new(self.leg_length.finish()),
                Arc::new(self.leg_pre_exp_departure_time.finish()),
                Arc::new(self.leg_pre_exp_arrival_time.finish()),
                Arc::new(self.leg_nb_edges.finish()),
            ],
        )?;
        let route_schema = Schema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("leg_id", DataType::UInt64, false),
            Field::new("leg_index", DataType::UInt64, false),
            Field::new("edge_id", DataType::UInt64, false),
            Field::new("entry_time", DataType::Float64, false),
            Field::new("exit_time", DataType::Float64, false),
        ]);
        let route_batch = RecordBatch::try_new(
            Arc::new(route_schema),
            vec![
                Arc::new(self.route_agent_id.finish()),
                Arc::new(self.route_leg_id.finish()),
                Arc::new(self.route_leg_index.finish()),
                Arc::new(self.route_edge_id.finish()),
                Arc::new(self.route_entry_time.finish()),
                Arc::new(self.route_exit_time.finish()),
            ],
        )?;
        let batch0 = if agent_batch.num_rows() == 0 {
            None
        } else {
            Some(agent_batch)
        };
        let batch1 = if leg_batch.num_rows() == 0 {
            None
        } else {
            Some(leg_batch)
        };
        let batch2 = if route_batch.num_rows() == 0 {
            None
        } else {
            Some(route_batch)
        };
        Ok([batch0, batch1, batch2])
    }
}

impl<T: ToPrimitive> ToArrow<3> for PreDayAgentResults<T> {
    fn to_arrow(data: &PreDayAgentResults<T>) -> Result<[Option<RecordBatch>; 3]> {
        let mut builder = PreDayAgentResultsBuilder::default();
        data.0.iter().for_each(|row| builder.append(row));
        builder.finish()
    }
    fn names() -> [&'static str; 3] {
        ["agent_results", "trip_results", "route_results"]
    }
}

#[derive(Debug)]
struct RoadNetworkWeightsBuilder<T> {
    period: Interval<T>,
    interval: Time<T>,
    vehicle_id: UInt64Builder,
    edge_id: UInt64Builder,
    departure_time: Float64Builder,
    travel_time: Float64Builder,
}

impl<T> RoadNetworkWeightsBuilder<T> {
    fn new(period: Interval<T>, interval: Time<T>) -> Self {
        Self {
            period,
            interval,
            vehicle_id: Default::default(),
            edge_id: Default::default(),
            departure_time: Default::default(),
            travel_time: Default::default(),
        }
    }
}

impl<T: TTFNum> RoadNetworkWeightsBuilder<T> {
    fn append(&mut self, vehicle_id: OriginalVehicleId, edge_id: u64, ttf: &TTF<Time<T>>) {
        let xs_iter =
            std::iter::successors(Some(self.period.start()), |&t| Some(t + self.interval))
                .take_while(|&t| t < self.period.end());
        for (x, y) in xs_iter.map(|x| (x, ttf.eval(x))) {
            self.vehicle_id.append_value(vehicle_id);
            self.edge_id.append_value(edge_id);
            self.departure_time.append_value(x.to_f64().unwrap());
            self.travel_time.append_value(y.to_f64().unwrap());
        }
    }

    fn finish(&mut self) -> Result<[Option<RecordBatch>; 1]> {
        let schema = Schema::new(vec![
            Field::new("vehicle_id", DataType::UInt64, false),
            Field::new("edge_id", DataType::UInt64, false),
            Field::new("departure_time", DataType::Float64, false),
            Field::new("travel_time", DataType::Float64, true),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(self.vehicle_id.finish()),
                Arc::new(self.edge_id.finish()),
                Arc::new(self.departure_time.finish()),
                Arc::new(self.travel_time.finish()),
            ],
        )?;
        if batch.num_rows() == 0 {
            Ok([None])
        } else {
            Ok([Some(batch)])
        }
    }
}

impl<T: TTFNum> ToArrow<1> for NetworkWeights<T> {
    fn to_arrow(data: &NetworkWeights<T>) -> Result<[Option<RecordBatch>; 1]> {
        if let Some(rn_weights) = data.road_network() {
            let mut builder =
                RoadNetworkWeightsBuilder::new(rn_weights.period, rn_weights.interval);
            for vehicle_weights in rn_weights.iter() {
                for vehicle_id in vehicle_weights.vehicle_ids() {
                    for (edge_id, ttf) in vehicle_weights.weights().iter() {
                        builder.append(*vehicle_id, *edge_id, ttf);
                    }
                }
            }
            builder.finish()
        } else {
            Ok([None])
        }
    }
    fn names() -> [&'static str; 1] {
        ["edge_ttfs"]
    }
}
