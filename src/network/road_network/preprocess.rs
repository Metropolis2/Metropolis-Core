// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs and functions to pre-process a [RoadNetwork].
use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use num_traits::ToPrimitive;
use petgraph::prelude::NodeIndex;
use serde::Deserialize;
use ttf::TTFNum;

use super::vehicle::{vehicle_index, Vehicle, VehicleIndex};
use super::{RoadNetwork, RoadNetworkParameters};
use crate::agent::Agent;
use crate::mode::Mode;
use crate::units::{Interval, Time};

/// Struct to store the set of unique vehicles and the equivalences between vehicles.
#[derive(Clone, Debug)]
struct UniqueVehicles {
    /// List all the vehicles for which [RoadNetworkWeights] and [RoadNetworkSkims] are computed.
    vehicles: Vec<VehicleIndex>,
    /// Map each vehicle to the corresponding id to use for [RoadNetworkWeights] and
    /// [RoadNetworkSkims].
    vehicle_map: HashMap<VehicleIndex, usize>,
}

impl UniqueVehicles {
    /// Creates a new [UniqueVehicles] from a Vec of [Vehicle].
    fn from_vehicles<T: TTFNum>(vehicles: &[Vehicle<T>]) -> Self {
        let mut unique_vehicles: Vec<VehicleIndex> = Vec::new();
        let mut vehicle_map = HashMap::with_capacity(vehicles.len());
        for (vehicle_id, vehicle) in vehicles.iter().enumerate() {
            if let Some(id) = unique_vehicles
                .iter()
                .find(|&id| vehicle.share_weights(&vehicles[id.index()]))
            {
                vehicle_map.insert(vehicle_index(vehicle_id), id.index());
            } else {
                unique_vehicles.push(vehicle_index(vehicle_id));
                vehicle_map.insert(vehicle_index(vehicle_id), unique_vehicles.len() - 1);
            }
        }
        UniqueVehicles {
            vehicles: unique_vehicles,
            vehicle_map,
        }
    }

    /// Returns the number of unique vehicles.
    fn len(&self) -> usize {
        self.vehicles.len()
    }
}

impl Default for UniqueVehicles {
    fn default() -> Self {
        Self {
            vehicles: vec![vehicle_index(0)],
            vehicle_map: [(vehicle_index(0), 0)].into_iter().collect(),
        }
    }
}

/// Set of pre-processing data used for different road-network computation.
#[derive(Clone, Debug, Default)]
pub struct RoadNetworkPreprocessingData<T> {
    /// Set of unique vehicles.
    unique_vehicles: UniqueVehicles,
    /// Vector with, for each unique vehicle, an [ODPairs] instance representing the
    /// origin-destination pairs for which at least one agent can make a trip with this vehicle.
    od_pairs: Vec<ODPairs>,
    /// Time intervals for which the simulated travel times are aggregated.
    recording_intervals: Vec<Time<T>>,
}

impl<T> RoadNetworkPreprocessingData<T> {
    /// Returns the number of unique vehicles.
    pub fn nb_unique_vehicles(&self) -> usize {
        self.unique_vehicles.len()
    }

    /// Returns the unique-vehicle index corresponding to the given [VehicleIndex].
    ///
    /// *Panics* if the given [VehicleIndex] is out-of-bound for this
    /// [RoadNetworkPreprocessingData].
    pub fn get_unique_vehicle_index(&self, id: VehicleIndex) -> usize {
        self.unique_vehicles.vehicle_map[&id]
    }

    /// Returns the [VehicleIndex] corresponding to the given unique-vehicle index.
    ///
    /// *Panics* if the given unique-vehicle index is out-of-bound for this
    /// [RoadNetworkPreprocessingData].
    pub fn get_vehicle_index(&self, id: usize) -> VehicleIndex {
        self.unique_vehicles.vehicles[id]
    }

    /// Iterates over the unique vehicles' ids and [Vehicle].
    pub fn iter_unique_vehicles<'a>(
        &'a self,
        vehicles: &'a [Vehicle<T>],
    ) -> impl Iterator<Item = (usize, &'a Vehicle<T>)> {
        self.unique_vehicles
            .vehicles
            .iter()
            .map(|v_id| &vehicles[v_id.index()])
            .enumerate()
    }

    /// Returns the slice of recording interval to use.
    pub fn recording_intervals(&self) -> &[Time<T>] {
        &self.recording_intervals
    }

    /// Returns the [ODPairs] corresponding to the given unique-vehicle index.
    ///
    /// *Panics* if the unique-vehicle index exceeds the number of unique vehicle of this
    /// [RoadNetworkPreprocessingData].
    pub fn od_pairs(&self, uvehicle_id: usize) -> &ODPairs {
        &self.od_pairs[uvehicle_id]
    }
}

impl<T: TTFNum> RoadNetworkPreprocessingData<T> {
    /// Computes pre-processed data for a [RoadNetwork], given the list of [Agent], the
    /// [RoadNetworkParameters] and the simulation interval.
    pub fn preprocess(
        road_network: &RoadNetwork<T>,
        agents: &[Agent<T>],
        parameters: &RoadNetworkParameters<T>,
        period: Interval<T>,
    ) -> Result<Self> {
        let unique_vehicles = UniqueVehicles::from_vehicles(&road_network.vehicles);
        let mut od_pairs = vec![ODPairs::default(); unique_vehicles.len()];
        for agent in agents {
            for mode in agent.iter_modes() {
                if let Mode::Road(road_mode) = mode {
                    let uvehicle = unique_vehicles.vehicle_map.get(&road_mode.vehicle_index());
                    if uvehicle.is_none() {
                        return Err(anyhow!(
                            "Agent {} has an invalid vehicle type index ({})",
                            agent.id,
                            road_mode.vehicle_index().index()
                        ));
                    }
                    let vehicle_od_pairs = &mut od_pairs[*uvehicle.unwrap()];
                    vehicle_od_pairs.add_pair(road_mode.origin(), road_mode.destination());
                }
            }
        }
        let recording_intervals = build_recording_intervals(period, parameters.recording_interval);
        Ok(RoadNetworkPreprocessingData {
            unique_vehicles,
            od_pairs,
            recording_intervals,
        })
    }
}

/// Structure representing the origin-destination pairs for which at least one agent can make a
/// trip, with a given vehicle.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(from = "crate::serialization::DeserODPairs")]
pub struct ODPairs {
    unique_origins: HashSet<NodeIndex>,
    unique_destinations: HashSet<NodeIndex>,
    pairs: HashMap<NodeIndex, HashSet<NodeIndex>>,
}

impl ODPairs {
    /// Create a new ODPairs from a Vec of tuples `(o, d)`, where `o` is the [NodeIndex] of the
    /// origin and `d` is the [NodeIndex] of the destination.
    pub fn from_vec(raw_pairs: Vec<(NodeIndex, NodeIndex)>) -> Self {
        let mut pairs = ODPairs::default();
        for (origin, destination) in raw_pairs {
            pairs.add_pair(origin, destination);
        }
        pairs
    }

    /// Add an origin-destination pair to the ODPairs.
    fn add_pair(&mut self, origin: NodeIndex, destination: NodeIndex) {
        self.unique_origins.insert(origin);
        self.unique_destinations.insert(destination);
        self.pairs
            .entry(origin)
            .or_insert_with(HashSet::new)
            .insert(destination);
    }

    /// Returns `true` if the [ODPairs] is empty.
    pub fn is_empty(&self) -> bool {
        self.unique_origins.is_empty() && self.unique_destinations.is_empty()
    }

    /// Returns the set of unique origins.
    pub fn unique_origins(&self) -> &HashSet<NodeIndex> {
        &self.unique_origins
    }

    /// Returns the set of unique destinations.
    pub fn unique_destinations(&self) -> &HashSet<NodeIndex> {
        &self.unique_destinations
    }

    /// Returns the list of valid destinations for each valid origin.
    pub fn pairs(&self) -> &HashMap<NodeIndex, HashSet<NodeIndex>> {
        &self.pairs
    }
}

fn build_recording_intervals<T: TTFNum>(period: Interval<T>, interval: Time<T>) -> Vec<Time<T>> {
    let mut intervals = Vec::with_capacity(
        ((period.end() - period.start()) / interval)
            .to_usize()
            .unwrap()
            + 2,
    );
    let mut current_time = period.start();
    intervals.push(period.start());
    loop {
        current_time += interval;
        if current_time >= period.end() {
            break;
        }
        intervals.push(current_time);
    }
    intervals.push(period.end());
    intervals
}

#[cfg(test)]
mod tests {
    use petgraph::graph::edge_index;

    use super::*;
    use crate::network::road_network::vehicle::SpeedFunction;
    use crate::units::{Length, Speed, PCE};

    #[test]
    fn preprocess_vehicles_test() {
        // Create three vehicles.
        // - Vehicles 0 and 1 are identical except for Length and PCE.
        // - Vehicles 0 and 2 are identical except for allowed / restricted edges.
        let speed_function = SpeedFunction::Piecewise(vec![
            [Speed(0.), Speed(0.)],
            [Speed(50.), Speed(50.)],
            [Speed(120.0), Speed(90.)],
        ]);
        let v0 = Vehicle::new(
            Length(10.0),
            PCE(1.0),
            speed_function.clone(),
            HashSet::new(),
            [edge_index(2)].into_iter().collect(),
        );
        let v1 = Vehicle::new(
            Length(30.0),
            PCE(3.0),
            speed_function.clone(),
            HashSet::new(),
            [edge_index(2)].into_iter().collect(),
        );
        let v2 = Vehicle::new(
            Length(10.0),
            PCE(1.0),
            speed_function,
            [edge_index(0), edge_index(1)].into_iter().collect(),
            HashSet::new(),
        );
        let vehicles = vec![v0, v1, v2];
        let results = UniqueVehicles::from_vehicles(&vehicles);
        assert_eq!(results.vehicles, vec![vehicle_index(0), vehicle_index(2)]);
        assert_eq!(results.vehicle_map[&vehicle_index(0)], 0);
        assert_eq!(results.vehicle_map[&vehicle_index(1)], 0);
        assert_eq!(results.vehicle_map[&vehicle_index(2)], 1);
    }
}
