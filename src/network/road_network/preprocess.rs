// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs and functions to pre-process a [RoadNetwork].
use std::ops::Index;

use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use ttf::{TTFNum, TTF};

use super::vehicle::{vehicle_index, Vehicle, VehicleIndex};
use super::{OriginalNodeIndex, RoadNetwork, RoadNetworkParameters};
use crate::agent::Agent;
use crate::mode::Mode;
use crate::units::Time;

/// Struct to store the set of unique vehicles and the equivalences between vehicles.
#[derive(Clone, Debug)]
pub(crate) struct UniqueVehicles {
    /// List all the vehicles for which [RoadNetworkWeights] and [RoadNetworkSkims] are computed.
    vehicles: Vec<VehicleIndex>,
    /// Map each vehicle to the corresponding id to use for [RoadNetworkWeights] and
    /// [RoadNetworkSkims].
    vehicle_map: HashMap<VehicleIndex, usize>,
}

impl UniqueVehicles {
    /// Creates a new [UniqueVehicles] from a Vec of [Vehicle].
    pub(crate) fn from_vehicles<T: TTFNum>(vehicles: &[Vehicle<T>]) -> Self {
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
    pub(crate) fn len(&self) -> usize {
        self.vehicles.len()
    }

    /// Iterates over the unique vehicles' ids and [Vehicle].
    pub(crate) fn iter_uniques<'a, T>(
        &'a self,
        vehicles: &'a [Vehicle<T>],
    ) -> impl Iterator<Item = (usize, &'a Vehicle<T>)> {
        self.vehicles
            .iter()
            .map(|v_id| &vehicles[v_id.index()])
            .enumerate()
    }
}

impl Index<VehicleIndex> for UniqueVehicles {
    type Output = usize;
    fn index(&self, index: VehicleIndex) -> &Self::Output {
        &self.vehicle_map[&index]
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
    pub(crate) unique_vehicles: UniqueVehicles,
    /// Vector with, for each unique vehicle, an [ODPairs] instance representing the
    /// origin-destination pairs for which at least one agent can make a trip with this vehicle.
    pub(crate) od_pairs: Vec<ODPairs>,
    /// Vector with, for each unique vehicle, an [ODTravelTimes] instance representing the
    /// OD-pair level free-flow travel times.
    pub(crate) free_flow_travel_times: Vec<ODTravelTimes<T>>,
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
    ) -> Result<Self> {
        let unique_vehicles = UniqueVehicles::from_vehicles(&road_network.vehicles);
        let od_pairs = od_pairs_from_agents(agents, &unique_vehicles)?;
        let free_flow_travel_times = compute_free_flow_travel_times(
            road_network,
            agents,
            parameters,
            &unique_vehicles,
            &od_pairs,
        )?;
        Ok(RoadNetworkPreprocessingData {
            unique_vehicles,
            od_pairs,
            free_flow_travel_times,
        })
    }
}

/// Structure representing the origin-destination pairs for which at least one agent can make a
/// trip, with a given vehicle.
#[derive(Clone, Debug, Default)]
pub struct ODPairs {
    unique_origins: HashSet<OriginalNodeIndex>,
    unique_destinations: HashSet<OriginalNodeIndex>,
    pairs: HashMap<OriginalNodeIndex, HashSet<OriginalNodeIndex>>,
}

impl ODPairs {
    /// Create a new ODPairs from a Vec of tuples `(o, d)`, where `o` is the [NodeIndex] of the
    /// origin and `d` is the [NodeIndex] of the destination.
    pub fn from_vec(raw_pairs: Vec<(OriginalNodeIndex, OriginalNodeIndex)>) -> Self {
        let mut pairs = ODPairs::default();
        for (origin, destination) in raw_pairs {
            pairs.add_pair(origin, destination);
        }
        pairs
    }

    /// Add an origin-destination pair to the ODPairs.
    fn add_pair(&mut self, origin: OriginalNodeIndex, destination: OriginalNodeIndex) {
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
    pub fn unique_origins(&self) -> &HashSet<OriginalNodeIndex> {
        &self.unique_origins
    }

    /// Returns the set of unique destinations.
    pub fn unique_destinations(&self) -> &HashSet<OriginalNodeIndex> {
        &self.unique_destinations
    }

    /// Returns the list of valid destinations for each valid origin.
    pub fn pairs(&self) -> &HashMap<OriginalNodeIndex, HashSet<OriginalNodeIndex>> {
        &self.pairs
    }
}

fn od_pairs_from_agents<T>(
    agents: &[Agent<T>],
    unique_vehicles: &UniqueVehicles,
) -> Result<Vec<ODPairs>> {
    let mut od_pairs = vec![ODPairs::default(); unique_vehicles.len()];
    for agent in agents {
        for mode in agent.iter_modes() {
            if let Mode::Trip(trip_mode) = mode {
                for leg in trip_mode.iter_road_legs() {
                    let vehicle_id = leg.vehicle;
                    let uvehicle = unique_vehicles.vehicle_map.get(&vehicle_id);
                    if let Some(&uvehicle) = uvehicle {
                        // Unwraping is safe because we are iterating over road legs.
                        let origin = leg.origin;
                        let destination = leg.destination;
                        let vehicle_od_pairs = &mut od_pairs[uvehicle];
                        vehicle_od_pairs.add_pair(origin, destination);
                    } else {
                        return Err(anyhow!(
                            "Agent {} has an invalid vehicle type index ({})",
                            agent.id,
                            vehicle_id.index(),
                        ));
                    }
                }
            }
        }
    }
    Ok(od_pairs)
}

/// Map for some origin nodes, an OD-level travel-time, for some destination nodes.
type ODTravelTimes<T> = HashMap<(OriginalNodeIndex, OriginalNodeIndex), Time<T>>;

fn compute_free_flow_travel_times<T: TTFNum>(
    road_network: &RoadNetwork<T>,
    agents: &[Agent<T>],
    parameters: &RoadNetworkParameters<T>,
    unique_vehicles: &UniqueVehicles,
    od_pairs: &Vec<ODPairs>,
) -> Result<Vec<ODTravelTimes<T>>> {
    let mut free_flow_travel_times = vec![ODTravelTimes::default(); unique_vehicles.len()];
    let free_flow_weights = road_network.get_free_flow_weights_inner(unique_vehicles);
    let skims = road_network.compute_skims_inner(&free_flow_weights, od_pairs, parameters)?;
    for agent in agents {
        for mode in agent.iter_modes() {
            if let Mode::Trip(trip_mode) = mode {
                for leg in trip_mode.iter_road_legs() {
                    let vehicle_id = leg.vehicle;
                    let uvehicle = unique_vehicles.vehicle_map.get(&vehicle_id).unwrap();
                    let origin = leg.origin;
                    let destination = leg.destination;
                    let vehicle_ff_tts = &mut free_flow_travel_times[*uvehicle];
                    let vehicle_skims = skims[*uvehicle]
                        .as_ref()
                        .unwrap_or_else(|| panic!("No skims for unique vehicle {uvehicle}"));
                    let ttf = vehicle_skims.profile_query(origin, destination)?;
                    let tt = match ttf {
                        Some(&TTF::Constant(tt)) => tt,
                        None => {
                            return Err(anyhow!(
                                "No route from node {} to node {}",
                                origin,
                                destination
                            ));
                        }
                        Some(TTF::Piecewise(_)) => {
                            return Err(anyhow!(
                                "Free-flow travel time from {} to {} is not constant",
                                origin,
                                destination
                            ));
                        }
                    };
                    vehicle_ff_tts.insert((origin, destination), tt);
                }
            }
        }
    }
    Ok(free_flow_travel_times)
}

#[cfg(test)]
mod tests {

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
            [2].into_iter().collect(),
        );
        let v1 = Vehicle::new(
            Length(30.0),
            PCE(3.0),
            speed_function.clone(),
            HashSet::new(),
            [2].into_iter().collect(),
        );
        let v2 = Vehicle::new(
            Length(10.0),
            PCE(1.0),
            speed_function,
            [0, 1].into_iter().collect(),
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
