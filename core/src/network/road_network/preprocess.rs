// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs and functions to pre-process a [RoadNetwork].
use std::ops::Index;

use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use ttf::TTF;

use super::vehicle::{vehicle_index, OriginalVehicleId, Vehicle, VehicleIndex};
use super::OriginalNodeId;
use crate::mode::Mode;
use crate::units::NonNegativeSeconds;

/// Unique vehicle index.
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct UniqueVehicleIndex(usize);

impl UniqueVehicleIndex {
    /// Creates a new UniqueVehicleIndex.
    pub const fn new(x: usize) -> Self {
        UniqueVehicleIndex(x)
    }

    /// Returns the index of the UniqueVehicleIndex.
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Short version of `UniqueVehicleIndex::new`.
pub const fn unique_vehicle_index(x: usize) -> UniqueVehicleIndex {
    UniqueVehicleIndex::new(x)
}

/// Struct to store the set of unique vehicles and the equivalences between vehicles.
#[derive(Clone, Debug)]
pub(crate) struct UniqueVehicles {
    /// Index in the road network's vehicle list of the reference unique vehicles.
    list: Vec<(VehicleIndex, Vec<OriginalVehicleId>)>,
    /// Map each original vehicle id to the index of their reference unique vehicle.
    vehicle_map: HashMap<OriginalVehicleId, UniqueVehicleIndex>,
}

impl UniqueVehicles {
    /// Creates a new [UniqueVehicles] from a Vec of [Vehicle].
    pub(crate) fn init() -> Self {
        let vehicles = super::vehicles();
        Self::init_inner(vehicles)
    }

    fn init_inner(vehicles: &[Vehicle]) -> Self {
        let mut list: Vec<(VehicleIndex, Vec<OriginalVehicleId>)> = Vec::new();
        let mut vehicle_map = HashMap::with_capacity(vehicles.len());
        for (vehicle_idx, vehicle) in vehicles.iter().enumerate() {
            if let Some(uid) = list
                .iter()
                .position(|(id, _)| vehicle.share_weights(&vehicles[id.index()]))
            {
                list[uid].1.push(vehicle.id);
                vehicle_map.insert(vehicle.id, unique_vehicle_index(uid));
            } else {
                // This vehicle is unique (so far).
                // It will be used as a reference unique vehicle.
                vehicle_map.insert(vehicle.id, unique_vehicle_index(list.len()));
                list.push((vehicle_index(vehicle_idx), vec![vehicle.id]));
            }
        }
        UniqueVehicles { list, vehicle_map }
    }

    /// Returns the number of unique vehicles.
    pub(crate) fn len(&self) -> usize {
        self.list.len()
    }

    /// Iterates over the `UniqueVehicleIndex` and the reference [Vehicle] of all unique vehicles.
    pub(crate) fn iter_uniques<'a>(
        &'a self,
        vehicles: &'a [Vehicle],
    ) -> impl Iterator<Item = (UniqueVehicleIndex, &'a Vehicle)> {
        self.list
            .iter()
            .enumerate()
            .map(|(i, (v_id, _))| (unique_vehicle_index(i), &vehicles[v_id.index()]))
    }

    /// Iterates over the [OriginalVehicleId] in each unique vehicle category.
    pub(crate) fn iter_original_ids(&self) -> impl Iterator<Item = &[OriginalVehicleId]> {
        self.list
            .iter()
            .map(|(_, vehicle_ids)| vehicle_ids.as_slice())
    }
}

impl Index<OriginalVehicleId> for UniqueVehicles {
    type Output = UniqueVehicleIndex;
    fn index(&self, id: OriginalVehicleId) -> &Self::Output {
        &self.vehicle_map[&id]
    }
}

/// Set of pre-processing data used for different road-network computation.
#[derive(Clone, Debug)]
pub struct RoadNetworkPreprocessingData {
    /// Set of unique vehicles.
    pub(crate) unique_vehicles: UniqueVehicles,
    /// Vector with, for each unique vehicle, an [ODPairs] instance representing the
    /// origin-destination pairs for which at least one agent can make a trip with this vehicle.
    pub(crate) od_pairs: Vec<ODPairs>,
    /// Vector with, for each unique vehicle, an [ODTravelTimes] instance representing the
    /// OD-pair level free-flow travel times.
    pub(crate) free_flow_travel_times: Vec<ODTravelTimes>,
}

impl RoadNetworkPreprocessingData {
    /// Returns the number of unique vehicles.
    pub fn nb_unique_vehicles(&self) -> usize {
        self.unique_vehicles.len()
    }

    /// Returns the [UniqueVehicleIndex] corresponding to the given [OriginalVehicleId].
    ///
    /// *Panics* if the given [OriginalVehicleId] is not in the [RoadNetworkPreprocessingData].
    pub fn get_unique_vehicle_index(&self, id: OriginalVehicleId) -> UniqueVehicleIndex {
        self.unique_vehicles.vehicle_map[&id]
    }

    /// Returns the [VehicleIndex] of the reference unique vehicle, for the given
    /// [UniqueVehicleIndex].
    ///
    /// *Panics* if the given unique-vehicle index is out-of-bound for this
    /// [RoadNetworkPreprocessingData].
    pub fn get_vehicle_index(&self, id: UniqueVehicleIndex) -> VehicleIndex {
        self.unique_vehicles.list[id.index()].0
    }

    /// Returns the [ODPairs] corresponding to the [UniqueVehicleIndex].
    ///
    /// *Panics* if the unique-vehicle index exceeds the number of unique vehicle of this
    /// [RoadNetworkPreprocessingData].
    pub fn od_pairs(&self, uvehicle_id: UniqueVehicleIndex) -> &ODPairs {
        &self.od_pairs[uvehicle_id.index()]
    }

    /// Returns the [ODTravelTimes] corresponding to the [UniqueVehicleIndex].
    ///
    /// *Panics* if the unique-vehicle index exceeds the number of unique vehicle of this
    /// [RoadNetworkPreprocessingData].
    pub fn free_flow_travel_times_of_unique_vehicle(
        &self,
        uvehicle_id: UniqueVehicleIndex,
    ) -> &ODTravelTimes {
        &self.free_flow_travel_times[uvehicle_id.index()]
    }
}

impl RoadNetworkPreprocessingData {
    /// Computes pre-processed data for a [RoadNetwork], given the list of [Agent], the
    /// [RoadNetworkParameters] and the simulation interval.
    pub fn preprocess() -> Result<Self> {
        let unique_vehicles = UniqueVehicles::init();
        let od_pairs = init_od_pairs(&unique_vehicles)?;
        let free_flow_travel_times = compute_free_flow_travel_times(&unique_vehicles, &od_pairs)?;
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
    unique_origins: HashSet<OriginalNodeId>,
    unique_destinations: HashSet<OriginalNodeId>,
    pairs: HashMap<OriginalNodeId, HashSet<OriginalNodeId>>,
}

impl ODPairs {
    /// Create a new ODPairs from a Vec of tuples `(o, d)`, where `o` is the [NodeIndex] of the
    /// origin and `d` is the [NodeIndex] of the destination.
    pub fn from_vec(raw_pairs: Vec<(OriginalNodeId, OriginalNodeId)>) -> Self {
        let mut pairs = ODPairs::default();
        for (origin, destination) in raw_pairs {
            pairs.add_pair(origin, destination);
        }
        pairs
    }

    /// Add an origin-destination pair to the ODPairs.
    fn add_pair(&mut self, origin: OriginalNodeId, destination: OriginalNodeId) {
        self.unique_origins.insert(origin);
        self.unique_destinations.insert(destination);
        self.pairs.entry(origin).or_default().insert(destination);
    }

    /// Returns `true` if the [ODPairs] is empty.
    pub fn is_empty(&self) -> bool {
        self.unique_origins.is_empty() && self.unique_destinations.is_empty()
    }

    /// Returns the set of unique origins.
    pub fn unique_origins(&self) -> &HashSet<OriginalNodeId> {
        &self.unique_origins
    }

    /// Returns the set of unique destinations.
    pub fn unique_destinations(&self) -> &HashSet<OriginalNodeId> {
        &self.unique_destinations
    }

    /// Returns the list of valid destinations for each valid origin.
    pub fn pairs(&self) -> &HashMap<OriginalNodeId, HashSet<OriginalNodeId>> {
        &self.pairs
    }
}

fn init_od_pairs(unique_vehicles: &UniqueVehicles) -> Result<Vec<ODPairs>> {
    let mut od_pairs = vec![ODPairs::default(); unique_vehicles.len()];
    for agent in crate::population::agents() {
        for mode in agent.iter_modes() {
            if let Mode::Trip(trip_mode) = mode {
                for leg in trip_mode.iter_road_legs() {
                    let vehicle_id = leg.vehicle;
                    let uvehicle = unique_vehicles.vehicle_map.get(&vehicle_id);
                    if let Some(&uvehicle) = uvehicle {
                        // Unwraping is safe because we are iterating over road legs.
                        let origin = leg.origin;
                        let destination = leg.destination;
                        let vehicle_od_pairs = &mut od_pairs[uvehicle.index()];
                        vehicle_od_pairs.add_pair(origin, destination);
                    } else {
                        return Err(anyhow!(
                            "Agent {} has an invalid vehicle type index ({})",
                            agent.id,
                            vehicle_id,
                        ));
                    }
                }
            }
        }
    }
    Ok(od_pairs)
}

/// Map for some origin nodes, an OD-level travel-time, for some destination nodes.
type ODTravelTimes = HashMap<(OriginalNodeId, OriginalNodeId), NonNegativeSeconds>;

fn compute_free_flow_travel_times(
    unique_vehicles: &UniqueVehicles,
    od_pairs: &[ODPairs],
) -> Result<Vec<ODTravelTimes>> {
    let mut free_flow_travel_times = vec![ODTravelTimes::default(); unique_vehicles.len()];
    let free_flow_weights = super::free_flow_weights_inner(unique_vehicles);
    let skims = super::compute_skims_inner(&free_flow_weights, od_pairs)?;
    for agent in crate::population::agents() {
        for mode in agent.iter_modes() {
            if let Mode::Trip(trip_mode) = mode {
                for leg in trip_mode.iter_road_legs() {
                    let vehicle_id = leg.vehicle;
                    let uvehicle = unique_vehicles.vehicle_map[&vehicle_id];
                    let origin = leg.origin;
                    let destination = leg.destination;
                    let vehicle_ff_tts = &mut free_flow_travel_times[uvehicle.index()];
                    let vehicle_skims = skims[uvehicle]
                        .as_ref()
                        .unwrap_or_else(|| panic!("No skims for unique vehicle {uvehicle:?}"));
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
                    vehicle_ff_tts.insert(
                        (origin, destination),
                        tt.try_into().expect("Free-flow travel time is negative"),
                    );
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
    use crate::units::{MetersPerSecond, NonNegativeMeters, PCE};

    #[test]
    fn preprocess_vehicles_test() {
        // Create three vehicles.
        // - Vehicles 0 and 1 are identical except for Length and PCE.
        // - Vehicles 0 and 2 are identical except for allowed / restricted edges.
        let speed_function = SpeedFunction::Piecewise(vec![
            [
                MetersPerSecond::new_unchecked(1.),
                MetersPerSecond::new_unchecked(1.),
            ],
            [
                MetersPerSecond::new_unchecked(50.),
                MetersPerSecond::new_unchecked(50.),
            ],
            [
                MetersPerSecond::new_unchecked(120.0),
                MetersPerSecond::new_unchecked(90.),
            ],
        ]);
        let v0 = Vehicle::new(
            1,
            NonNegativeMeters::new_unchecked(10.0),
            PCE::new_unchecked(1.0),
            speed_function.clone(),
            HashSet::new(),
            [2].into_iter().collect(),
        );
        let v1 = Vehicle::new(
            2,
            NonNegativeMeters::new_unchecked(30.0),
            PCE::new_unchecked(3.0),
            speed_function.clone(),
            HashSet::new(),
            [2].into_iter().collect(),
        );
        let v2 = Vehicle::new(
            3,
            NonNegativeMeters::new_unchecked(10.0),
            PCE::new_unchecked(1.0),
            speed_function,
            [0, 1].into_iter().collect(),
            HashSet::new(),
        );
        let vehicles = vec![v0, v1, v2];
        let results = UniqueVehicles::init_inner(&vehicles);
        assert_eq!(
            results.list,
            vec![(vehicle_index(0), vec![1, 2]), (vehicle_index(2), vec![3])]
        );
        assert_eq!(results.vehicle_map[&1], unique_vehicle_index(0));
        assert_eq!(results.vehicle_map[&2], unique_vehicle_index(0));
        assert_eq!(results.vehicle_map[&3], unique_vehicle_index(1));
    }
}
