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

//! Structs and functions to pre-process a [RoadNetwork].
use std::ops::Index;

use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use num_traits::ConstZero;
use rayon::prelude::*;

use super::skim::EAAllocation;
use super::vehicle::{vehicle_index, Vehicle, VehicleIndex};
use super::{AnySeconds, OriginalNodeId};
use crate::mode::Mode;
use crate::units::{MetroId, NonNegativeSeconds};

// Threshold used to consider a node as a popular origin or destination (see
// [ODPairsStruct::popular_origins_and_destinations]).
const POPULAR_THRESHOLD: usize = 20;

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
    list: Vec<(VehicleIndex, Vec<MetroId>)>,
    /// Map each original vehicle id to the index of their reference unique vehicle.
    vehicle_map: HashMap<MetroId, UniqueVehicleIndex>,
}

impl UniqueVehicles {
    /// Creates a new [UniqueVehicles] from a Vec of [Vehicle].
    pub(crate) fn init() -> Self {
        let vehicles = super::vehicles();
        Self::init_inner(vehicles)
    }

    fn init_inner(vehicles: &[Vehicle]) -> Self {
        let mut list: Vec<(VehicleIndex, Vec<MetroId>)> = Vec::new();
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

    /// Iterates over the [MetroId] in each unique vehicle category.
    pub(crate) fn iter_original_ids(&self) -> impl Iterator<Item = &[MetroId]> {
        self.list
            .iter()
            .map(|(_, vehicle_ids)| vehicle_ids.as_slice())
    }
}

impl Index<MetroId> for UniqueVehicles {
    type Output = UniqueVehicleIndex;
    fn index(&self, id: MetroId) -> &Self::Output {
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
    pub(crate) od_pairs: Vec<ODPairsStruct>,
    /// Vector with, for each unique vehicle, an [ODTravelTimes] instance representing the
    /// OD-pair level free-flow travel times.
    pub(crate) free_flow_travel_times: Vec<ODTravelTimes>,
}

impl RoadNetworkPreprocessingData {
    /// Returns the number of unique vehicles.
    pub fn nb_unique_vehicles(&self) -> usize {
        self.unique_vehicles.len()
    }

    /// Returns the [UniqueVehicleIndex] corresponding to the given [MetroId].
    ///
    /// *Panics* if the given [MetroId] is not in the [RoadNetworkPreprocessingData].
    pub fn get_unique_vehicle_index(&self, id: MetroId) -> UniqueVehicleIndex {
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
    pub fn od_pairs(&self, uvehicle_id: UniqueVehicleIndex) -> &ODPairsStruct {
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
pub struct ODPairsStruct {
    /// Set of nodes used as origin for at least one trip which requires profile query.
    unique_origins: HashSet<OriginalNodeId>,
    /// Set of nodes used as destination for at least one trip which requires profile query.
    unique_destinations: HashSet<OriginalNodeId>,
    /// For each origin node, the set of destination nodes (with a boolean indicating whether the
    /// OD pair requires a profile query).
    pairs: ODPairs,
    /// For each destination node, the set of origin nodes (with a boolean indicating whether the
    /// OD pair requires a profile query).
    reverse_pairs: ODPairs,
}

/// For each node used as origin, a set of nodes used as destination, with a boolean indicating
/// whether there is at least one trip which requires profile query.
type ODPairs = HashMap<OriginalNodeId, HashSet<(OriginalNodeId, bool)>>;

impl ODPairsStruct {
    /// Create a new ODPairs from a Vec of tuples `(o, d, b)`, where `o` is the [NodeIndex] of the
    /// origin, `d` is the [NodeIndex] of the destination and `b` is a boolean indicating whether
    /// the OD pair requires a profile query.
    pub fn from_vec(raw_pairs: Vec<(OriginalNodeId, OriginalNodeId, bool)>) -> Self {
        let mut pairs = ODPairsStruct::default();
        for (origin, destination, requires_profile_query) in raw_pairs {
            pairs.add_pair(origin, destination, requires_profile_query);
        }
        pairs
    }

    /// Add an origin-destination pair to the ODPairs.
    fn add_pair(
        &mut self,
        origin: OriginalNodeId,
        destination: OriginalNodeId,
        requires_profile_query: bool,
    ) {
        if requires_profile_query {
            self.unique_origins.insert(origin);
            self.unique_destinations.insert(destination);
        }
        self.pairs
            .entry(origin)
            .or_default()
            .insert((destination, requires_profile_query));
        self.reverse_pairs
            .entry(destination)
            .or_default()
            .insert((origin, requires_profile_query));
    }

    /// Returns `true` if the [ODPairs] has no pair.
    pub fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }

    /// Returns the set of unique origins.
    pub fn unique_origins(&self) -> &HashSet<OriginalNodeId> {
        &self.unique_origins
    }

    /// Returns the set of unique destinations.
    pub fn unique_destinations(&self) -> &HashSet<OriginalNodeId> {
        &self.unique_destinations
    }

    /// Returns a parallel iterator over the unique destinations (which requires profile query) for
    /// all the unique origins.
    ///
    /// Also returns the number of unique origins.
    pub fn pairs(
        &self,
    ) -> (
        impl ParallelIterator<Item = (OriginalNodeId, impl Iterator<Item = OriginalNodeId> + '_)> + '_,
        usize,
    ) {
        (
            self.pairs.par_iter().map(|(&origin, set)| {
                (
                    origin,
                    set.iter()
                        .filter_map(|&(destination, requires_profile_query)| {
                            if requires_profile_query {
                                Some(destination)
                            } else {
                                None
                            }
                        }),
                )
            }),
            self.pairs.len(),
        )
    }

    /// Returns the most popular origins and destination.
    ///
    /// A node is a "popular" origin if it the origin for at least `POPULAR_THRESHOLD` OD pairs for which the
    /// destination appears in at least `POPULAR_THRESHOLD` OD pairs.
    pub fn popular_origins_and_destinations(&self) -> (Vec<OriginalNodeId>, Vec<OriginalNodeId>) {
        // How many times each node is used as origin.
        let origin_counts: HashMap<OriginalNodeId, usize> = self
            .pairs
            .iter()
            .map(|(&o, dests)| {
                (
                    o,
                    dests
                        .iter()
                        .filter(|(_d, requires_profile)| *requires_profile)
                        .count(),
                )
            })
            .collect();
        // How many times each node is used as destination.
        let destination_counts: HashMap<OriginalNodeId, usize> = self
            .reverse_pairs
            .iter()
            .map(|(&d, origins)| {
                (
                    d,
                    origins
                        .iter()
                        .filter(|(_o, requires_profile)| *requires_profile)
                        .count(),
                )
            })
            .collect();
        // Nodes which are used more than POPULAR_THRESHOLD times as origin.
        let main_origins: HashSet<OriginalNodeId> = origin_counts
            .into_iter()
            .filter_map(|(o, c)| {
                if c >= POPULAR_THRESHOLD {
                    Some(o)
                } else {
                    None
                }
            })
            .collect();
        // Nodes which are used more than POPULAR_THRESHOLD times as destination.
        let main_destinations: HashSet<OriginalNodeId> = destination_counts
            .into_iter()
            .filter_map(|(o, c)| {
                if c >= POPULAR_THRESHOLD {
                    Some(o)
                } else {
                    None
                }
            })
            .collect();
        let popular_origins: Vec<OriginalNodeId> = self
            .pairs
            .iter()
            .filter_map(|(&o, dests)| {
                let c = dests
                    .iter()
                    .filter(|(d, requires_profile)| {
                        *requires_profile && main_destinations.contains(d)
                    })
                    .count();
                if c >= POPULAR_THRESHOLD {
                    Some(o)
                } else {
                    None
                }
            })
            .collect();
        let popular_destinations: Vec<OriginalNodeId> = self
            .reverse_pairs
            .iter()
            .filter_map(|(&d, origins)| {
                let c = origins
                    .iter()
                    .filter(|(o, requires_profile)| *requires_profile && main_origins.contains(o))
                    .count();
                if c >= POPULAR_THRESHOLD {
                    Some(d)
                } else {
                    None
                }
            })
            .collect();
        (popular_origins, popular_destinations)
    }
}

fn init_od_pairs(unique_vehicles: &UniqueVehicles) -> Result<Vec<ODPairsStruct>> {
    let mut od_pairs = vec![ODPairsStruct::default(); unique_vehicles.len()];
    for agent in crate::population::agents() {
        for mode in agent.iter_modes() {
            if let Mode::Trip(trip_mode) = mode {
                let requires_profile_query =
                    trip_mode.departure_time_model.requires_profile_query();
                for leg in trip_mode.iter_road_legs() {
                    if leg.route.is_some() {
                        // A route is specified for this leg so there is no need to consider this
                        // OD pair in the skims.
                        continue;
                    }
                    let vehicle_id = leg.vehicle;
                    let uvehicle = unique_vehicles.vehicle_map.get(&vehicle_id);
                    if let Some(&uvehicle) = uvehicle {
                        let origin = leg.origin;
                        let destination = leg.destination;
                        let vehicle_od_pairs = &mut od_pairs[uvehicle.index()];
                        vehicle_od_pairs.add_pair(origin, destination, requires_profile_query);
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
    od_pairs: &[ODPairsStruct],
) -> Result<Vec<ODTravelTimes>> {
    let mut free_flow_travel_times = vec![ODTravelTimes::default(); unique_vehicles.len()];
    let free_flow_weights = super::free_flow_weights_inner(unique_vehicles);
    let skims = super::compute_skims_inner(&free_flow_weights, od_pairs)?;
    for (vehicle_index, vehicle_od_pairs) in od_pairs.iter().enumerate() {
        if let Some(vehicle_skims) = skims[unique_vehicle_index(vehicle_index)].as_ref() {
            let vehicle_ff_tts: ODTravelTimes = vehicle_od_pairs
                .pairs
                .par_iter()
                .map(|(&origin, set)| {
                    set.par_iter()
                        .map(move |&(destination, requires_profile_query)| {
                            (origin, destination, requires_profile_query)
                        })
                })
                .flatten()
                .map_init(
                    EAAllocation::default,
                    |alloc, (origin, destination, requires_profile_query)| {
                        let maybe_tt: Option<_> = if requires_profile_query {
                            let maybe_ttf = vehicle_skims.profile_query(origin, destination)?;
                            maybe_ttf.map(|ttf| {
                                assert!(ttf.is_constant());
                                ttf.as_constant().copied().unwrap()
                            })
                        } else {
                            // The profile query has not been pre-computed (probably because there is no
                            // trip with a departure-time choice for this OD pair).
                            // Insted, we run a earliest-arrival query.
                            vehicle_skims
                                .earliest_arrival_query(
                                    origin,
                                    destination,
                                    AnySeconds::ZERO,
                                    alloc,
                                )?
                                .map(|(arrival_time, _route)| arrival_time)
                        };
                        let tt = maybe_tt.ok_or(anyhow!(
                            "No route from node {} to node {}",
                            origin,
                            destination
                        ))?;
                        Ok((
                            (origin, destination),
                            tt.try_into().expect("Free-flow travel time is negative"),
                        ))
                    },
                )
                .collect::<Result<_>>()?;
            free_flow_travel_times[vehicle_index] = vehicle_ff_tts;
        } else {
            // No skims for the unique vehicle.
            assert!(vehicle_od_pairs.is_empty());
        }
    }
    Ok(free_flow_travel_times)
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::network::road_network::vehicle::SpeedFunction;
    use crate::units::*;

    #[test]
    fn preprocess_vehicles_test() {
        let id1 = MetroId::Integer(1);
        let id2 = MetroId::Integer(2);
        let id3 = MetroId::Integer(3);
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
            [id2].into_iter().collect(),
        );
        let v1 = Vehicle::new(
            2,
            NonNegativeMeters::new_unchecked(30.0),
            PCE::new_unchecked(3.0),
            speed_function.clone(),
            HashSet::new(),
            [id2].into_iter().collect(),
        );
        let v2 = Vehicle::new(
            3,
            NonNegativeMeters::new_unchecked(10.0),
            PCE::new_unchecked(1.0),
            speed_function,
            [id1, id1].into_iter().collect(),
            HashSet::new(),
        );
        let vehicles = vec![v0, v1, v2];
        let results = UniqueVehicles::init_inner(&vehicles);
        assert_eq!(
            results.list,
            vec![
                (vehicle_index(0), vec![id1, id2]),
                (vehicle_index(2), vec![id3])
            ]
        );
        assert_eq!(results.vehicle_map[&id1], unique_vehicle_index(0));
        assert_eq!(results.vehicle_map[&id2], unique_vehicle_index(0));
        assert_eq!(results.vehicle_map[&id3], unique_vehicle_index(1));
    }
}
