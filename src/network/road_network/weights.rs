// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode
//! Description of the [RoadNetworkWeights].
#![allow(clippy::disallowed_types)]
use std::ops::{Index, IndexMut};

use anyhow::{bail, Context, Result};
use hashbrown::{HashMap, HashSet};
use log::warn;
use num_traits::{Float, Zero};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::{PwlTTF, TTFNum, TTF};

use super::{
    preprocess::{UniqueVehicleIndex, UniqueVehicles},
    vehicle::OriginalVehicleId,
    OriginalEdgeId, RoadNetwork, RoadNetworkPreprocessingData,
};
use crate::units::{Interval, Time};

/// Structure to store the travel-time functions of each edge of a
/// [RoadNetwork](super::RoadNetwork), for a group of unique vehicle types.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema, PartialEq)]
#[serde(bound = "T: TTFNum")]
pub struct VehicleWeights<T> {
    /// Original id of the vehicle for which the weights are valid.
    pub(crate) vehicle_ids: Vec<OriginalVehicleId>,
    #[schemars(with = "std::collections::HashMap<OriginalEdgeId, TTF<Time<T>>>")]
    /// Weights.
    pub(crate) weights: HashMap<OriginalEdgeId, TTF<Time<T>>>,
}

impl<T> VehicleWeights<T> {
    pub(crate) fn weights(&self) -> &HashMap<OriginalEdgeId, TTF<Time<T>>> {
        &self.weights
    }

    pub(crate) fn weights_mut(&mut self) -> &mut HashMap<OriginalEdgeId, TTF<Time<T>>> {
        &mut self.weights
    }

    pub(crate) fn vehicle_ids(&self) -> &[OriginalVehicleId] {
        self.vehicle_ids.as_slice()
    }

    fn len(&self) -> usize {
        self.weights.len()
    }
}

impl<T: TTFNum> VehicleWeights<T> {
    pub(crate) fn complexity(&self) -> usize {
        self.weights.values().map(|w| w.complexity()).sum()
    }
}

/// Structure to store the travel-time functions of each edge of a
/// [RoadNetwork](super::RoadNetwork), for each unique vehicle type.
///
/// The outer vector has the same length as the number of unique vehicles of the associated
/// [RoadNetwork](super::RoadNetwork).
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(title = "Road Network Weights")]
#[schemars(
    description = "Travel-time functions of each edge of road network, for each unique vehicle \
    (outer array)."
)]
pub struct RoadNetworkWeights<T> {
    pub(crate) weights: Vec<VehicleWeights<T>>,
    #[serde(skip)]
    pub(crate) period: Interval<T>,
    #[serde(skip)]
    pub(crate) interval: Time<T>,
}

impl<T> RoadNetworkWeights<T> {
    /// Initializes a new RoadNetworkWeights instance with enough capacity for the given number of
    /// unique vehicles and edges.
    pub(crate) fn with_capacity(
        period: Interval<T>,
        interval: Time<T>,
        unique_vehicles: &UniqueVehicles,
        nb_edges: usize,
    ) -> Self {
        let weights = unique_vehicles
            .iter_original_ids()
            .map(|vehicle_ids| VehicleWeights {
                vehicle_ids: vehicle_ids.to_vec(),
                weights: HashMap::with_capacity(nb_edges),
            })
            .collect();
        RoadNetworkWeights {
            weights,
            period,
            interval,
        }
    }

    /// Returns the number of unique vehicles in the weights.
    pub(crate) fn len(&self) -> usize {
        self.weights.len()
    }

    /// Returns the [TTF] corresponding to the given unique vehicle id and edge.
    ///
    /// Returns `None` if the edge is not accessible for the given vehicle.
    pub(crate) fn get(
        &self,
        vehicle_id: UniqueVehicleIndex,
        edge_id: OriginalEdgeId,
    ) -> Option<&TTF<Time<T>>> {
        self.weights[vehicle_id.index()].weights.get(&edge_id)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &VehicleWeights<T>> {
        self.weights.iter()
    }
}

impl<T: Copy> RoadNetworkWeights<T> {
    /// Initializes a new RoadNetworkWeights instance with the same capacity as the given
    /// RoadNetworkWeights.
    pub fn with_capacity_in(instance: &Self) -> Self {
        let mut weights = Vec::with_capacity(instance.len());
        for v_weights in instance.weights.iter() {
            weights.push(VehicleWeights {
                vehicle_ids: v_weights.vehicle_ids.clone(),
                weights: HashMap::with_capacity(v_weights.len()),
            });
        }
        RoadNetworkWeights {
            weights,
            period: instance.period,
            interval: instance.interval,
        }
    }
}

type XYVec<T> = Vec<(Time<T>, Time<T>)>;

impl<T: TTFNum> RoadNetworkWeights<T> {
    pub(crate) fn from_values(
        values: Vec<(OriginalVehicleId, OriginalEdgeId, Time<T>, Time<T>)>,
        period: Interval<T>,
        interval: Time<T>,
        road_network: &RoadNetwork<T>,
        unique_vehicles: &UniqueVehicles,
    ) -> Result<Self> {
        // Collect all the values in a map (vid, eid) -> (td, tt).
        let mut global_map: HashMap<(OriginalVehicleId, OriginalEdgeId), XYVec<T>> = HashMap::new();
        for (vid, eid, x, y) in values {
            global_map
                .entry((vid, eid))
                .or_insert_with(Vec::new)
                .push((x, y));
        }
        // Build the TTFs.
        let mut ttf_map = HashMap::new();
        for ((vid, eid), xy_vec) in global_map.into_iter() {
            let ttf = build_ttf(xy_vec, period, interval).with_context(|| {
                format!("Failed to build TTF for vehicle id `{vid}` and edge id `{eid}`")
            })?;
            ttf_map
                .entry(vid)
                .or_insert_with(HashMap::new)
                .insert(eid, ttf);
        }
        // Make sure that we have the weights for all vehicles and all accessible edges of the road
        // network.
        for vehicle in road_network.iter_vehicles() {
            let w = ttf_map.entry(vehicle.id).or_insert_with(HashMap::new);
            let mut nb_warnings = 0;
            let all_edges: HashSet<_> = road_network
                .iter_original_edge_ids()
                .filter(|&edge_id| vehicle.can_access(edge_id))
                .collect();
            // Discard the weights of edges that cannot be accessed.
            w.retain(|edge_id, _| all_edges.contains(edge_id));
            // Use free-flow weights for edges with no given weight.
            for edge_id in all_edges {
                w.entry(edge_id).or_insert_with(|| {
                    if nb_warnings < 5 {
                        warn!(
                            "No TTF given for edge {edge_id} with vehicle {}, \
                                using free-flow weight instead.",
                            vehicle.id
                        );
                        nb_warnings += 1;
                        if nb_warnings == 5 {
                            warn!("Skipping similar warnings...");
                        }
                    }
                    TTF::Constant(road_network.get_free_flow_travel_time_of_edge(edge_id, vehicle))
                });
            }
        }
        // Check if we got some weights for vehicles which are not part of the road network.
        let all_vehicles: HashSet<_> = road_network.iter_vehicles().map(|v| v.id).collect();
        let mut ids_to_remove = Vec::new();
        for vid in ttf_map.keys() {
            if !all_vehicles.contains(vid) {
                warn!(
                    "Vehicle id {vid} is in the road-network conditions but it is not part of \
                    the input vehicle types"
                );
                ids_to_remove.push(*vid);
            }
        }
        for vid in ids_to_remove {
            ttf_map.remove(&vid).unwrap();
        }
        // At this point, ttf_map has an entry for all vehicle types.
        let mut weights =
            Self::with_capacity(period, interval, unique_vehicles, road_network.nb_edges());
        let mut to_insert = Vec::new();
        for vweights in weights.weights.iter_mut() {
            // Set the weights to the input weights for the first vehicle id in the group.
            vweights.weights = ttf_map.remove(&vweights.vehicle_ids[0]).unwrap();
            // Check if the other vehcles in the group have the same input weight.
            for &vid in vweights.vehicle_ids[1..].iter() {
                let w = ttf_map.remove(&vid).unwrap();
                if w != vweights.weights {
                    // Different weights were given for this vehicle.
                    warn!(
                        "Vehicle id {vid} could share road-network conditions with \
                            vehicle id {} but different conditions were given",
                        vweights.vehicle_ids[0]
                    );
                    to_insert.push(VehicleWeights {
                        vehicle_ids: vec![vid],
                        weights: w,
                    });
                }
            }
        }
        for vw in to_insert {
            weights.weights.push(vw);
        }
        Ok(weights)
    }

    /// Returns the average between two RoadNetworkWeights, using the given coefficient.
    ///
    /// For each vehicle `v` and edge `e`, the weight of the new RoadNetworkWeights is `w_ve = a *
    /// w1_ve + (1 - a) * w2_ve`, where `a` is the coefficient, `w1_ve` is the weight of `self` and
    /// `w2_ve` is the weight of `other`.
    ///
    /// **Panics** if the two RoadNetworkWeights do not have the same shape.
    #[must_use]
    pub fn average(&self, other: &Self, coefficient: T) -> Self {
        let mut new_weights = RoadNetworkWeights::with_capacity_in(self);
        for (i, (self_weights, other_weights)) in self.iter().zip(other.iter()).enumerate() {
            assert_eq!(
                self_weights.len(),
                other_weights.len(),
                "Incompatible RoadNetworkWeights."
            );
            debug_assert_eq!(
                self_weights.vehicle_ids, other_weights.vehicle_ids,
                "The weights do not have the same vehicle ids"
            );
            debug_assert_eq!(new_weights.weights[i].vehicle_ids, self_weights.vehicle_ids);
            for (self_id, self_ttf) in self_weights.weights.iter() {
                if let Some(other_ttf) = other_weights.weights.get(self_id) {
                    new_weights.weights[i].weights.insert(
                        *self_id,
                        self_ttf.apply(other_ttf, |w1, w2| {
                            Time(coefficient * w1.0 + (T::one() - coefficient) * w2.0)
                        }),
                    );
                } else {
                    panic!("The weights do not have the same edge ids");
                }
            }
        }
        new_weights
    }

    /// Returns the genetic average between two RoadNetworkWeights, using the given exponents.
    ///
    /// For each vehicle `v` and edge `e`, the weight of the new RoadNetworkWeights is `w_ve =
    /// (w1_ve^a + w2_ve^b)^(1/(a+b))`, where `a` and `b` are the exponents, `w1_ve` is the weight
    /// of `self` and `w2_ve` is the weight of `other`.
    ///
    /// **Panics** if the two RoadNetworkWeights do not have the same shape.
    #[must_use]
    pub fn genetic_average(&self, other: &Self, a: T, b: T) -> Self {
        let mut new_weights = RoadNetworkWeights::with_capacity_in(self);
        for (i, (self_weights, other_weights)) in self.iter().zip(other.iter()).enumerate() {
            assert_eq!(
                self_weights.len(),
                other_weights.len(),
                "Incompatible RoadNetworkWeights."
            );
            debug_assert_eq!(
                self_weights.vehicle_ids, other_weights.vehicle_ids,
                "The weights do not have the same vehicle ids"
            );
            debug_assert_eq!(new_weights.weights[i].vehicle_ids, self_weights.vehicle_ids);
            for (self_id, self_ttf) in self_weights.weights.iter() {
                if let Some(other_ttf) = other_weights.weights.get(self_id) {
                    new_weights.weights[i].weights.insert(
                        *self_id,
                        self_ttf.apply(other_ttf, |w1, w2| {
                            Time(w1.0.powf(a / (a + b)) * w2.0.powf(b / (a + b)))
                        }),
                    );
                } else {
                    panic!("The weights do not have the same edge ids");
                }
            }
        }
        new_weights
    }

    /// Returns the root mean squared difference between `self` and `other`.
    pub fn rmse(&self, other: &Self) -> Time<T> {
        let mut rmse = Time::zero();
        let mut n = 0;
        for (self_weights, other_weights) in self.iter().zip(other.iter()) {
            assert_eq!(
                self_weights.len(),
                other_weights.len(),
                "Incompatible RoadNetworkWeights."
            );
            debug_assert_eq!(
                self_weights.vehicle_ids, other_weights.vehicle_ids,
                "The weights do not have the same vehicle ids"
            );
            for (self_id, self_ttf) in self_weights.weights.iter() {
                if let Some(other_ttf) = other_weights.weights.get(self_id) {
                    rmse += self_ttf.squared_difference(other_ttf);
                    n += 1;
                    debug_assert!(rmse.is_finite(), "{other_weights:?}");
                } else {
                    panic!("The weights do not have the same edge ids");
                }
            }
        }
        Time((rmse.0 / T::from_usize(n).unwrap()).sqrt())
    }

    /// Consumes a [RoadNetworkWeights] and returns a [RoadNetworkWeights] compatible with the
    /// given road network and preprocess data.
    ///
    /// - Extra weights are removed (weights for inaccessible edges).
    /// - Missing weights are set to free-flow weights (e.g., weights for extra unique vehicles).
    /// - Infinite weights are set to free-flow weights.
    pub fn with_road_network(
        mut self,
        road_network: &RoadNetwork<T>,
        preprocess_data: &RoadNetworkPreprocessingData<T>,
    ) -> Self {
        match self.len() as i64 - preprocess_data.unique_vehicles.len() as i64 {
            n if n > 0 => {
                warn!(
                    "The number of road-network weights sets is larger than the number of unique \
                    vehicles in the road network by {n}.\nThe extra set(s) are ignored."
                );
                self.weights.truncate(preprocess_data.unique_vehicles.len());
            }
            n if n < 0 => {
                warn!(
                    "The number of road-network weights sets is smaller than the number of unique \
                    vehicles in the road network by {n}.\nFree-flow weights will be used for the \
                    missing weights."
                );
            }
            _ => (),
        }
        let mut nb_warnings = 0;
        for (uid, unique_vehicle, vehicle_ids) in preprocess_data
            .unique_vehicles
            .iter_uniques_with_original_ids(&road_network.vehicles)
        {
            // Collect all the edges that can be accessed by the unique vehicle.
            let all_edges: HashSet<OriginalEdgeId> = road_network
                .iter_original_edge_ids()
                .filter(|&edge_id| unique_vehicle.can_access(edge_id))
                .collect();
            if let Some(weights) = self.weights.get_mut(uid.index()) {
                // Discard the weights of edges that cannot be accessed.
                weights
                    .weights
                    .retain(|edge_id, _| all_edges.contains(edge_id));
                // Use free-flow weights for edges with no given weight.
                for edge_id in all_edges {
                    weights
                        .weights
                        .entry(edge_id)
                        .and_modify(|ttf| {
                            if !ttf.get_max().is_finite() {
                                // The given weight is infinite: use free-flow weight instead.
                                *ttf = TTF::Constant(
                                    road_network
                                        .get_free_flow_travel_time_of_edge(edge_id, unique_vehicle),
                                );
                                if nb_warnings < 5 {
                                    warn!(
                                        "Infinite weights are not allowed \
                                        (edge {edge_id}, unique vehicle {uid:?}), \
                                        using free-flow weight instead."
                                    );
                                    nb_warnings += 1;
                                    if nb_warnings == 5 {
                                        warn!("Skipping similar warnings...");
                                    }
                                }
                            }
                        })
                        .or_insert_with(|| {
                            if nb_warnings < 5 {
                                warn!(
                                    "No weight given for edge {edge_id} with unique vehicle \
                                    {uid:?}, using free-flow weight instead."
                                );
                                nb_warnings += 1;
                                if nb_warnings == 5 {
                                    warn!("Skipping similar warnings...");
                                }
                            }
                            TTF::Constant(
                                road_network
                                    .get_free_flow_travel_time_of_edge(edge_id, unique_vehicle),
                            )
                        });
                }
            } else {
                // No weights for the given unique vehicle: insert free-flow weights.
                let weights: HashMap<OriginalEdgeId, TTF<Time<T>>> = all_edges
                    .into_iter()
                    .map(|edge_id| {
                        let tt =
                            road_network.get_free_flow_travel_time_of_edge(edge_id, unique_vehicle);
                        (edge_id, TTF::Constant(tt))
                    })
                    .collect();
                self.weights.push(VehicleWeights {
                    vehicle_ids: vehicle_ids.to_vec(),
                    weights,
                });
            }
        }
        self
    }
}

fn build_ttf<T: TTFNum>(
    mut xy_vec: XYVec<T>,
    period: Interval<T>,
    interval: Time<T>,
) -> Result<TTF<Time<T>>> {
    xy_vec.sort_by_key(|(x, _)| *x);
    if xy_vec[0].0 != period.start() {
        bail!(
            "Invalid starting departure time: {} (expected: {})",
            xy_vec[0].0 .0,
            period.start()
        );
    }
    if !xy_vec
        .iter()
        .zip(std::iter::successors(Some(period.start()), |&t| {
            Some(t + interval)
        }))
        .all(|(xy, xp_td)| xy.0 == xp_td)
    {
        bail!(
            "The departure time values are not evenly spaced with interval {}",
            interval.0
        );
    }
    let ttf = if xy_vec.iter().all(|xy| xy.1 == xy_vec[0].1) {
        TTF::Constant(xy_vec[0].1)
    } else {
        TTF::Piecewise(PwlTTF::from_values(
            xy_vec.into_iter().map(|xy| xy.1).collect(),
            period.start(),
            interval,
        ))
    };
    Ok(ttf)
}

impl<T> Index<UniqueVehicleIndex> for RoadNetworkWeights<T> {
    type Output = VehicleWeights<T>;
    fn index(&self, x: UniqueVehicleIndex) -> &Self::Output {
        &self.weights[x.index()]
    }
}

impl<T> IndexMut<UniqueVehicleIndex> for RoadNetworkWeights<T> {
    fn index_mut(&mut self, x: UniqueVehicleIndex) -> &mut Self::Output {
        &mut self.weights[x.index()]
    }
}

impl<T> Index<(UniqueVehicleIndex, OriginalEdgeId)> for RoadNetworkWeights<T> {
    type Output = TTF<Time<T>>;
    fn index(&self, (vehicle_id, edge_id): (UniqueVehicleIndex, OriginalEdgeId)) -> &Self::Output {
        &self.weights[vehicle_id.index()].weights[&edge_id]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn average_test() {
        let w0 = RoadNetworkWeights {
            weights: vec![VehicleWeights {
                vehicle_ids: vec![0],
                weights: [(0, TTF::Constant(Time(10.)))].into_iter().collect(),
            }],
            period: Interval([Time(0.0), Time(100.0)]),
            interval: Time(0.0),
        };
        let w1 = RoadNetworkWeights {
            weights: vec![VehicleWeights {
                vehicle_ids: vec![0],
                weights: [(0, TTF::Constant(Time(20.)))].into_iter().collect(),
            }],
            period: Interval([Time(0.0), Time(100.0)]),
            interval: Time(0.0),
        };
        // Result = 0.2 * 10 + 0.8 * 20 = 2 + 16 = 18.
        let w2 = vec![VehicleWeights {
            vehicle_ids: vec![0],
            weights: [(0, TTF::Constant(Time(18.)))].into_iter().collect(),
        }];
        assert_eq!(w0.average(&w1, 0.2).weights, w2);
    }

    #[test]
    fn genetic_average_test() {
        let w0 = RoadNetworkWeights {
            weights: vec![VehicleWeights {
                vehicle_ids: vec![0],
                weights: [(0, TTF::Constant(Time(2.)))].into_iter().collect(),
            }],
            period: Interval([Time(0.0), Time(100.0)]),
            interval: Time(0.0),
        };
        let w1 = RoadNetworkWeights {
            weights: vec![VehicleWeights {
                vehicle_ids: vec![0],
                weights: [(0, TTF::Constant(Time(3.)))].into_iter().collect(),
            }],
            period: Interval([Time(0.0), Time(100.0)]),
            interval: Time(0.0),
        };
        // Result = (2^3 * 3^2)^(1/5) = 72^(1/5).
        let w2 = vec![VehicleWeights {
            vehicle_ids: vec![0],
            weights: [(0, TTF::Constant(Time(72.0f64.powf(0.2))))]
                .into_iter()
                .collect(),
        }];
        assert_eq!(w0.genetic_average(&w1, 3.0, 2.0).weights, w2);
    }
}
