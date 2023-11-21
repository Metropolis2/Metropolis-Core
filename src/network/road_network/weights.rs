// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode
//! Description of the [RoadNetworkWeights].
#![allow(clippy::disallowed_types)]
use std::ops::{Index, IndexMut};

use hashbrown::{HashMap, HashSet};
use log::warn;
use num_traits::{Float, Zero};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::{TTFNum, TTF};

use super::{OriginalEdgeIndex, RoadNetwork, RoadNetworkPreprocessingData};
use crate::units::Time;

/// Structure to store the travel-time functions of each edge of a
/// [RoadNetwork](super::RoadNetwork), for each unique vehicle type.
///
/// The outer vector has the same length as the number of unique vehicles of the associated
/// [RoadNetwork](super::RoadNetwork).
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(title = "Road Network Weights")]
#[schemars(
    description = "Travel-time functions of each edge of road network, for each unique vehicle \
    (outer array)."
)]
pub struct RoadNetworkWeights<T>(
    #[schemars(with = "Vec<std::collections::HashMap<OriginalEdgeIndex, TTF<Time<T>>>>")]
    Vec<HashMap<OriginalEdgeIndex, TTF<Time<T>>>>,
);

impl<T> RoadNetworkWeights<T> {
    /// Initializes a new RoadNetworkWeights instance with enough capacity for the given number of
    /// unique vehicles and edges.
    pub fn with_capacity(nb_unique_vehicles: usize, nb_edges: usize) -> Self {
        let mut vehicle_weights = Vec::new();
        vehicle_weights.resize_with(nb_unique_vehicles, || HashMap::with_capacity(nb_edges));
        RoadNetworkWeights(vehicle_weights)
    }

    /// Initializes a new RoadNetworkWeights instance with the same capacity as the given
    /// RoadNetworkWeights.
    pub fn with_capacity_in(instance: &Self) -> Self {
        let mut vehicle_weights = Vec::with_capacity(instance.len());
        for weights in instance.0.iter() {
            vehicle_weights.push(HashMap::with_capacity(weights.len()));
        }
        RoadNetworkWeights(vehicle_weights)
    }

    /// Returns `true` if the [RoadNetworkWeights] is empty, i.e., there is no unique vehicle.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of unique vehicles in the weights.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns the [TTF] corresponding to the given vehicle id and edge.
    ///
    /// Returns `None` if the edge is not accessible for the given vehicle.
    pub fn get(&self, vehicle_id: usize, edge_id: OriginalEdgeIndex) -> Option<&TTF<Time<T>>> {
        self.0[vehicle_id].get(&edge_id)
    }
}

impl<T: TTFNum> RoadNetworkWeights<T> {
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
        for (i, (self_weights, other_weights)) in self.0.iter().zip(other.0.iter()).enumerate() {
            assert_eq!(
                self_weights.len(),
                other_weights.len(),
                "Incompatible RoadNetworkWeights."
            );
            for (self_id, self_ttf) in self_weights.iter() {
                if let Some(other_ttf) = other_weights.get(self_id) {
                    new_weights.0[i].insert(
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
        for (i, (self_weights, other_weights)) in self.0.iter().zip(other.0.iter()).enumerate() {
            assert_eq!(
                self_weights.len(),
                other_weights.len(),
                "Incompatible RoadNetworkWeights."
            );
            for (self_id, self_ttf) in self_weights.iter() {
                if let Some(other_ttf) = other_weights.get(self_id) {
                    new_weights.0[i].insert(
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
        for (self_weights, other_weights) in self.0.iter().zip(other.0.iter()) {
            assert_eq!(
                self_weights.len(),
                other_weights.len(),
                "Incompatible RoadNetworkWeights."
            );
            for (self_id, self_ttf) in self_weights.iter() {
                if let Some(other_ttf) = other_weights.get(self_id) {
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
        for (i, unique_vehicle) in preprocess_data
            .unique_vehicles
            .iter_uniques(&road_network.vehicles)
        {
            // Collect all the edges that can be accessed by the unique vehicle.
            let all_edges: HashSet<OriginalEdgeIndex> = road_network
                .iter_original_edge_ids()
                .filter(|&edge_id| unique_vehicle.can_access(edge_id))
                .collect();
            if let Some(weights) = self.0.get_mut(i) {
                // Discard the weights of edges that cannot be accessed.
                weights.retain(|edge_id, _| all_edges.contains(edge_id));
                // Use free-flow weights for edges with no given weight.
                for edge_id in all_edges {
                    weights
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
                                        (edge {edge_id}, unique vehicle {i}), \
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
                                    "No weight given for edge {edge_id} with unique vehicle {i}, \
                                    using free-flow weight instead."
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
                let weights: HashMap<OriginalEdgeIndex, TTF<Time<T>>> = all_edges
                    .into_iter()
                    .map(|edge_id| {
                        let tt =
                            road_network.get_free_flow_travel_time_of_edge(edge_id, unique_vehicle);
                        (edge_id, TTF::Constant(tt))
                    })
                    .collect();
                self.0.push(weights);
            }
        }
        self
    }
}

impl<T> Index<usize> for RoadNetworkWeights<T> {
    type Output = HashMap<OriginalEdgeIndex, TTF<Time<T>>>;
    fn index(&self, x: usize) -> &Self::Output {
        &self.0[x]
    }
}

impl<T> IndexMut<usize> for RoadNetworkWeights<T> {
    fn index_mut(&mut self, x: usize) -> &mut Self::Output {
        &mut self.0[x]
    }
}

impl<T> Index<(usize, OriginalEdgeIndex)> for RoadNetworkWeights<T> {
    type Output = TTF<Time<T>>;
    fn index(&self, (vehicle_id, edge_id): (usize, OriginalEdgeIndex)) -> &Self::Output {
        &self.0[vehicle_id][&edge_id]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn average_test() {
        let w0 = RoadNetworkWeights(vec![[(0, TTF::Constant(Time(10.)))].into_iter().collect()]);
        let w1 = RoadNetworkWeights(vec![[(0, TTF::Constant(Time(20.)))].into_iter().collect()]);
        // Result = 0.2 * 10 + 0.8 * 20 = 2 + 16 = 18.
        let w2 = RoadNetworkWeights(vec![[(0, TTF::Constant(Time(18.)))].into_iter().collect()]);
        assert_eq!(w0.average(&w1, 0.2), w2);
    }

    #[test]
    fn genetic_average_test() {
        let w0 = RoadNetworkWeights(vec![[(0, TTF::Constant(Time(2.)))].into_iter().collect()]);
        let w1 = RoadNetworkWeights(vec![[(0, TTF::Constant(Time(3.)))].into_iter().collect()]);
        // Result = (2^3 * 3^2)^(1/5) = 72^(1/5).
        let w2 = RoadNetworkWeights(vec![[(0, TTF::Constant(Time(72.0f64.powf(0.2))))]
            .into_iter()
            .collect()]);
        assert_eq!(w0.genetic_average(&w1, 3.0, 2.0), w2);
    }
}
