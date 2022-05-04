use super::vehicle::VehicleIndex;
use crate::units::Time;

use petgraph::graph::EdgeIndex;
use serde_derive::{Deserialize, Serialize};
use std::ops::{Index, IndexMut};
use ttf::{TTFNum, TTF};

/// Structure to store the travel-time functions of each edge of a [RoadNetwork], for each
/// [Vehicle].
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RoadNetworkWeights<T>(pub Vec<Vec<TTF<Time<T>>>>);

impl<T> RoadNetworkWeights<T> {
    /// Initialize a new RoadNetworkWeights instance with enough capacity for the given number of
    /// vehicles and edges.
    pub fn with_capacity(nb_vehicles: usize, nb_edges: usize) -> Self {
        let mut vehicle_weights = Vec::new();
        vehicle_weights.resize_with(nb_vehicles, || Vec::with_capacity(nb_edges));
        RoadNetworkWeights(vehicle_weights)
    }

    pub fn shape(&self) -> (usize, usize) {
        let nb_vehicles = self.0.len();
        if nb_vehicles == 0 {
            (0, 0)
        } else {
            (nb_vehicles, self.0[0].len())
        }
    }
}

impl<T: TTFNum> RoadNetworkWeights<T> {
    #[must_use]
    pub fn average(&self, other: &Self, coefficient: T) -> Self {
        assert_eq!(
            self.shape(),
            other.shape(),
            "Incompatible RoadNetworkWeights."
        );
        let (nb_vehicles, nb_edges) = self.shape();
        let mut new_weights = RoadNetworkWeights::with_capacity(nb_vehicles, nb_edges);
        for (i, (self_weights, other_weights)) in self.0.iter().zip(other.0.iter()).enumerate() {
            for (self_ttf, other_ttf) in self_weights.iter().zip(other_weights.iter()) {
                new_weights.0[i].push(self_ttf.apply(other_ttf, |a, b| {
                    Time(coefficient * a.0 + (T::one() - coefficient) * b.0)
                }));
            }
        }
        new_weights
    }

    #[must_use]
    pub fn genetic_average(&self, other: &Self, exponent: i32) -> Self {
        assert_eq!(
            self.shape(),
            other.shape(),
            "Incompatible RoadNetworkWeights."
        );
        let (nb_vehicles, nb_edges) = self.shape();
        let mut new_weights = RoadNetworkWeights::with_capacity(nb_vehicles, nb_edges);
        let exponent = T::from_i32(exponent).unwrap();
        for (i, (self_weights, other_weights)) in self.0.iter().zip(other.0.iter()).enumerate() {
            for (self_ttf, other_ttf) in self_weights.iter().zip(other_weights.iter()) {
                new_weights.0[i].push(self_ttf.apply(other_ttf, |a, b| {
                    Time(
                        a.0.powf(exponent / (T::one() + exponent))
                            * b.0.powf(T::one() / (T::one() + exponent)),
                    )
                }));
            }
        }
        new_weights
    }
}

impl<T> Index<VehicleIndex> for RoadNetworkWeights<T> {
    type Output = Vec<TTF<Time<T>>>;
    fn index(&self, x: VehicleIndex) -> &Self::Output {
        &self.0[x.index()]
    }
}

impl<T> IndexMut<VehicleIndex> for RoadNetworkWeights<T> {
    fn index_mut(&mut self, x: VehicleIndex) -> &mut Self::Output {
        &mut self.0[x.index()]
    }
}

impl<T> Index<(VehicleIndex, EdgeIndex)> for RoadNetworkWeights<T> {
    type Output = TTF<Time<T>>;
    fn index(&self, (vehicle, edge): (VehicleIndex, EdgeIndex)) -> &Self::Output {
        &self.0[vehicle.index()][edge.index()]
    }
}
