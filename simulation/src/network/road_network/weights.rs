//! Description of the [RoadNetworkWeights].
use super::vehicle::VehicleIndex;
use crate::units::Time;

use petgraph::graph::EdgeIndex;
use serde_derive::{Deserialize, Serialize};
use std::ops::{Index, IndexMut};
use ttf::{TTFNum, TTF};

/// Structure to store the travel-time functions of each edge of a [RoadNetwork], for each
/// [Vehicle].
///
/// The outer vector has the same length as the number of vehicles of the associated [RoadNetwork].
/// The inner vectors have all the same length (i.e., the RoadNetworkWeights represent a matrix)
/// which is equal to the number of edges of the associated [RoadNetwork].
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct RoadNetworkWeights<T>(Vec<Vec<TTF<Time<T>>>>);

impl<T> RoadNetworkWeights<T> {
    /// Initialize a new RoadNetworkWeights instance with enough capacity for the given number of
    /// vehicles and edges.
    pub fn with_capacity(nb_vehicles: usize, nb_edges: usize) -> Self {
        let mut vehicle_weights = Vec::new();
        vehicle_weights.resize_with(nb_vehicles, || Vec::with_capacity(nb_edges));
        RoadNetworkWeights(vehicle_weights)
    }

    /// Return the shape of the RoadNetworkWeights, i.e., a tuple with the number of vehicles and
    /// the number of edges.
    pub fn shape(&self) -> (usize, usize) {
        match self.0.len() {
            0 => (0, 0),
            nb_vehicles => (nb_vehicles, self.0[0].len()),
        }
    }
}

impl<T: TTFNum> RoadNetworkWeights<T> {
    /// Return the average between two RoadNetworkWeights, using the given coefficient.
    ///
    /// For each vehicle `v` and edge `e`, the weight of the new RoadNetworkWeights is `w_ve = a *
    /// w1_ve + (1 - a) * w2_ve`, where `a` is the coefficient, `w1_ve` is the weight of `self` and
    /// `w2_ve` is the weight of `other`.
    ///
    /// **Panics** if the two RoadNetworkWeights do not have the same shape.
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
                new_weights.0[i].push(self_ttf.apply(other_ttf, |w1, w2| {
                    Time(coefficient * w1.0 + (T::one() - coefficient) * w2.0)
                }));
            }
        }
        new_weights
    }

    /// Return the genetic average between two RoadNetworkWeights, using the given exponents.
    ///
    /// For each vehicle `v` and edge `e`, the weight of the new RoadNetworkWeights is `w_ve =
    /// (w1_ve^a + w2_ve^b)^(1/(a+b))`, where `a` and `b` are the exponents, `w1_ve` is the weight
    /// of `self` and `w2_ve` is the weight of `other`.
    ///
    /// **Panics** if the two RoadNetworkWeights do not have the same shape.
    #[must_use]
    pub fn genetic_average(&self, other: &Self, a: T, b: T) -> Self {
        assert_eq!(
            self.shape(),
            other.shape(),
            "Incompatible RoadNetworkWeights."
        );
        let (nb_vehicles, nb_edges) = self.shape();
        let mut new_weights = RoadNetworkWeights::with_capacity(nb_vehicles, nb_edges);
        for (i, (self_weights, other_weights)) in self.0.iter().zip(other.0.iter()).enumerate() {
            for (self_ttf, other_ttf) in self_weights.iter().zip(other_weights.iter()) {
                new_weights.0[i].push(self_ttf.apply(other_ttf, |w1, w2| {
                    Time(w1.0.powf(a / (a + b)) * w2.0.powf(b / (a + b)))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn average_test() {
        let w0 = RoadNetworkWeights(vec![vec![TTF::Constant(Time(10.))]]);
        let w1 = RoadNetworkWeights(vec![vec![TTF::Constant(Time(20.))]]);
        // Result = 0.2 * 10 + 0.8 * 20 = 2 + 16 = 18.
        let w2 = RoadNetworkWeights(vec![vec![TTF::Constant(Time(18.))]]);
        assert_eq!(w0.average(&w1, 0.2), w2);
    }

    #[test]
    fn genetic_average_test() {
        let w0 = RoadNetworkWeights(vec![vec![TTF::Constant(Time(2.))]]);
        let w1 = RoadNetworkWeights(vec![vec![TTF::Constant(Time(3.))]]);
        // Result = (2^3 * 3^2)^(1/5) = 72^(1/5).
        let w2 = RoadNetworkWeights(vec![vec![TTF::Constant(Time(72.0f64.powf(0.2)))]]);
        assert_eq!(w0.genetic_average(&w1, 3.0, 2.0), w2);
    }
}
