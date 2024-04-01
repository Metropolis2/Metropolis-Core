// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Day-to-day learning models.
use num_traits::{Float, One, Zero};
use serde_derive::{Deserialize, Serialize};

use crate::network::NetworkWeights;
use crate::units::NoUnit;

/// A learning model that specifies how to compute the new value `x_{t+1}`, given the old value
/// `x_t` and an update value `y`.
/// value.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "type", content = "value")]
pub enum LearningModel {
    /// Exponential learning model with adjustment for the initial weights.
    ///
    /// The average value at iteration `T`, `x_T`, is a mean of the update values `y_t` at each
    /// iteration `t`, where the coefficient of the update value `y_t` is
    /// `(1 - alpha) * alpha^(T - t) / (1 - alpha^T)`.
    ///
    /// When `T` is large, the exponential learning model is such that
    /// `x_{t+1} = alpha * x_t + (1 - alpha) * y_{t+1}`
    Exponential(NoUnit),
    /// Exponential learning model with no adjustment for the initial weights:
    /// `x_{t+1} = alpha * x_t + (1 - alpha) * y`.
    ExponentialUnadjusted(NoUnit),
    /// Linear learning model: `x_{t+1} = (t / (t + 1)) * x_t + (1 / (t + 1)) * y`
    Linear,
    /// Genetic learning model: `x_{t+1} = (x_t^t * y)^(1 / (t + 1))`
    Genetic,
    /// Quadratic learning model: `x_{t+1} = (w / (w + 1)) * x_t + (1 / (w + 1)) * y` where
    /// `w = t^(1/2)`
    Quadratic,
}

impl Default for LearningModel {
    fn default() -> Self {
        Self::Linear
    }
}

impl LearningModel {
    /// Returns the new [NetworkWeights] given the old values, the update values and the iteration
    /// counter.
    ///
    /// **Panics** if the iteration counter cannot be converted to `T`.
    pub fn learn(
        &self,
        old_weights: &NetworkWeights,
        update_weights: &NetworkWeights,
        iteration_counter: u32,
    ) -> NetworkWeights {
        match self {
            &Self::Exponential(alpha) => {
                // Use the formula to correct the weight of the first value.
                let coef_update = if alpha == NoUnit::one() {
                    NoUnit::one()
                } else if alpha == NoUnit::zero() {
                    // With `alpha = 0`, we resort to Linear learning.
                    return Self::Linear.learn(old_weights, update_weights, iteration_counter);
                } else {
                    alpha
                        / (NoUnit::one()
                            - (NoUnit::one() - alpha).powi(iteration_counter as i32 + 1))
                };
                old_weights.average(update_weights, 1.0 - coef_update.0)
            }
            &Self::ExponentialUnadjusted(alpha) => {
                old_weights.average(update_weights, 1.0 - alpha.0)
            }
            Self::Linear => {
                let t = iteration_counter as f64;
                let coef = t / (t + 1.0);
                old_weights.average(update_weights, coef)
            }
            Self::Genetic => {
                let t = iteration_counter as f64;
                old_weights.genetic_average(update_weights, t, 1.0)
            }
            Self::Quadratic => {
                let t = iteration_counter as f64;
                let coef = t.sqrt() / (t.sqrt() + 1.0);
                old_weights.average(update_weights, coef)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ttf::TTF;

    use super::*;
    use crate::network::road_network::preprocess::unique_vehicle_index;
    use crate::network::road_network::weights::VehicleWeights;
    use crate::network::road_network::RoadNetworkWeights;
    use crate::units::Time;

    fn get_weigths(v: f64) -> NetworkWeights {
        let rn = RoadNetworkWeights {
            weights: vec![VehicleWeights {
                weights: [(0, TTF::Constant(Time(v)))].into_iter().collect(),
                vehicle_ids: vec![0],
            }],
        };
        NetworkWeights::new(Some(rn))
    }

    #[test]
    fn linear_learning_test() {
        let old_weights = get_weigths(10.);
        let update_weights = get_weigths(20.);
        let model = LearningModel::Linear;
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 0)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(20.).road_network().unwrap().weights
        );
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 1)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(15.).road_network().unwrap().weights
        );
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 4)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(12.).road_network().unwrap().weights
        );
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 9)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(11.).road_network().unwrap().weights
        );
    }

    #[test]
    fn quadratic_learning_test() {
        let old_weights = get_weigths(10.);
        let update_weights = get_weigths(20.);
        let model = LearningModel::Quadratic;
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 0)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(20.).road_network().unwrap().weights
        );
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 1)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(15.).road_network().unwrap().weights
        );
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 16)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(12.).road_network().unwrap().weights
        );
        assert_eq!(
            model
                .learn(&old_weights, &update_weights, 81)
                .road_network()
                .unwrap()
                .weights,
            get_weigths(11.).road_network().unwrap().weights
        );
    }

    #[test]
    fn exponential_learning_test() {
        let uid = unique_vehicle_index(0);
        let w1 = get_weigths(10.);
        let w2 = get_weigths(20.);
        let w3 = get_weigths(30.);
        let model = LearningModel::Exponential(NoUnit(0.2));
        assert_eq!(
            model.learn(&w1, &w2, 0).road_network().unwrap().weights,
            get_weigths(20.).road_network().unwrap().weights
        );
        let x2 = model.learn(&w1, &w2, 1);
        if let TTF::Constant(v) = x2.road_network().unwrap()[(uid, 0)] {
            let expected = (20. + 0.8 * 10.) * 0.2 / (1. - 0.8f64.powi(2));
            assert!((v.0 - expected).abs() < 1e-4, "{:?} != {:?}", v, expected);
        } else {
            panic!("Invalid road network weight: {:?}", x2.road_network());
        }
        let x3 = model.learn(&x2, &w3, 2);
        if let TTF::Constant(v) = x3.road_network().unwrap()[(uid, 0)] {
            let expected = (30. + 0.8 * 20. + 0.8f64.powi(2) * 10.) * 0.2 / (1. - 0.8f64.powi(3));
            assert!((v.0 - expected).abs() < 1e-4, "{:?} != {:?}", v, expected);
        } else {
            panic!("Invalid road network weight: {:?}", x3.road_network());
        }
    }
}
