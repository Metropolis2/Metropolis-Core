// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Day-to-day learning models.
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::network::NetworkWeights;

/// A learning model that specifies how to compute the new value `x_{t+1}`, given the old value
/// `x_t` and an update value `y`.
/// value.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "values")]
pub enum LearningModel<T> {
    /// Exponential learning model.
    Exponential(ExponentialLearningModel<T>),
    /// Linear learning model: `x_{t+1} = (t / (t + 1)) * x_t + (1 / (t + 1)) * y`
    Linear,
    /// Genetic learning model: `x_{t+1} = (x_t^t * y)^(1 / (t + 1))`
    Genetic,
    /// Quadratic learning model: `x_{t+1} = (w / (w + 1)) * x_t + (1 / (w + 1)) * y` where
    /// `w = t^(1/2)`
    Quadratic,
}

impl<T> Default for LearningModel<T> {
    fn default() -> Self {
        Self::Linear
    }
}

impl<T: TTFNum> LearningModel<T> {
    /// Returns the new [NetworkWeights] given the old values, the update values and the iteration
    /// counter.
    ///
    /// **Panics** if the iteration counter cannot be converted to `T`.
    pub fn learn(
        &self,
        old_weights: &NetworkWeights<T>,
        update_weights: &NetworkWeights<T>,
        iteration_counter: u64,
    ) -> NetworkWeights<T> {
        match self {
            Self::Exponential(model) => model.learn(old_weights, update_weights, iteration_counter),
            Self::Linear => {
                let t = T::from_u64(iteration_counter)
                    .unwrap_or_else(|| panic!("Cannot convert {:?} to TTFNum", iteration_counter));
                let coef = t / (t + T::one());
                old_weights.average(update_weights, coef)
            }
            Self::Genetic => {
                let t = T::from_u64(iteration_counter)
                    .unwrap_or_else(|| panic!("Cannot convert {:?} to TTFNum", iteration_counter));
                old_weights.genetic_average(update_weights, t, T::one())
            }
            Self::Quadratic => {
                let t = T::from_u64(iteration_counter)
                    .unwrap_or_else(|| panic!("Cannot convert {:?} to TTFNum", iteration_counter));
                let coef = t.sqrt() / (t.sqrt() + T::one());
                old_weights.average(update_weights, coef)
            }
        }
    }
}

/// An exponential learning model.
///
/// The average value at iteration `T`, `x_T`, is a mean of the update values `y_t` at each
/// iteration `t`, where the coefficient of the update value `y_t` is
/// `(1 - alpha) * alpha^(T - t) / (1 - alpha^T)`.
///
/// When `T` is large, the exponential learning model is such that
/// `x_{t+1} = alpha * x_t + (1 - alpha) * y_{t+1}`
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub struct ExponentialLearningModel<T> {
    /// Weight of the old value, between 0 and 1.
    #[validate(range(min = 0.0, max = 1.0))]
    alpha: T,
}

impl<T: TTFNum> ExponentialLearningModel<T> {
    /// Creates a new exponential learning model.
    pub fn new(alpha: T) -> Self {
        ExponentialLearningModel { alpha }
    }

    /// Returns the new [NetworkWeights] given the old values, the update values and the iteration
    /// counter.
    pub fn learn(
        &self,
        old_weights: &NetworkWeights<T>,
        update_weights: &NetworkWeights<T>,
        iteration_counter: u64,
    ) -> NetworkWeights<T> {
        // Use the formula to correct the weight of the first value.
        let coef_update = if self.alpha == T::zero() {
            T::one()
        } else if self.alpha == T::one() {
            T::zero()
        } else {
            (T::one() - self.alpha) / (T::one() - self.alpha.powi(iteration_counter as i32 + 1))
        };
        old_weights.average(update_weights, T::one() - coef_update)
    }
}

#[cfg(test)]
mod tests {
    use ttf::TTF;

    use super::*;
    use crate::network::road_network::vehicle::vehicle_index;
    use crate::network::road_network::weights::RoadNetworkWeights;
    use crate::units::Time;

    fn get_weigths(v: f64) -> NetworkWeights<f64> {
        let mut rn = RoadNetworkWeights::with_capacity(1, 1);
        rn[vehicle_index(0)].push(TTF::Constant(Time(v)));
        NetworkWeights::new(Some(rn))
    }

    #[test]
    fn linear_learning_test() {
        let old_weights = get_weigths(10.);
        let update_weights = get_weigths(20.);
        let model = LearningModel::Linear;
        assert_eq!(
            model.learn(&old_weights, &update_weights, 0),
            get_weigths(20.)
        );
        assert_eq!(
            model.learn(&old_weights, &update_weights, 1),
            get_weigths(15.)
        );
        assert_eq!(
            model.learn(&old_weights, &update_weights, 4),
            get_weigths(12.)
        );
        assert_eq!(
            model.learn(&old_weights, &update_weights, 9),
            get_weigths(11.)
        );
    }

    #[test]
    fn quadratic_learning_test() {
        let old_weights = get_weigths(10.);
        let update_weights = get_weigths(20.);
        let model = LearningModel::Quadratic;
        assert_eq!(
            model.learn(&old_weights, &update_weights, 0),
            get_weigths(20.)
        );
        assert_eq!(
            model.learn(&old_weights, &update_weights, 1),
            get_weigths(15.)
        );
        assert_eq!(
            model.learn(&old_weights, &update_weights, 16),
            get_weigths(12.)
        );
        assert_eq!(
            model.learn(&old_weights, &update_weights, 81),
            get_weigths(11.)
        );
    }

    #[test]
    fn exponential_learning_test() {
        let w1 = get_weigths(10.);
        let w2 = get_weigths(20.);
        let w3 = get_weigths(30.);
        let exp_model = ExponentialLearningModel::new(0.8);
        let model = LearningModel::Exponential(exp_model);
        assert_eq!(model.learn(&w1, &w2, 0), get_weigths(20.));
        let x2 = model.learn(&w1, &w2, 1);
        if let TTF::Constant(v) = x2.get_road_network().unwrap()[vehicle_index(0)][0] {
            let expected = Time((20. + 0.8 * 10.) * 0.2 / (1. - 0.8f64.powi(2)));
            assert!(v.approx_eq(&expected), "{:?} != {:?}", v, expected);
        } else {
            panic!("Invalid road network weight: {:?}", x2.get_road_network());
        }
        let x3 = model.learn(&x2, &w3, 2);
        if let TTF::Constant(v) = x3.get_road_network().unwrap()[vehicle_index(0)][0] {
            let expected =
                Time((30. + 0.8 * 20. + 0.8f64.powi(2) * 10.) * 0.2 / (1. - 0.8f64.powi(3)));
            assert!(v.approx_eq(&expected), "{:?} != {:?}", v, expected);
        } else {
            panic!("Invalid road network weight: {:?}", x3.get_road_network());
        }
    }
}
