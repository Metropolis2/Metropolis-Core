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

//! Day-to-day learning models.
use serde_derive::Deserialize;

use crate::{network::NetworkWeights, units::*};

/// A learning model that specifies how to compute the new value `x_{t+1}`, given the old value
/// `x_t` and an update value `y`.
/// value.
#[derive(Clone, Debug, Default, Deserialize)]
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
    Exponential(ZeroOneNum),
    /// Exponential learning model with no adjustment for the initial weights:
    /// `x_{t+1} = alpha * x_t + (1 - alpha) * y`.
    ExponentialUnadjusted(ZeroOneNum),
    /// Linear learning model: `x_{t+1} = (t / (t + 1)) * x_t + (1 / (t + 1)) * y`
    #[default]
    Linear,
    /// Exponential model with no adjustment for the initial weights (see
    /// [ExponentialUnadjusted](Self::ExponentialUnadjusted)) for the first `nb_exponential`
    /// iterations, then Linear model (see [Linear](Self::Linear)) restarted from the learned
    /// values.
    ///
    /// The fast exponential phase quickly gets rid of the initial conditions; the Linear phase then
    /// averages all the following iterations with equal weights, so that the noise vanishes
    /// without keeping the early (very congested) iterations in memory.
    ///
    /// With `t` the iteration counter given to the learning model, `x_{t+1} = alpha * x_t + (1 -
    /// alpha) * y` if `t <= nb_exponential`, and `x_{t+1} = (s / (s + 1)) * x_t + (1 / (s + 1)) * y`
    /// with `s = t - nb_exponential` otherwise.
    ExponentialThenLinear {
        /// Parameter of the exponential phase.
        alpha: ZeroOneNum,
        /// Number of iterations of the exponential phase.
        nb_exponential: u32,
    },
    /// Exponential model with no adjustment for the initial weights (see
    /// [ExponentialUnadjusted](Self::ExponentialUnadjusted)) for the first `nb_exponential`
    /// iterations, then Exponential model with adjustment for the initial weights (see
    /// [Exponential](Self::Exponential)) with parameter `final_alpha`, at the same iteration counter
    /// (it is not restarted).
    ///
    /// The fast exponential phase quickly gets rid of the initial conditions;
    /// the second phase then keeps a memory of about `1 / final_alpha` iterations.
    ///
    /// With `t` the iteration counter given to the learning model, `x_{t+1} = (1 - alpha) * x_t +
    /// alpha * y` if `t <= nb_exponential`, and `x_{t+1} = (1 - w_t) * x_t + w_t * y` otherwise,
    /// where `w_t` is the weight of the update value of the `Exponential` model with parameter
    /// `final_alpha` at counter `t`.
    ExponentialThenExponential {
        /// Parameter of the first exponential phase.
        alpha: ZeroOneNum,
        /// Number of iterations of the first exponential phase.
        nb_exponential: u32,
        /// Parameter of the second exponential phase.
        final_alpha: ZeroOneNum,
    },
    /// Genetic learning model: `x_{t+1} = (x_t^t * y)^(1 / (t + 1))`
    Genetic,
    /// Quadratic learning model: `x_{t+1} = (w / (w + 1)) * x_t + (1 / (w + 1)) * y` where
    /// `w = t^(1/2)`
    Quadratic,
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
            Self::Genetic => {
                let t = iteration_counter as f64;
                old_weights.genetic_average(update_weights, t, 1.0)
            }
            _ => {
                // The weight of the update value is between 0 and 1.
                let coef_old = 1. - self.update_weight(iteration_counter);
                old_weights.average(update_weights, ZeroOneNum::new_unchecked(coef_old))
            }
        }
    }

    /// Returns the weight of the update value `y` in the new value `x_{t+1}` computed by
    /// [learn](Self::learn) with the given iteration counter (for the Genetic model, the exponent
    /// of `y`).
    ///
    /// For the `Exponential` model, the formula corrects the weight of the first values (with
    /// `alpha = 0`, it is the Linear model).
    pub fn update_weight(&self, iteration_counter: u32) -> f64 {
        let t = iteration_counter as f64;
        match self {
            &Self::Exponential(alpha) => {
                let alpha = f64::from(alpha);
                if alpha == 1. {
                    1.
                } else if alpha == 0. {
                    Self::Linear.update_weight(iteration_counter)
                } else {
                    // At most 1 (the weight is 1 at counter 0, up to rounding errors).
                    (alpha / (1. - (1. - alpha).powi(iteration_counter as i32 + 1))).min(1.)
                }
            }
            &Self::ExponentialUnadjusted(alpha) => f64::from(alpha),
            &Self::ExponentialThenLinear {
                alpha,
                nb_exponential,
            } => {
                if iteration_counter <= nb_exponential {
                    f64::from(alpha)
                } else {
                    Self::Linear.update_weight(iteration_counter - nb_exponential)
                }
            }
            &Self::ExponentialThenExponential {
                alpha,
                nb_exponential,
                final_alpha,
            } => {
                if iteration_counter <= nb_exponential {
                    f64::from(alpha)
                } else {
                    Self::Exponential(final_alpha).update_weight(iteration_counter)
                }
            }
            Self::Linear | Self::Genetic => 1. / (t + 1.),
            Self::Quadratic => 1. / (t.sqrt() + 1.),
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

    fn get_weigths(v: f64) -> NetworkWeights {
        let id = MetroId::Integer(0);
        let rn = RoadNetworkWeights {
            weights: vec![VehicleWeights {
                weights: [(id, TTF::Constant(AnySeconds::new_unchecked(v)))]
                    .into_iter()
                    .collect(),
                vehicle_ids: vec![id],
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
        let id = MetroId::Integer(0);
        let w1 = get_weigths(10.);
        let w2 = get_weigths(20.);
        let w3 = get_weigths(30.);
        let model = LearningModel::Exponential(ZeroOneNum::new_unchecked(0.2));
        assert_eq!(
            model.learn(&w1, &w2, 0).road_network().unwrap().weights,
            get_weigths(20.).road_network().unwrap().weights
        );
        let x2 = model.learn(&w1, &w2, 1);
        if let TTF::Constant(v) = x2.road_network().unwrap()[(uid, id)] {
            let expected = (20. + 0.8 * 10.) * 0.2 / (1. - 0.8f64.powi(2));
            assert!(
                (Into::<f64>::into(v) - expected).abs() < 1e-4,
                "{:?} != {:?}",
                v,
                expected
            );
        } else {
            panic!("Invalid road network weight: {:?}", x2.road_network());
        }
        let x3 = model.learn(&x2, &w3, 2);
        if let TTF::Constant(v) = x3.road_network().unwrap()[(uid, id)] {
            let expected = (30. + 0.8 * 20. + 0.8f64.powi(2) * 10.) * 0.2 / (1. - 0.8f64.powi(3));
            assert!(
                (Into::<f64>::into(v) - expected).abs() < 1e-4,
                "{:?} != {:?}",
                v,
                expected
            );
        } else {
            panic!("Invalid road network weight: {:?}", x3.road_network());
        }
    }

    #[test]
    fn exponential_then_linear_learning_test() {
        let old_weights = get_weigths(10.);
        let update_weights = get_weigths(20.);
        let model = LearningModel::ExponentialThenLinear {
            alpha: ZeroOneNum::new_unchecked(0.2),
            nb_exponential: 5,
        };
        // Exponential phase: 0.8 * 10 + 0.2 * 20 = 12.
        for t in [1, 5] {
            assert_eq!(
                model
                    .learn(&old_weights, &update_weights, t)
                    .road_network()
                    .unwrap()
                    .weights,
                get_weigths(12.).road_network().unwrap().weights
            );
        }
        // Linear phase, restarted after the exponential phase (s = 1 and s = 4).
        for (t, expected) in [(6, 15.), (9, 12.)] {
            assert_eq!(
                model
                    .learn(&old_weights, &update_weights, t)
                    .road_network()
                    .unwrap()
                    .weights,
                get_weigths(expected).road_network().unwrap().weights
            );
        }
    }

    #[test]
    fn exponential_then_exponential_learning_test() {
        let old_weights = get_weigths(10.);
        let update_weights = get_weigths(20.);
        let model = LearningModel::ExponentialThenExponential {
            alpha: ZeroOneNum::new_unchecked(0.5),
            nb_exponential: 5,
            final_alpha: ZeroOneNum::new_unchecked(0.2),
        };
        // First phase: 0.5 * 10 + 0.5 * 20 = 15.
        for t in [1, 5] {
            assert_eq!(
                model
                    .learn(&old_weights, &update_weights, t)
                    .road_network()
                    .unwrap()
                    .weights,
                get_weigths(15.).road_network().unwrap().weights
            );
        }
        // Second phase: weight of `Exponential` 0.2 at the same counter (not restarted).
        let exponential = LearningModel::Exponential(ZeroOneNum::new_unchecked(0.2));
        for t in [6, 9, 100] {
            assert_eq!(model.update_weight(t), exponential.update_weight(t));
        }
        assert!((model.update_weight(6) - 0.2 / (1. - 0.8f64.powi(7))).abs() < 1e-12);
        // Input format.
        let parsed: LearningModel = serde_json::from_str(
            r#"{"type": "ExponentialThenExponential",
            "value": {"alpha": 0.5, "nb_exponential": 5, "final_alpha": 0.2}}"#,
        )
        .unwrap();
        assert_eq!(parsed.update_weight(5), 0.5);
        assert_eq!(parsed.update_weight(6), exponential.update_weight(6));
    }

    #[test]
    fn update_weight_test() {
        let uid = unique_vehicle_index(0);
        let id = MetroId::Integer(0);
        let alpha = ZeroOneNum::new_unchecked(0.2);
        let models = [
            LearningModel::Exponential(alpha),
            LearningModel::Exponential(ZeroOneNum::new_unchecked(0.)),
            LearningModel::Exponential(ZeroOneNum::new_unchecked(1.)),
            LearningModel::ExponentialUnadjusted(alpha),
            LearningModel::ExponentialThenLinear {
                alpha,
                nb_exponential: 5,
            },
            LearningModel::ExponentialThenExponential {
                alpha: ZeroOneNum::new_unchecked(0.5),
                nb_exponential: 5,
                final_alpha: alpha,
            },
            LearningModel::Linear,
            LearningModel::Quadratic,
        ];
        // From 10 to 20, the learned value is 10 + 10 * weight.
        for model in models.iter() {
            for t in [0, 1, 2, 5, 6, 9, 100] {
                let learned = model.learn(&get_weigths(10.), &get_weigths(20.), t);
                let TTF::Constant(v) = learned.road_network().unwrap()[(uid, id)] else {
                    panic!("Invalid road network weight");
                };
                let expected = 10. + 10. * model.update_weight(t);
                assert!(
                    (f64::from(v) - expected).abs() < 1e-9,
                    "{model:?} at {t}: {v:?} != {expected}"
                );
            }
        }
        // Weight of a day with `Exponential` 0.02: about 50% at counter 1, 2% when large.
        let model = LearningModel::Exponential(ZeroOneNum::new_unchecked(0.02));
        assert!((model.update_weight(1) - 0.02 / (1. - 0.98f64.powi(2))).abs() < 1e-12);
        assert!((model.update_weight(1000) - 0.02).abs() < 1e-6);
    }
}
