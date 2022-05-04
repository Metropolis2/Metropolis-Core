use crate::network::NetworkWeights;

use anyhow::{anyhow, Result};
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum LearningModel<T> {
    Exponential(ExponentialLearningModel<T>),
    Linear,
    Genetic,
}

impl<T: TTFNum> LearningModel<T> {
    pub fn learn(
        &self,
        old_weights: &NetworkWeights<T>,
        new_weights: &NetworkWeights<T>,
        iteration_counter: u64,
    ) -> NetworkWeights<T> {
        match self {
            Self::Exponential(model) => model.learn(old_weights, new_weights, iteration_counter),
            Self::Linear => {
                let v = iteration_counter as f64 / (iteration_counter + 1) as f64;
                let coef = T::from(v).unwrap_or_else(|| panic!("Cannot convert {:?} to TTFNum", v));
                old_weights.average(new_weights, coef)
            }
            Self::Genetic => old_weights.genetic_average(new_weights, iteration_counter as i32),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(transparent)]
pub struct ExponentialLearningModel<T> {
    /// Weight of the past value, between 0.0 and 1.0.
    alpha: T,
}

impl<T: TTFNum> ExponentialLearningModel<T> {
    pub fn new(alpha: T) -> Result<Self> {
        if !(T::zero()..=T::one()).contains(&alpha) {
            Err(anyhow!(
                "The value of alpha must be such that 0.0 <= alpha <= 1.0, got {:?}",
                alpha
            ))
        } else {
            Ok(ExponentialLearningModel { alpha })
        }
    }

    pub fn learn(
        &self,
        old_weights: &NetworkWeights<T>,
        new_weights: &NetworkWeights<T>,
        iteration_counter: u64,
    ) -> NetworkWeights<T> {
        // Use the formula to correct the weight of the first value.
        let coef_new = if self.alpha == T::zero() {
            T::one()
        } else if self.alpha == T::one() {
            T::zero()
        } else {
            (T::one() - self.alpha) / (T::one() - self.alpha.powi(iteration_counter as i32 + 1))
        };
        old_weights.average(new_weights, T::one() - coef_new)
    }
}
