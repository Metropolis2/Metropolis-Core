// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Discrete and continuous choice models.
#![doc(html_no_source)]

mod deterministic_choice;
mod logit;
mod schema;

use anyhow::{anyhow, bail, Result};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::{PwlXYF, TTFNum};

pub use self::deterministic_choice::DeterministicChoiceModel;
pub use self::logit::LogitModel;

/// A choice model between a finite number of alternatives.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
#[schemars(example = "crate::schema::example_choice_model")]
pub enum ChoiceModel<T> {
    /// Choose the alternative with the largest utility.
    Deterministic(DeterministicChoiceModel<T>),
    /// Choose the alternative using Logit probabilities.
    Logit(LogitModel<T>),
}

impl<T: TTFNum> ChoiceModel<T> {
    /// Creates a new [ChoiceModel] from deserialized values.
    pub fn from_values(
        model_type: Option<&str>,
        u: Option<f64>,
        mu: Option<f64>,
        constants: Option<Vec<f64>>,
    ) -> Result<Self> {
        match model_type {
            Some("Logit") => {
                let u =
                    u.ok_or_else(|| anyhow!("Value `u` is mandatory when `type` is \"Logit\""))?;
                if !((0.0..=1.0).contains(&u)) {
                    bail!("Value `u` must be between 0 and 1, got {u}");
                }
                let mu =
                    mu.ok_or_else(|| anyhow!("Value `mu` is mandatory when `type` is \"Logit\""))?;
                if mu <= 0.0 {
                    bail!("Value `mu` must be positive, got {mu}");
                }
                Ok(ChoiceModel::Logit(LogitModel::new(
                    T::from_f64(u).unwrap(),
                    T::from_f64(mu).unwrap(),
                )))
            }
            Some("Deterministic") => {
                let u =
                    u.ok_or_else(|| anyhow!("Value `u` is mandatory when `type` is \"Logit\""))?;
                if !((0.0..=1.0).contains(&u)) {
                    bail!("Value `u` must be between 0 and 1, got {u}");
                }
                let u = T::from_f64(u).unwrap();
                if let Some(csts) = constants {
                    let constants = csts.into_iter().map(|v| T::from_f64(v).unwrap()).collect();
                    Ok(ChoiceModel::Deterministic(
                        DeterministicChoiceModel::new_with_constants(u, constants),
                    ))
                } else {
                    Ok(ChoiceModel::Deterministic(DeterministicChoiceModel::new(u)))
                }
            }
            Some(s) => Err(anyhow!("Unknown `type`: {s}")),
            None => Err(anyhow!(
                "Value `type` is mandatory for a discrete choice model"
            )),
        }
    }

    /// Returns the index of the chosen alternative and the expected utility of the choice, given
    /// the vector of values of the alternatives.
    pub fn get_choice<V: TTFNum + Into<T> + From<T>>(&self, values: &[V]) -> Result<(usize, V)> {
        match self {
            Self::Deterministic(model) => model.get_choice(values),
            Self::Logit(model) => model.get_choice(values),
        }
    }
}

/// A boxed callback function that returns the chosen (continuous) value.
pub type ContinuousChoiceCallback<'a, T> = Box<dyn FnOnce() -> T + 'a>;

/// A choice model between a continuous number of ordered alternatives.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum ContinuousChoiceModel<T> {
    /// Choose the alternative using Continuous Logit probabilities.
    Logit(LogitModel<T>),
}

impl<T: TTFNum> ContinuousChoiceModel<T> {
    /// Creates a new [ContinuousChoiceModel] from deserialized values.
    pub fn from_values(model_type: Option<&str>, u: Option<f64>, mu: Option<f64>) -> Result<Self> {
        match model_type {
            Some("Logit") => {
                let u =
                    u.ok_or_else(|| anyhow!("Value `u` is mandatory when `type` is \"Logit\""))?;
                if !((0.0..=1.0).contains(&u)) {
                    bail!("Value `u` must be between 0 and 1, got {u}");
                }
                let mu =
                    mu.ok_or_else(|| anyhow!("Value `mu` is mandatory when `type` is \"Logit\""))?;
                if mu <= 0.0 {
                    bail!("Value `mu` must be positive, got {mu}");
                }
                Ok(Self::Logit(LogitModel::new(
                    T::from_f64(u).unwrap(),
                    T::from_f64(mu).unwrap(),
                )))
            }
            Some(s) => Err(anyhow!("Unknown `type`: {s}")),
            None => Err(anyhow!(
                "Value `type` is mandatory for a continuous choice model"
            )),
        }
    }

    /// Returns the expected payoff of the choice and a [ContinuousChoiceCallback] that gives the
    /// chosen continuous alternative, given a [PwlXYF] that yields the payoff value for any
    /// possible alternative.
    pub fn get_choice<
        'a,
        X: TTFNum + Into<T> + From<T> + 'a,
        Y: TTFNum + Into<T> + From<T> + 'a,
    >(
        &'a self,
        func: PwlXYF<X, Y, T>,
    ) -> Result<(ContinuousChoiceCallback<'a, X>, Y)> {
        match self {
            Self::Logit(model) => model.get_continuous_choice(func),
        }
    }
}
