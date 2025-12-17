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

//! Discrete and continuous choice models.
#![doc(html_no_source)]

mod deterministic_choice;
mod logit;

use std::ops::Add;

use anyhow::{anyhow, bail, Result};
use ttf::{PwlXYF, TTFNum};

pub use self::deterministic_choice::DeterministicChoiceModel;
pub use self::logit::LogitModel;

/// A choice model between a finite number of alternatives.
#[derive(Clone, Debug)]
pub enum ChoiceModel<V> {
    /// Choose the alternative with the largest utility.
    Deterministic(DeterministicChoiceModel<V>),
    /// Choose the alternative using Logit probabilities.
    Logit(LogitModel),
}

impl<V> ChoiceModel<V>
where
    V: TryFrom<f64>,
    <V as TryFrom<f64>>::Error: Into<anyhow::Error>,
{
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
                if mu <= 0.0 || !mu.is_finite() {
                    bail!("Value `mu` must be positive, got {mu}");
                }
                Ok(ChoiceModel::Logit(LogitModel::new(u, mu)))
            }
            Some("Deterministic") => {
                let u = u.unwrap_or(0.0);
                if !((0.0..=1.0).contains(&u)) {
                    bail!("Value `u` must be between 0 and 1, got {u}");
                }
                if let Some(csts) = constants {
                    let constants = csts
                        .into_iter()
                        .map(|v| V::try_from(v).map_err(|e| e.into()))
                        .collect::<Result<Vec<V>>>()?;
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
}

impl<V> ChoiceModel<V>
where
    V: Copy + PartialOrd + TryFrom<f64> + Into<f64> + Add<V, Output = V> + std::fmt::Debug,
    <V as TryFrom<f64>>::Error: Into<anyhow::Error>,
{
    /// Returns the index of the chosen alternative and the expected utility of the choice, given
    /// the vector of values of the alternatives.
    pub fn get_choice(&self, values: &[V]) -> Result<(usize, V)> {
        match self {
            Self::Deterministic(model) => model.get_choice(values),
            Self::Logit(model) => model.get_choice(values),
        }
    }
}

/// A boxed callback function that returns the chosen (continuous) value.
pub type ContinuousChoiceCallback<'a, T> = Box<dyn FnOnce() -> T + 'a>;

/// A choice model between a continuous number of ordered alternatives.
#[derive(Clone, Debug)]
pub enum ContinuousChoiceModel {
    /// Choose the alternative using Continuous Logit probabilities.
    Logit(LogitModel),
}

impl ContinuousChoiceModel {
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
                Ok(Self::Logit(LogitModel::new(u, mu)))
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
    pub fn get_choice<'a, X, Y, T>(
        &'a self,
        func: PwlXYF<X, Y, T>,
    ) -> Result<(ContinuousChoiceCallback<'a, X>, Y)>
    where
        X: TTFNum + Into<T> + From<T> + Into<f64> + TryFrom<f64> + 'a,
        Y: TTFNum + Into<T> + From<T> + Into<f64> + TryFrom<f64> + 'a,
        T: TTFNum + 'a,
        <X as TryFrom<f64>>::Error: Into<anyhow::Error>,
        <Y as TryFrom<f64>>::Error: Into<anyhow::Error>,
    {
        match self {
            Self::Logit(model) => model.get_continuous_choice(func),
        }
    }
}
