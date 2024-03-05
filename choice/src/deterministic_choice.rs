// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::cmp::Ordering;

use anyhow::{anyhow, Result};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::TTFNum;

/// A deterministic choice model between a finite number of alternatives.
///
/// The chosen alternative is the one with the largest value.
/// In case of tie, an alternative is chosen randomly (with uniform probabilities) among the
/// alternatives with the largest value.
///
/// # Example
///
/// ```
/// use choice::DeterministicChoiceModel;
/// let model = DeterministicChoiceModel::new(0.0f64);
/// assert_eq!(model.get_choice(&[0., 1.]).unwrap(), (1, 1.));
/// assert_eq!(model.get_choice(&[0., 0., -1.]).unwrap(), (0, 0.));
/// ```
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Deterministic choice model")]
#[schemars(description = "Choose the alternative with the largest value.")]
pub struct DeterministicChoiceModel<T> {
    /// Uniform random number between 0.0 and 1.0 to choose the alternative in case of tie.
    #[validate(range(min = 0.0, max = 1.0))]
    u: T,
    /// Constants added to the value of each alternative.
    ///
    /// The number of constants does not have to match the number of alternatives. If there are
    /// less constants than alternatives, then the constants are cycled over.
    ///
    /// If `None`, no constant is added to the alternatives' value.
    #[serde(default = "default_is_none::<T>")]
    constants: Option<Vec<T>>,
}

fn default_is_none<T>() -> Option<Vec<T>> {
    None
}

impl<T: TTFNum> DeterministicChoiceModel<T> {
    /// Initializes a new deterministic choice model.
    ///
    /// The value of `u` must be such that `0.0 <= u < 1.0`.
    pub fn new(u: T) -> Self {
        DeterministicChoiceModel { u, constants: None }
    }

    /// Initializes a new deterministic choice model with constants.
    ///
    /// The value of `u` must be such that `0.0 <= u < 1.0`.
    pub fn new_with_constants(u: T, constants: Vec<T>) -> Self {
        DeterministicChoiceModel {
            u,
            constants: Some(constants),
        }
    }

    fn iter_values<'a, V: Copy + Into<T>>(
        &'a self,
        values: &'a [V],
    ) -> Box<dyn Iterator<Item = T> + 'a> {
        if let Some(csts) = &self.constants {
            Box::new(
                values
                    .iter()
                    .zip(csts.iter().cycle())
                    .map(|(&v, &c)| v.into() + c),
            )
        } else {
            Box::new(values.iter().map(|&v| v.into()))
        }
    }

    /// Returns the id of the chosen alternative and its payoff, given a vector of payoffs.
    ///
    /// Returns an error if
    ///
    /// - The vector of payoffs is empty.
    ///
    /// - The payoffs cannot be compared.
    pub fn get_choice<V: Copy + Into<T> + From<T>>(&self, values: &[V]) -> Result<(usize, V)> {
        if values.is_empty() {
            return Err(anyhow!(
                "Cannot compute choice from an empty slice of values"
            ));
        }
        // Find the maximum value and the indices where the value is maximal.
        let mut max_indices = Vec::new();
        let mut max_value = T::neg_infinity();
        for (i, value) in self.iter_values(values).enumerate() {
            match value.partial_cmp(&max_value) {
                Some(Ordering::Greater) => {
                    max_value = value;
                    max_indices = vec![i];
                }
                Some(Ordering::Equal) => {
                    max_indices.push(i);
                }
                None => {
                    return Err(anyhow!("Cannot compare {:?} and {:?}", value, max_value));
                }
                _ => {}
            }
        }
        // If there are n alternatives with the maximum value, we choose the i-th one if:
        // (i / n) <= u < ((i+1) / n)   =>   i <= u * n < i+1
        // so i is equal to the integer part of u * n.
        if let Some(nb_indices) = T::from_usize(max_indices.len()) {
            if let Some(i) = (self.u * nb_indices).to_usize() {
                let choice_id = max_indices[i];
                Ok((choice_id, <V as From<T>>::from(max_value)))
            } else {
                Err(anyhow!(
                    "Cannot convert {:?} to `usize`",
                    self.u * nb_indices
                ))
            }
        } else {
            Err(anyhow!("Cannot convert {:?} to Float", max_indices.len()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_choice_test() {
        let model = DeterministicChoiceModel::new(0.6);
        // Only one choice.
        assert_eq!(
            model.get_choice(&[f64::NEG_INFINITY]).unwrap(),
            (0, f64::NEG_INFINITY)
        );
        // Two choices.
        assert_eq!(model.get_choice(&[1., 0.]).unwrap(), (0, 1.));
        // Three choices, two that maximize, negative values.
        assert_eq!(model.get_choice(&[-1., -1., -2.]).unwrap(), (1, -1.));
        // No choice.
        assert!(model.get_choice::<f64>(&[]).is_err());
        // Invalid comparison
        assert!(model.get_choice(&[1., f64::NAN, 2.]).is_err());
    }
}
