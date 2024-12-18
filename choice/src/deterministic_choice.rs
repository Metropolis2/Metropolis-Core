// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::cmp::Ordering;
use std::ops::Add;

use anyhow::{bail, Result};
use either::Either;

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
#[derive(Clone, Debug)]
pub struct DeterministicChoiceModel<V> {
    /// Uniform random number between 0.0 and 1.0 to choose the alternative in case of tie.
    u: f64,
    /// Constants added to the value of each alternative.
    ///
    /// The number of constants does not have to match the number of alternatives. If there are
    /// less constants than alternatives, then the constants are cycled over.
    ///
    /// If `None`, no constant is added to the alternatives' value.
    constants: Option<Vec<V>>,
}

impl<V> DeterministicChoiceModel<V> {
    /// Initializes a new deterministic choice model.
    ///
    /// The value of `u` must be such that `0.0 <= u < 1.0`.
    pub fn new(u: f64) -> Self {
        DeterministicChoiceModel { u, constants: None }
    }

    /// Initializes a new deterministic choice model with constants.
    ///
    /// The value of `u` must be such that `0.0 <= u < 1.0`.
    pub fn new_with_constants(u: f64, constants: Vec<V>) -> Self {
        DeterministicChoiceModel {
            u,
            constants: Some(constants),
        }
    }
}

impl<V: Copy + Add<V, Output = V>> DeterministicChoiceModel<V> {
    fn iter_values<'a>(&'a self, values: &'a [V]) -> Box<dyn Iterator<Item = V> + 'a> {
        if let Some(csts) = &self.constants {
            Box::new(values.iter().zip(csts.iter().cycle()).map(|(&v, &c)| v + c))
        } else {
            Box::new(values.iter().copied())
        }
    }
}

impl<V: Copy + PartialOrd + Add<V, Output = V> + std::fmt::Debug> DeterministicChoiceModel<V> {
    /// Returns the id of the chosen alternative and its payoff, given a vector of payoffs.
    ///
    /// Returns an error if
    ///
    /// - The vector of payoffs is empty.
    /// - The payoffs cannot be compared.
    pub fn get_choice(&self, values: &[V]) -> Result<(usize, V)> {
        if values.is_empty() {
            bail!("Cannot compute choice from an empty slice of values");
        }
        // Find the maximum value and the indices where the value is maximal.
        let mut max_indices: Either<usize, Vec<usize>> = Either::Left(0);
        // `max_value` is initialized without the potential constant value but this is not a
        // problem.
        let mut max_value: V = values[0];
        for (i, value) in self.iter_values(values).enumerate() {
            if i == 0 {
                // First iteration of the loop.
                max_indices = Either::Left(0);
                max_value = value;
                continue;
            }
            match value.partial_cmp(&max_value) {
                Some(Ordering::Greater) => {
                    max_value = value;
                    max_indices = Either::Left(i);
                }
                Some(Ordering::Equal) => match max_indices {
                    Either::Left(old_i) => max_indices = Either::Right(vec![old_i, i]),
                    Either::Right(ref mut indices) => indices.push(i),
                },
                Some(Ordering::Less) => {}
                None => {
                    bail!("Cannot compare {:?} and {:?}", value, max_value);
                }
            }
        }
        // If there are n alternatives with the maximum value, we choose the i-th one if:
        // (i / n) <= u < ((i+1) / n)   =>   i <= u * n < i+1
        // so i is equal to the integer part of u * n.
        let choice_id = match max_indices {
            Either::Left(choice_id) => choice_id,
            Either::Right(indices) => {
                let i = (self.u * indices.len() as f64) as usize;
                indices[i]
            }
        };
        Ok((choice_id, max_value))
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
        assert!(model.get_choice(&[]).is_err());
        // Invalid comparison
        assert!(model.get_choice(&[1., f64::NAN, 2.]).is_err());
    }
}
