use std::cmp::Ordering;

use anyhow::{anyhow, Result};
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
/// let model = DeterministicChoiceModel::new(0.0f64).unwrap();
/// assert_eq!(model.get_choice(&[0., 1.]).unwrap(), (1, 1.));
/// assert_eq!(model.get_choice(&[0., 0., -1.]).unwrap(), (0, 0.));
/// ```
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct DeterministicChoiceModel<V> {
    /// Uniform random number between 0.0 and 1.0 to choose the alternative in case of tie.
    u: V,
}

impl<V: TTFNum> DeterministicChoiceModel<V> {
    /// Initialize a new deterministic choice model.
    ///
    /// The value of `u` must be such that `0.0 <= u < 1.0`.
    pub fn new(u: V) -> Result<Self> {
        if (V::zero()..V::one()).contains(&u) {
            Ok(DeterministicChoiceModel { u })
        } else {
            Err(anyhow!(
                "The value of u must be such that 0.0 <= u < 1.0, got {:?}",
                u
            ))
        }
    }

    /// Return the id of the chosen alternative and its payoff, given a vector of payoffs.
    ///
    /// Return an error if
    ///
    /// - The vector of payoffs is empty.
    /// - The payoffs cannot be compared.
    pub fn get_choice(&self, values: &[V]) -> Result<(usize, V)> {
        if values.is_empty() {
            return Err(anyhow!(
                "Cannot compute choice from an empty slice of values"
            ));
        }
        // Find the maximum value and the indices where the value is maximal.
        let mut max_indices = Vec::new();
        let mut max_value = values[0];
        for (i, value) in values.iter().enumerate() {
            match value.partial_cmp(&max_value) {
                Some(Ordering::Greater) => {
                    max_value = *value;
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
        if let Some(nb_indices) = V::from(max_indices.len()) {
            if let Some(i) = (self.u * nb_indices).to_usize() {
                let choice_id = max_indices[i];
                Ok((choice_id, max_value))
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
    fn new_deterministic_choice_model_test() {
        // Only create the model if 0.0 <= u < 1.0; else return an error.
        assert!(DeterministicChoiceModel::new(0.4).is_ok());
        assert!(DeterministicChoiceModel::new(-1.).is_err());
        assert!(DeterministicChoiceModel::new(1.).is_err());
        assert!(DeterministicChoiceModel::new(f64::NAN).is_err());
    }

    #[test]
    fn deterministic_choice_test() {
        let model = DeterministicChoiceModel::new(0.6).unwrap();
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
