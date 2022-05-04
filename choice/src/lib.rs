mod deterministic_choice;
mod logit;

pub use self::deterministic_choice::DeterministicChoiceModel;
pub use self::logit::LogitModel;

use anyhow::Result;
use ttf::{PwlTTF, TTFNum};

#[cfg(feature = "serde-1")]
#[macro_use]
extern crate serde_derive;

/// A choice model between a finite number of alternatives.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum ChoiceModel<V> {
    /// Choose the alternative with the largest utility.
    Deterministic(DeterministicChoiceModel<V>),
    /// Choose the alternative using Logit probabilities.
    Logit(LogitModel<V>),
    /// Always choose the first alternative.
    First,
}

impl<V: TTFNum> ChoiceModel<V> {
    /// Return the index of the chosen alternative and the expected utility of the choice, given
    /// the vector of values of the alternatives.
    pub fn get_choice(&self, values: &[V]) -> Result<(usize, V)> {
        match self {
            Self::Deterministic(model) => model.get_choice(values),
            Self::Logit(model) => model.get_choice(values),
            Self::First => Ok((0, values[0])),
        }
    }
}

/// A boxed callback function that returns the chosen (continuous) value.
pub type ContinuousChoiceCallback<'a, T> = Box<dyn FnOnce() -> T + 'a>;

/// A choice model between a continuous number of ordered alternatives.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum ContinuousChoiceModel<T> {
    /// Always choose the same alternative.
    Constant(T),
    /// Choose the alternative using Continuous Logit probabilities.
    Logit(LogitModel<T>),
}

impl<T: TTFNum> ContinuousChoiceModel<T> {
    /// Return the expected payoff of the choice and a [ContinuousChoiceCallback] that gives the
    /// chosen continuous alternative, given a [PWLFunction] that yields the payoff value
    /// for any possible alternative.
    pub fn get_choice(&self, func: PwlTTF<T>) -> Result<(ContinuousChoiceCallback<T>, T)> {
        match self {
            Self::Logit(model) => model.get_continuous_choice(func),
            Self::Constant(x) => Ok((Box::new(move || *x), func.eval(*x))),
        }
    }
}
