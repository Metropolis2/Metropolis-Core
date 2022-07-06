mod deterministic_choice;
mod logit;

pub use self::deterministic_choice::DeterministicChoiceModel;
pub use self::logit::LogitModel;

use anyhow::Result;
use ttf::{PwlXYF, TTFNum};

#[cfg(feature = "serde-1")]
#[macro_use]
extern crate serde_derive;

/// A choice model between a finite number of alternatives.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum ChoiceModel<T> {
    /// Choose the alternative with the largest utility.
    Deterministic(DeterministicChoiceModel<T>),
    /// Choose the alternative using Logit probabilities.
    Logit(LogitModel<T>),
    /// Always choose the first alternative.
    First,
}

impl<T: TTFNum> ChoiceModel<T> {
    /// Return the index of the chosen alternative and the expected utility of the choice, given
    /// the vector of values of the alternatives.
    pub fn get_choice<V: TTFNum + Into<T> + From<T>>(&self, values: &[V]) -> Result<(usize, V)> {
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
pub enum ContinuousChoiceModel<T, V> {
    /// Always choose the same alternative.
    Constant(V),
    /// Choose the alternative using Continuous Logit probabilities.
    Logit(LogitModel<T>),
}

impl<T: TTFNum, X: TTFNum + Into<T> + From<T>> ContinuousChoiceModel<T, X> {
    /// Return the expected payoff of the choice and a [ContinuousChoiceCallback] that gives the
    /// chosen continuous alternative, given a [PWLFunction] that yields the payoff value
    /// for any possible alternative.
    pub fn get_choice<'a, Y: TTFNum + Into<T> + From<T> + 'a>(
        &'a self,
        func: PwlXYF<X, Y, T>,
    ) -> Result<(ContinuousChoiceCallback<X>, Y)> {
        match self {
            Self::Logit(model) => model.get_continuous_choice(func),
            &Self::Constant(x) => Ok((Box::new(move || x), func.eval(x))),
        }
    }
}
