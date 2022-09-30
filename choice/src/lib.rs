// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Discrete and continuous choice models.
#![warn(
    elided_lifetimes_in_paths,
    elided_lifetimes_in_paths,
    macro_use_extern_crate,
    missing_debug_implementations,
    missing_docs,
    non_ascii_idents,
    noop_method_call,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unused_crate_dependencies,
    unused_extern_crates,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications
)]

mod deterministic_choice;
mod logit;
mod schema;

pub use self::deterministic_choice::DeterministicChoiceModel;
pub use self::logit::LogitModel;

use anyhow::Result;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::{PwlXYF, TTFNum};

/// A choice model between a finite number of alternatives.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "values")]
#[schemars(example = "crate::schema::example_choice_model")]
pub enum ChoiceModel<T> {
    /// Choose the alternative with the largest utility.
    Deterministic(DeterministicChoiceModel<T>),
    /// Choose the alternative using Logit probabilities.
    Logit(LogitModel<T>),
}

impl<T: TTFNum> ChoiceModel<T> {
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
#[serde(tag = "type", content = "values")]
pub enum ContinuousChoiceModel<T> {
    /// Choose the alternative using Continuous Logit probabilities.
    Logit(LogitModel<T>),
}

impl<T: TTFNum> ContinuousChoiceModel<T> {
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
