// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to schedule utility.
use alpha_beta_gamma::AlphaBetaGammaModel;
use num_traits::Zero;
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::{TTFNum, TTF};

use crate::units::{Time, Utility};

pub mod alpha_beta_gamma;

/// Model used to represent the schedule utility of an agent.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
#[schemars(example = "crate::schema::example_schedule_utility")]
pub enum ScheduleUtility<T> {
    /// The schedule utility is always null.
    None,
    /// The schedule utility is computed using the alpha-beta-gamma model.
    AlphaBetaGamma(AlphaBetaGammaModel<T>),
}

impl<T> Default for ScheduleUtility<T> {
    fn default() -> Self {
        Self::None
    }
}

impl<T: TTFNum> ScheduleUtility<T> {
    /// Return a vector of breakpoints (departure time, travel time) that should be added to the
    /// travel-time function before computing the utility to ensure that the linear interpolation
    /// assumption is good enough.
    ///
    /// The breakpoints must be order by increasing departure time.
    pub fn get_breakpoints(&self, ttf: &TTF<Time<T>>) -> Vec<(Time<T>, Time<T>)> {
        match self {
            Self::AlphaBetaGamma(model) => model.get_breakpoints(ttf),
            _ => Vec::new(),
        }
    }

    /// Return the schedule utility given the departure and arrival time of the trip.
    pub fn get_utility(&self, departure_time: Time<T>, arrival_time: Time<T>) -> Utility<T> {
        match self {
            Self::None => Utility::zero(),
            Self::AlphaBetaGamma(model) => model.get_utility(departure_time, arrival_time),
        }
    }
}
