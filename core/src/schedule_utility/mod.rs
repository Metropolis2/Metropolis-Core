// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to schedule utility.
use alpha_beta_gamma::AlphaBetaGammaModel;
use anyhow::{anyhow, bail, Context, Result};
use num_traits::Zero;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::units::{Time, Utility};

pub mod alpha_beta_gamma;

/// Model used to represent the schedule utility of an agent.
///
/// The schedule utility is the utility that an agent gets given his / her departure time from an
/// origin or arrival time at a destination.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "type", content = "value")]
#[serde(bound(deserialize = "T: TTFNum"))]
pub enum ScheduleUtility<T> {
    /// The schedule utility is always null.
    None,
    /// The schedule utility is computed using the alpha-beta-gamma model.
    ///
    /// There is a penalty beta for leaving / arriving early and a penalty gamma for leaving /
    /// arriving late.
    AlphaBetaGamma(AlphaBetaGammaModel<T>),
}

impl<T> Default for ScheduleUtility<T> {
    fn default() -> Self {
        Self::None
    }
}

impl<T: TTFNum> ScheduleUtility<T> {
    pub(crate) fn from_values(
        utility_type: Option<&str>,
        tstar: Option<f64>,
        beta: Option<f64>,
        gamma: Option<f64>,
        delta: Option<f64>,
    ) -> Result<Self> {
        match utility_type {
            Some("AlphaBetaGamma") => {
                let model = AlphaBetaGammaModel::from_values(tstar, beta, gamma, delta)
                    .with_context(|| {
                        anyhow!(
                            "Failed to create schedule utility with `type`=`\"AlphaBetaGamma\"`"
                        )
                    })?;
                Ok(ScheduleUtility::AlphaBetaGamma(model))
            }
            None => Ok(ScheduleUtility::None),
            Some(s) => bail!("Unknown type: {s}"),
        }
    }

    /// Iterates over the breakpoints where the schedule utility is non-linear.
    ///
    /// The breakpoints are ordered by increasing departure time.
    pub fn iter_breakpoints(&self) -> Box<dyn Iterator<Item = Time<T>>> {
        match self {
            Self::AlphaBetaGamma(model) => model.iter_breakpoints(),
            _ => Box::new(std::iter::empty()),
        }
    }

    /// Returns the schedule utility given the threshold time (departure time from an origin or
    /// arrival time at a destination).
    pub fn get_utility(&self, time: Time<T>) -> Utility<T> {
        match self {
            Self::None => Utility::zero(),
            Self::AlphaBetaGamma(model) => model.get_utility(time),
        }
    }
}
