// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to schedule utility.
use alpha_beta_gamma::LinearPenaltiesModel;
use anyhow::{anyhow, bail, Context, Result};
use num_traits::ConstZero;

use crate::{
    logging::{send_warning_at_most_once, WarningType},
    units::{NonNegativeSeconds, Utility},
};

pub mod alpha_beta_gamma;

/// Model used to represent the schedule utility of an agent.
///
/// The schedule utility is the utility that an agent gets given his / her departure time from an
/// origin or arrival time at a destination.
#[derive(Clone, Debug)]
pub enum ScheduleUtility {
    /// The schedule utility is always null.
    None,
    /// The schedule utility is computed using the alpha-beta-gamma model.
    ///
    /// There is a penalty beta for leaving / arriving early and a penalty gamma for leaving /
    /// arriving late.
    LinearPenalties(LinearPenaltiesModel),
}

impl Default for ScheduleUtility {
    fn default() -> Self {
        Self::None
    }
}

impl ScheduleUtility {
    pub(crate) fn from_values(
        utility_type: Option<&str>,
        tstar: Option<f64>,
        beta: Option<f64>,
        gamma: Option<f64>,
        delta: Option<f64>,
    ) -> Result<Self> {
        match utility_type {
            Some("Linear") => {
                let model = LinearPenaltiesModel::from_values(tstar, beta, gamma, delta)
                    .with_context(|| {
                        anyhow!("Failed to create schedule utility with `type`=`\"Linear\"`")
                    })?;
                Ok(ScheduleUtility::LinearPenalties(model))
            }
            Some("AlphaBetaGamma") => {
                let model = LinearPenaltiesModel::from_values(tstar, beta, gamma, delta)
                    .with_context(|| {
                        anyhow!(
                            "Failed to create schedule utility with `type`=`\"AlphaBetaGamma\"`"
                        )
                    })?;
                send_warning_at_most_once(
                    WarningType::DeprecatedAlphaBetaGamma,
                    "Schedule utility type \"AlphaBetaGamma\" is deprecated. \
                    Use \"Linear\" instead.",
                );
                Ok(ScheduleUtility::LinearPenalties(model))
            }
            None => Ok(ScheduleUtility::None),
            Some(s) => bail!("Unknown type: {s}"),
        }
    }

    /// Iterates over the breakpoints where the schedule utility is non-linear.
    ///
    /// The breakpoints are ordered by increasing departure time.
    pub fn iter_breakpoints(&self) -> Box<dyn Iterator<Item = NonNegativeSeconds>> {
        match self {
            Self::LinearPenalties(model) => model.iter_breakpoints(),
            _ => Box::new(std::iter::empty()),
        }
    }

    /// Returns the schedule utility given the threshold time (departure time from an origin or
    /// arrival time at a destination).
    pub fn get_utility(&self, time: NonNegativeSeconds) -> Utility {
        match self {
            Self::None => Utility::ZERO,
            Self::LinearPenalties(model) => model.get_utility(time),
        }
    }
}
