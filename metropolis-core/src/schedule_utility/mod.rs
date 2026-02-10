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
#[derive(Clone, Debug, Default)]
pub enum ScheduleUtility {
    /// The schedule utility is always null.
    #[default]
    None,
    /// The schedule utility is computed using the alpha-beta-gamma model.
    ///
    /// There is a penalty beta for leaving / arriving early and a penalty gamma for leaving /
    /// arriving late.
    LinearPenalties(LinearPenaltiesModel),
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
