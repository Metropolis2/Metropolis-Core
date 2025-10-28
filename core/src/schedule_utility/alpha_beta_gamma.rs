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

//! The alpha-beta-gamma schedule-delay cost model.
use anyhow::{anyhow, bail, Context, Result};
use num_traits::ConstZero;

use crate::units::*;

/// Structure to compute the schedule-delay utility from Vickrey's alpha-beta-gamma model.
///
/// The schedule utility is:
///
/// - Zero if the threshold time `t` is between the lower and higher t*.
/// - Equal to `-beta * (t_star_low - t)` if `t` is smaller than the lower t*.
/// - Equal to `-gamma * (t - t_star_high)` if `t` is larger than the higher t*.
#[derive(Clone, Debug)]
pub struct LinearPenaltiesModel {
    /// The earliest desired arrival (or departure) time.
    pub(crate) t_star_low: NonNegativeSeconds,
    /// The latest desired arrival (or departure) time (must not be smaller than `t_star_low`).
    pub(crate) t_star_high: NonNegativeSeconds,
    /// The penalty for early arrivals (or departures), in utility per second.
    pub(crate) beta: ValueOfTime,
    /// The penalty for late arrivals (or departures), in utility per second.
    pub(crate) gamma: ValueOfTime,
}

impl LinearPenaltiesModel {
    /// Creates a new LinearPenaltiesModel.
    pub fn new(
        t_star_low: NonNegativeSeconds,
        t_star_high: NonNegativeSeconds,
        beta: ValueOfTime,
        gamma: ValueOfTime,
    ) -> Result<LinearPenaltiesModel> {
        let model = UncheckedLinearPenaltiesModel {
            t_star_low,
            t_star_high,
            beta,
            gamma,
        };
        LinearPenaltiesModel::try_from(model)
    }

    pub(crate) fn from_values(
        tstar: Option<f64>,
        beta: Option<f64>,
        gamma: Option<f64>,
        delta: Option<f64>,
    ) -> Result<Self> {
        let half_delta = NonNegativeSeconds::try_from(delta.unwrap_or(0.0) / 2.0)
            .context("Value `delta` does not satisfy the constraints")?;
        let tstar =
            NonNegativeSeconds::try_from(tstar.ok_or_else(|| {
                anyhow!("Value `tstar` is mandatory for the alpha-beta-gamma model")
            })?)
            .context("Value `t_star` does not satisfy the constraints")?;
        if (tstar - half_delta).is_negative() {
            bail!("Value `tstar` must be larger than value `delta / 2`");
        }
        Ok(Self {
            t_star_low: (tstar - half_delta).assume_non_negative_unchecked(),
            t_star_high: tstar + half_delta,
            beta: ValueOfTime::try_from(beta.unwrap_or(0.0))
                .context("Value `beta` does not satisfy the constraints")?,
            gamma: ValueOfTime::try_from(gamma.unwrap_or(0.0))
                .context("Value `gamma` does not satisfy the constraints")?,
        })
    }

    /// Returns the schedule-delay utility given the threshold time.
    ///
    /// The schedule-delay cost is `c = beta * [t_star_low - t]_+ + gamma * [t - t_star_high]_+`
    /// The schedule-delay utility is `-c`.
    pub fn get_utility(&self, at_time: NonNegativeSeconds) -> Utility {
        let cost = if at_time < self.t_star_low {
            self.beta * (self.t_star_low - at_time).assume_positive_unchecked()
        } else if at_time > self.t_star_high {
            self.gamma * (at_time - self.t_star_high).assume_positive_unchecked()
        } else {
            Utility::ZERO
        };
        -cost
    }

    /// Iterates over the breakpoints (departure time, travel time) at the kinks of the
    /// schedule-utility function.
    ///
    /// The kinks are the points such that arrival time is equal to desired arrival time or
    /// departure time is equal to desired departure time.
    pub fn iter_breakpoints(&self) -> Box<dyn Iterator<Item = NonNegativeSeconds>> {
        if self.t_star_low == self.t_star_high {
            Box::new([self.t_star_low].into_iter())
        } else {
            Box::new([self.t_star_low, self.t_star_high].into_iter())
        }
    }
}

/// [LinearPenaltiesModel] before validation, for deserialization.
#[derive(Clone, Debug)]
pub struct UncheckedLinearPenaltiesModel {
    /// The earliest desired arrival (or departure) time.
    t_star_low: NonNegativeSeconds,
    /// The latest desired arrival (or departure) time (must not be smaller than `t_star_low`).
    t_star_high: NonNegativeSeconds,
    /// The penalty for early arrivals (or departures), in utility per second.
    beta: ValueOfTime,
    /// The penalty for late arrivals (or departures), in utility per second.
    gamma: ValueOfTime,
}

impl TryFrom<UncheckedLinearPenaltiesModel> for LinearPenaltiesModel {
    type Error = anyhow::Error;
    fn try_from(value: UncheckedLinearPenaltiesModel) -> Result<Self> {
        if value.t_star_high < value.t_star_low {
            return Err(anyhow!(
                "Value of t* high cannot be smaller than value of t* low"
            ));
        }
        Ok(LinearPenaltiesModel {
            t_star_low: value.t_star_low,
            t_star_high: value.t_star_high,
            beta: value.beta,
            gamma: value.gamma,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_model() -> LinearPenaltiesModel {
        LinearPenaltiesModel {
            t_star_low: NonNegativeSeconds::new_unchecked(10.),
            t_star_high: NonNegativeSeconds::new_unchecked(20.),
            beta: ValueOfTime::new_unchecked(5.),
            gamma: ValueOfTime::new_unchecked(20.),
        }
    }

    #[test]
    fn new_model_test() {
        let model = LinearPenaltiesModel::new(
            NonNegativeSeconds::new_unchecked(10.),
            NonNegativeSeconds::new_unchecked(20.),
            ValueOfTime::new_unchecked(5.),
            ValueOfTime::new_unchecked(5.),
        );
        assert!(model.is_ok());
        let model = LinearPenaltiesModel::new(
            NonNegativeSeconds::new_unchecked(20.),
            NonNegativeSeconds::new_unchecked(10.),
            ValueOfTime::new_unchecked(5.),
            ValueOfTime::new_unchecked(5.),
        );
        assert!(model.is_err());
    }

    #[test]
    fn get_utility_test() {
        let model = get_model();
        assert_eq!(
            model.get_utility(NonNegativeSeconds::new_unchecked(5.)),
            Utility::new_unchecked(-25.)
        );
        assert_eq!(
            model.get_utility(NonNegativeSeconds::new_unchecked(15.)),
            Utility::new_unchecked(0.)
        );
        assert_eq!(
            model.get_utility(NonNegativeSeconds::new_unchecked(25.)),
            Utility::new_unchecked(-100.)
        );
    }

    #[test]
    fn iter_breakpoints_test() {
        let model = LinearPenaltiesModel {
            t_star_low: NonNegativeSeconds::new_unchecked(10.),
            t_star_high: NonNegativeSeconds::new_unchecked(20.),
            beta: ValueOfTime::new_unchecked(5.),
            gamma: ValueOfTime::new_unchecked(20.),
        };
        let mut iter = model.iter_breakpoints();
        assert_eq!(iter.next(), Some(NonNegativeSeconds::new_unchecked(10.)));
        assert_eq!(iter.next(), Some(NonNegativeSeconds::new_unchecked(20.)));
        assert_eq!(iter.next(), None);

        let model = LinearPenaltiesModel {
            t_star_low: NonNegativeSeconds::new_unchecked(10.),
            t_star_high: NonNegativeSeconds::new_unchecked(10.),
            beta: ValueOfTime::new_unchecked(5.),
            gamma: ValueOfTime::new_unchecked(20.),
        };
        let mut iter = model.iter_breakpoints();
        assert_eq!(iter.next(), Some(NonNegativeSeconds::new_unchecked(10.)));
        assert_eq!(iter.next(), None);
    }
}
