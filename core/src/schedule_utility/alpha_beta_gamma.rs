// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! The alpha-beta-gamma schedule-delay cost model.
use anyhow::anyhow;
use num_traits::{FromPrimitive, Zero};
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::units::{Time, Utility, ValueOfTime};

/// Structure to compute the schedule-delay utility from Vickrey's alpha-beta-gamma model.
///
/// The schedule utility is:
///
/// - Zero if the threshold time `t` is between the lower and higher t*.
/// - Equal to `-beta * (t_star_low - t)` if `t` is smaller than the lower t*.
/// - Equal to `-gamma * (t - t_star_high)` if `t` is larger than the higher t*.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(try_from = "UncheckedAlphaBetaGammaModel<T>")]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct AlphaBetaGammaModel<T> {
    /// The earliest desired arrival (or departure) time.
    pub(crate) t_star_low: Time<T>,
    /// The latest desired arrival (or departure) time (must not be smaller than `t_star_low`).
    pub(crate) t_star_high: Time<T>,
    /// The penalty for early arrivals (or departures), in utility per second.
    pub(crate) beta: ValueOfTime<T>,
    /// The penalty for late arrivals (or departures), in utility per second.
    pub(crate) gamma: ValueOfTime<T>,
}

impl<T: TTFNum> AlphaBetaGammaModel<T> {
    /// Creates a new AlphaBetaGammaModel.
    pub fn new(
        t_star_low: Time<T>,
        t_star_high: Time<T>,
        beta: ValueOfTime<T>,
        gamma: ValueOfTime<T>,
    ) -> anyhow::Result<AlphaBetaGammaModel<T>> {
        let model = UncheckedAlphaBetaGammaModel {
            t_star_low,
            t_star_high,
            beta,
            gamma,
        };
        AlphaBetaGammaModel::try_from(model)
    }

    pub(crate) fn from_values(
        tstar: Option<f64>,
        beta: Option<f64>,
        gamma: Option<f64>,
        delta: Option<f64>,
    ) -> anyhow::Result<Self> {
        let delta = delta.unwrap_or(0.0);
        let tstar = tstar
            .ok_or_else(|| anyhow!("Value `tstar` is mandatory for the alpha-beta-gamma model"))?;
        Ok(Self {
            t_star_low: Time::from_f64(tstar - delta / 2.0).unwrap(),
            t_star_high: Time::from_f64(tstar + delta / 2.0).unwrap(),
            beta: ValueOfTime::from_f64(beta.unwrap_or(0.0)).unwrap(),
            gamma: ValueOfTime::from_f64(gamma.unwrap_or(0.0)).unwrap(),
        })
    }

    /// Returns the schedule-delay utility given the threshold time.
    ///
    /// The schedule-delay cost is `c = beta * [t_star_low - t]_+ + gamma * [t - t_star_high]_+`
    /// The schedule-delay utility is `-c`.
    pub fn get_utility(&self, at_time: Time<T>) -> Utility<T> {
        let cost = if at_time < self.t_star_low {
            self.beta * (self.t_star_low - at_time)
        } else if at_time > self.t_star_high {
            self.gamma * (at_time - self.t_star_high)
        } else {
            Utility::zero()
        };
        -cost
    }

    /// Iterates over the breakpoints (departure time, travel time) at the kinks of the
    /// schedule-utility function.
    ///
    /// The kinks are the points such that arrival time is equal to desired arrival time or
    /// departure time is equal to desired departure time.
    pub fn iter_breakpoints(&self) -> Box<dyn Iterator<Item = Time<T>>> {
        if self.t_star_low == self.t_star_high {
            Box::new([self.t_star_low].into_iter())
        } else {
            Box::new([self.t_star_low, self.t_star_high].into_iter())
        }
    }
}

/// [AlphaBetaGammaModel] before validation, for deserialization.
#[derive(Clone, Debug, Deserialize)]
pub struct UncheckedAlphaBetaGammaModel<T> {
    /// The earliest desired arrival (or departure) time.
    t_star_low: Time<T>,
    /// The latest desired arrival (or departure) time (must not be smaller than `t_star_low`).
    t_star_high: Time<T>,
    /// The penalty for early arrivals (or departures), in utility per second.
    beta: ValueOfTime<T>,
    /// The penalty for late arrivals (or departures), in utility per second.
    gamma: ValueOfTime<T>,
}

impl<T: TTFNum> TryFrom<UncheckedAlphaBetaGammaModel<T>> for AlphaBetaGammaModel<T> {
    type Error = anyhow::Error;

    fn try_from(value: UncheckedAlphaBetaGammaModel<T>) -> Result<Self, Self::Error> {
        if value.t_star_high < value.t_star_low {
            return Err(anyhow!(
                "Value of t* high cannot be smaller than value of t* low"
            ));
        }
        Ok(AlphaBetaGammaModel {
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

    fn get_model() -> AlphaBetaGammaModel<f64> {
        AlphaBetaGammaModel {
            t_star_low: Time(10.),
            t_star_high: Time(20.),
            beta: ValueOfTime(5.),
            gamma: ValueOfTime(20.),
        }
    }

    #[test]
    fn new_model_test() {
        let model =
            AlphaBetaGammaModel::new(Time(10.), Time(20.), ValueOfTime(5.), ValueOfTime(5.));
        assert!(model.is_ok());
        let model =
            AlphaBetaGammaModel::new(Time(20.), Time(10.), ValueOfTime(5.), ValueOfTime(5.));
        assert!(model.is_err());
    }

    #[test]
    fn deser_model_test() {
        let js = "{
            \"t_star_low\": 10.0,
            \"t_star_high\": 20.0,
            \"beta\": 5.0,
            \"gamma\": 5.0
        }";
        let model = serde_json::from_str::<AlphaBetaGammaModel<f64>>(js);
        assert!(model.is_ok());
        let js = "{
            \"t_star_low\": 20.0,
            \"t_star_high\": 10.0,
            \"beta\": 5.0,
            \"gamma\": 5.0
        }";
        let model = serde_json::from_str::<AlphaBetaGammaModel<f64>>(js);
        assert!(model.is_err());
    }

    #[test]
    fn get_utility_test() {
        let model = get_model();
        assert_eq!(model.get_utility(Time(5.)), Utility(-25.));
        assert_eq!(model.get_utility(Time(15.)), Utility(0.));
        assert_eq!(model.get_utility(Time(25.)), Utility(-100.));
    }

    #[test]
    fn iter_breakpoints_test() {
        let model = AlphaBetaGammaModel {
            t_star_low: Time(10.),
            t_star_high: Time(20.),
            beta: ValueOfTime(5.),
            gamma: ValueOfTime(20.),
        };
        let mut iter = model.iter_breakpoints();
        assert_eq!(iter.next(), Some(Time(10.)));
        assert_eq!(iter.next(), Some(Time(20.)));
        assert_eq!(iter.next(), None);

        let model = AlphaBetaGammaModel {
            t_star_low: Time(10.),
            t_star_high: Time(10.),
            beta: ValueOfTime(5.),
            gamma: ValueOfTime(20.),
        };
        let mut iter = model.iter_breakpoints();
        assert_eq!(iter.next(), Some(Time(10.)));
        assert_eq!(iter.next(), None);
    }
}
