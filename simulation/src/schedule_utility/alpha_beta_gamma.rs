//! The alpha-beta-gamma schedule-delay cost model.
use crate::units::{Time, Utility, ValueOfTime};

use num_traits::Zero;
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::{TTFNum, TTF};

/// Structure to compute the schedule-delay utility from Vickrey's alpha-beta-gamma model.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Alpha-Beta-Gamma Model")]
#[schemars(
    description = "Compute the schedule-delay utility using Vickrey's alpha-beta-gamma model"
)]
pub struct AlphaBetaGammaModel<T> {
    /// The earliest desired arrival (or departure) time.
    t_star_low: Time<T>,
    /// The latest desired arrival (or departure) time.
    t_star_high: Time<T>,
    /// The penalty for early arrivals (or departures), in utility per second.
    beta: ValueOfTime<T>,
    /// The penalty for late arrivals (or departures), in utility per second.
    gamma: ValueOfTime<T>,
    /// If `true`, `tstar_low` and `t_star_high` represent the desired arrival-time interval,
    /// otherwise they represent the desired departure-time interval.
    #[serde(default = "default_is_true")]
    desired_arrival: bool,
}

impl<T> AlphaBetaGammaModel<T> {
    pub fn new(
        t_star_low: Time<T>,
        t_star_high: Time<T>,
        beta: ValueOfTime<T>,
        gamma: ValueOfTime<T>,
        desired_arrival: bool,
    ) -> AlphaBetaGammaModel<T> {
        AlphaBetaGammaModel {
            t_star_low,
            t_star_high,
            beta,
            gamma,
            desired_arrival,
        }
    }
}

impl<T: TTFNum> AlphaBetaGammaModel<T> {
    /// Return the schedule-delay utility given the departure time (if `desired_arrival` is
    /// `false`) or the arrival time (otherwise).
    ///
    /// The schedule-delay cost is `c = beta * [t_star_low - t]_+ + gamma * [t - t_star_high]_+`
    /// The schedule-delay utility is `-c`.
    fn get_utility_from_time(&self, at_time: Time<T>) -> Utility<T> {
        let cost = if at_time < self.t_star_low {
            self.beta * (self.t_star_low - at_time)
        } else if at_time > self.t_star_high {
            self.gamma * (at_time - self.t_star_high)
        } else {
            Utility::zero()
        };
        -cost
    }

    /// Return the point (departure time, travel time) such that arrival time is equal to `t_star`
    /// (for desired arrival time) or such that departure time is equal to `t_star` (for desired
    /// departure time).
    fn get_kink_at(&self, t_star: Time<T>, ttf: &TTF<Time<T>>) -> Option<(Time<T>, Time<T>)> {
        if self.desired_arrival {
            ttf.departure_time_with_arrival(t_star)
                .map(|dt| (dt, t_star - dt))
        } else {
            Some((t_star, ttf.eval(t_star)))
        }
    }

    /// Return the breakpoints (departure time, travel time) at the kinks of the schedule-utility
    /// function.
    ///
    /// The kinks are the points such that arrival time is equal to desired arrival time or
    /// departure time is equal to desired departure time.
    pub fn get_breakpoints(&self, ttf: &TTF<Time<T>>) -> Vec<(Time<T>, Time<T>)> {
        let mut breakpoints = Vec::with_capacity(2);
        if let Some(kink) = self.get_kink_at(self.t_star_low, ttf) {
            breakpoints.push(kink);
        }
        if self.t_star_low != self.t_star_high {
            if let Some(kink) = self.get_kink_at(self.t_star_high, ttf) {
                breakpoints.push(kink);
            }
        }
        breakpoints
    }

    /// Return the schedule-utility given the departure time and arrival time.
    pub fn get_utility(&self, departure_time: Time<T>, arrival_time: Time<T>) -> Utility<T> {
        if self.desired_arrival {
            self.get_utility_from_time(arrival_time)
        } else {
            self.get_utility_from_time(departure_time)
        }
    }
}

fn default_is_true() -> bool {
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_model(desired_arrival: bool) -> AlphaBetaGammaModel<f64> {
        AlphaBetaGammaModel {
            t_star_low: Time(10.),
            t_star_high: Time(20.),
            beta: ValueOfTime(5.),
            gamma: ValueOfTime(20.),
            desired_arrival,
        }
    }

    #[test]
    fn get_utility_from_time_test() {
        let model = get_model(true);
        assert_eq!(model.get_utility_from_time(Time(5.)), Utility(-25.));
        assert_eq!(model.get_utility_from_time(Time(15.)), Utility(0.));
        assert_eq!(model.get_utility_from_time(Time(25.)), Utility(-100.));
    }

    #[test]
    fn get_utility_test() {
        let model = get_model(true);
        // Early arrival by 5 seconds.
        assert_eq!(model.get_utility(Time(5.), Time(5.)), Utility(-25.));
        // On-time arrival.
        assert_eq!(model.get_utility(Time(5.), Time(10.)), Utility(0.));
        // On-time arrival.
        assert_eq!(model.get_utility(Time(10.), Time(15.)), Utility(0.));
        // On-time arrival.
        assert_eq!(model.get_utility(Time(25.), Time(20.)), Utility(0.));
        // Late arrival by 5 seconds.
        assert_eq!(model.get_utility(Time(15.), Time(25.)), Utility(-100.));
        let model = get_model(false);
        // Early departure by 5 seconds.
        assert_eq!(model.get_utility(Time(5.), Time(10.)), Utility(-25.));
        // On-time departure.
        assert_eq!(model.get_utility(Time(10.), Time(15.)), Utility(0.));
        // On-time departure.
        assert_eq!(model.get_utility(Time(15.), Time(25.)), Utility(0.));
        // On-time departure.
        assert_eq!(model.get_utility(Time(20.), Time(25.)), Utility(0.));
        // Late departure by 5 seconds.
        assert_eq!(model.get_utility(Time(25.), Time(15.)), Utility(-100.));
    }

    #[test]
    fn get_kink_at_test() {
        let ttf = TTF::Constant(Time(10.));
        let model = get_model(true);
        assert_eq!(
            model.get_kink_at(Time(15.), &ttf),
            Some((Time(5.), Time(10.)))
        );
        let model = get_model(false);
        assert_eq!(
            model.get_kink_at(Time(15.), &ttf),
            Some((Time(15.), Time(10.)))
        );
    }

    #[test]
    fn get_breakpoints_test() {
        let ttf = TTF::Constant(Time(10.));
        let model = get_model(true);
        assert_eq!(
            model.get_breakpoints(&ttf),
            vec![(Time(0.), Time(10.)), (Time(10.), Time(10.))]
        );
        let model = get_model(false);
        assert_eq!(
            model.get_breakpoints(&ttf),
            vec![(Time(10.), Time(10.)), (Time(20.), Time(10.))]
        );
    }
}
