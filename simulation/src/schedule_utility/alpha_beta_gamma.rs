use crate::units::{Time, Utility, ValueOfTime};

use num_traits::Zero;
use serde_derive::{Deserialize, Serialize};
use ttf::{TTFNum, TTF};

/// Structure to compute the schedule-delay utility from Vickrey's alpha-beta-gamma model.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct AlphaBetaGammaModel<T> {
    /// The earliest desired arrival (or departure) time.
    t_star_low: Time<T>,
    /// The latest desired arrival (or departure) time.
    t_star_high: Time<T>,
    /// The penalty for early arrivals (or departures), in utility per second.
    beta: ValueOfTime<T>,
    /// The penalty for late arrivals (or departures), in utility per second.
    gamma: ValueOfTime<T>,
    /// If `true` tstar represents the desired arrival time, otherwise it represents the desired
    /// departure time.
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
    fn get_schedule_delay_utility(&self, at_time: Time<T>) -> Utility<T> {
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

    pub fn get_utility(&self, departure_time: Time<T>, arrival_time: Time<T>) -> Utility<T> {
        if self.desired_arrival {
            self.get_schedule_delay_utility(arrival_time)
        } else {
            self.get_schedule_delay_utility(departure_time)
        }
    }
}
