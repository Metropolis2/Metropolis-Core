// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to stopping criteria.
use log::debug;
use num_traits::{Float, Zero};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::simulation::results::AgentResults;
use crate::units::Time;

/// Criterion that is used to check if a simulation must be stopped.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum StopCriterion<T> {
    /// Stop when the number of iterations has reached a given value.
    #[validate(range(min = 1))]
    MaxIteration(u32),
    /// Stop when the mean departure-time shift from one iteration to another is below a threshold
    /// value.
    ///
    /// The mean departure-time shift is computed over agents who did not shift to another mode
    /// from the previous to the current iteration and whose chosen mode has a departure time.
    DepartureTime(Time<T>),
}

impl<T: TTFNum> StopCriterion<T> {
    /// Returns `true` if the simulation must be stopped according to the current `StopCriterion`.
    pub fn stop(&self, iteration_counter: u32, results: &AgentResults<T>) -> bool {
        match *self {
            Self::MaxIteration(max_iter) => {
                if max_iter <= iteration_counter {
                    debug!("Maximum number of iteration reached");
                    true
                } else {
                    false
                }
            }
            Self::DepartureTime(threshold) => {
                if get_mean_departure_time_shift(results) <= threshold {
                    debug!("Departure time shift threshold reached");
                    true
                } else {
                    false
                }
            }
        }
    }
}

/// Return the mean departure time shift between two iterations.
///
/// The `default` value is used when an agent switched to another mode.
fn get_mean_departure_time_shift<T: TTFNum>(results: &AgentResults<T>) -> Time<T> {
    let (total, count) = results
        .iter()
        .filter_map(|res| {
            res.mode_results
                .as_trip()
                .and_then(|r| r.departure_time_shift.map(|dts| dts.abs()))
        })
        .fold((T::zero(), 0), |acc, x| (acc.0 + x.0, acc.1 + 1));
    if count == 0 {
        Time::zero()
    } else {
        Time(total / T::from_usize(count).unwrap())
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Float;

    use super::*;
    use crate::agent::agent_index;
    use crate::mode::trip::results::TripResults;
    use crate::mode::{mode_index, ModeResults};
    use crate::simulation::results::AgentResult;
    use crate::units::Utility;

    #[test]
    fn max_iteration_test() {
        let c: StopCriterion<f64> = StopCriterion::MaxIteration(10);
        assert!(!c.stop(5, &Default::default()));
        assert!(c.stop(10, &Default::default()));
        assert!(c.stop(15, &Default::default()));
    }

    #[test]
    fn departure_time_shift_test() {
        let c = StopCriterion::DepartureTime(Time(2.0f64));

        // === Departure times ===
        // Iteration 1: [0., 0.].
        // Iteration 2: [0., 2.].
        let mut agent_results = AgentResults::with_capacity(2);
        let mut trip_results = TripResults::new(vec![], Time(0.), Utility::nan(), false);
        trip_results.departure_time_shift = Some(Time(0.));
        let mode_results = ModeResults::Trip(trip_results);
        let r = AgentResult::new(1, 1, mode_index(0), Utility::nan(), mode_results);
        agent_results.push(r);
        let mut trip_results = TripResults::new(vec![], Time(2.), Utility::nan(), false);
        trip_results.departure_time_shift = Some(Time(-2.));
        let mode_results = ModeResults::Trip(trip_results);
        let r = AgentResult::new(2, 1, mode_index(0), Utility::nan(), mode_results);
        agent_results.push(r);

        assert_eq!(get_mean_departure_time_shift(&agent_results), Time(1.));
        assert!(c.stop(0, &agent_results));

        // Now the second agent switched to another mode (index 1).
        agent_results[agent_index(1)].shifted_mode = true;
        agent_results[agent_index(1)]
            .mode_results
            .as_trip_mut()
            .unwrap()
            .departure_time_shift = None;

        assert_eq!(get_mean_departure_time_shift(&agent_results), Time(0.));
        assert!(c.stop(0, &agent_results));
    }
}
