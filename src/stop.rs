// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to stopping criteria.
use num_traits::{Float, FromPrimitive, Zero};
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
    /// The first value represents the threshold value.
    /// The second value represents the backup value to use when an agent switch from a mode to
    /// another mode.
    DepartureTime(Time<T>, Time<T>),
}

impl<T: TTFNum> StopCriterion<T> {
    /// Returns `true` if the simulation must be stopped according to the current `StopCriterion`.
    pub fn stop(
        &self,
        iteration_counter: u32,
        results: &AgentResults<T>,
        prev_results: Option<&AgentResults<T>>,
    ) -> bool {
        match *self {
            Self::MaxIteration(max_iter) => max_iter <= iteration_counter,
            Self::DepartureTime(threshold, default) => prev_results.map_or(false, |prev_results| {
                get_mean_departure_time_shift(results, prev_results, default) <= threshold
            }),
        }
    }
}

/// Return the mean departure time shift between two iterations.
///
/// The `default` value is used when an agent switched to another mode.
fn get_mean_departure_time_shift<T: TTFNum>(
    results: &AgentResults<T>,
    prev_results: &AgentResults<T>,
    default: Time<T>,
) -> Time<T> {
    results
        .iter()
        .zip(prev_results.iter())
        .map(|(res, prev_res)| {
            if res.pre_day_results().get_mode_index() == prev_res.pre_day_results().get_mode_index()
            {
                if let (Some(dt), Some(prev_dt)) = (res.departure_time(), prev_res.departure_time())
                {
                    (dt - prev_dt).abs()
                } else {
                    Time::zero()
                }
            } else {
                // The agent has switched to another mode.
                default
            }
        })
        .fold(Time::zero(), |acc, x| acc + x)
        / Time::from_usize(results.len()).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::agent_index;
    use crate::mode::{mode_index, ModeResults, PreDayChoices};
    use crate::simulation::results::{AgentResult, PreDayResult};
    use crate::units::Utility;

    #[test]
    fn max_iteration_test() {
        let c: StopCriterion<f64> = StopCriterion::MaxIteration(10);
        assert!(!c.stop(5, &Default::default(), None));
        assert!(c.stop(10, &Default::default(), None));
        assert!(c.stop(15, &Default::default(), None));
    }

    #[test]
    fn departure_time_shift_test() {
        let c = StopCriterion::DepartureTime(Time(2.0f64), Time(100.0));
        assert!(!c.stop(0, &Default::default(), None));

        // === Departure times ===
        // Iteration 1: [0., 0.].
        // Iteration 2: [0., 2.].
        let pdr = PreDayResult::new(mode_index(1), Utility(0.), PreDayChoices::None);

        let mut prev_agent_results = AgentResults::with_capacity(2);
        let mut r = AgentResult::new(1, pdr.clone(), ModeResults::None);
        r.set_departure_time(Time(0.));
        prev_agent_results.push(r);
        let mut r = AgentResult::new(2, pdr.clone(), ModeResults::None);
        r.set_departure_time(Time(0.));
        prev_agent_results.push(r);

        let mut agent_results = AgentResults::with_capacity(2);
        let mut r = AgentResult::new(1, pdr.clone(), ModeResults::None);
        r.set_departure_time(Time(0.));
        agent_results.push(r);
        let mut r = AgentResult::new(2, pdr, ModeResults::None);
        r.set_departure_time(Time(2.));
        agent_results.push(r);

        assert_eq!(
            get_mean_departure_time_shift(&prev_agent_results, &agent_results, Time(100.)),
            Time(1.)
        );
        assert_eq!(
            get_mean_departure_time_shift(&agent_results, &prev_agent_results, Time(100.)),
            Time(1.)
        );
        assert!(c.stop(0, &agent_results, Some(&prev_agent_results)));

        // Now the second agent switched to another mode.
        let pdr = PreDayResult::new(mode_index(2), Utility(0.), PreDayChoices::None);
        let mut r = AgentResult::new(2, pdr, ModeResults::None);
        r.set_departure_time(Time(0.));
        agent_results[agent_index(1)] = r;

        assert_eq!(
            get_mean_departure_time_shift(&prev_agent_results, &agent_results, Time(100.)),
            Time(50.)
        );
        assert_eq!(
            get_mean_departure_time_shift(&agent_results, &prev_agent_results, Time(100.)),
            Time(50.)
        );
        assert!(!c.stop(0, &agent_results, Some(&prev_agent_results)));
    }
}
