//! Everything related to stopping criteria.
use crate::simulation::AgentResults;
use crate::units::Time;

use num_traits::{Float, FromPrimitive, Zero};
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

/// Criterion that is used to check if a simulation must be stopped.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum StopCriterion<T> {
    /// Stop when the number of iterations has reached a given value.
    MaxIteration(u64),
    /// Stop when the mean departure-time shift from one iteration to another is below a threshold
    /// value.
    ///
    /// The first value represents the threshold value.
    /// The second value represents the value to use when an agent switch from a mode to another
    /// mode.
    DepartureTime(Time<T>, Time<T>),
}

impl<T: TTFNum> StopCriterion<T> {
    /// Return `true` if the simulation must be stopped according to the current `StopCriterion`.
    pub fn stop(
        &self,
        iteration_counter: u64,
        results: &AgentResults<T>,
        prev_results: Option<&AgentResults<T>>,
    ) -> bool {
        match *self {
            Self::MaxIteration(max_iter) => max_iter <= iteration_counter,
            Self::DepartureTime(threshold, default) => {
                if let Some(prev_results) = prev_results {
                    get_mean_departure_time_shift(results, prev_results, default) <= threshold
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
    use crate::simulation::{AgentResult, PreDayResult};
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
