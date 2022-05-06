use crate::simulation::AgentResults;
use crate::units::Time;

use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum ConvergenceCriterion<T> {
    MaxIteration(u64),
    DepartureTime(T, Time<T>),
}

impl<T: TTFNum> ConvergenceCriterion<T> {
    pub fn has_converged(
        &self,
        iteration_counter: u64,
        results: &AgentResults<T>,
        prev_results: Option<&AgentResults<T>>,
    ) -> bool {
        match self {
            Self::MaxIteration(max_iter) => *max_iter <= iteration_counter,
            Self::DepartureTime(threshold, default) => {
                if let Some(prev_results) = prev_results {
                    let mean_dep_time_shift = results
                        .departure_times()
                        .zip(prev_results.departure_times())
                        .map(|(dt_opt, prev_dt_opt)| {
                            if let (Some(dt), Some(prev_dt)) = (dt_opt, prev_dt_opt) {
                                (dt.0 - prev_dt.0).abs()
                            } else if dt_opt.is_none() && prev_dt_opt.is_none() {
                                T::zero()
                            } else {
                                default.0
                            }
                        })
                        .fold(T::zero(), |acc, x| acc + x)
                        / T::from_usize(results.len()).unwrap();
                    mean_dep_time_shift <= *threshold
                } else {
                    false
                }
            }
        }
    }
}
