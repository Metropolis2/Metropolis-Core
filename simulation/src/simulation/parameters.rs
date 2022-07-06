use super::{AgentResults, AggregateResults, IterationResults};
use crate::learning::LearningModel;
use crate::network::{NetworkParameters, NetworkWeights};
use crate::stop::StopCriterion;
use crate::units::Interval;

use anyhow::{anyhow, Result};
use serde_derive::{Deserialize, Serialize};
use std::fs::File;
use std::path::{Path, PathBuf};
use ttf::TTFNum;

fn default_update_ratio() -> f64 {
    1.0
}

// period_end is the latest possible departure from any edge
// The latest possible departure for an agent is such that he can take the last edge of his route
// at `period_end`.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct Parameters<T> {
    pub period: Interval<T>,
    pub network: NetworkParameters<T>,
    pub learning_model: LearningModel<T>,
    pub stopping_criteria: Vec<StopCriterion<T>>,
    #[serde(default = "default_update_ratio")]
    pub update_ratio: f64,
    pub random_seed: u64,
}

impl<T> Parameters<T> {
    pub fn new(
        period: Interval<T>,
        network: NetworkParameters<T>,
        learning_model: LearningModel<T>,
        stopping_criteria: Vec<StopCriterion<T>>,
        update_ratio: f64,
        random_seed: u64,
    ) -> Result<Self> {
        if !(0.0..=1.0).contains(&update_ratio) && update_ratio != 0.0 {
            return Err(anyhow!(
                "The value of the update ratio must be such that 0.0 < u <= 1.0, got {}",
                update_ratio
            ));
        }
        Ok(Parameters {
            period,
            network,
            learning_model,
            stopping_criteria,
            update_ratio,
            random_seed,
        })
    }
}

impl<T: TTFNum> Parameters<T> {
    pub fn stop(
        &self,
        iteration_counter: u64,
        results: &AgentResults<T>,
        prev_results: Option<&AgentResults<T>>,
    ) -> bool {
        self.stopping_criteria
            .iter()
            .any(|c| c.stop(iteration_counter, results, prev_results))
    }

    pub fn learn(
        &self,
        old_weights: &NetworkWeights<T>,
        weights: &NetworkWeights<T>,
        iteration_counter: u64,
    ) -> NetworkWeights<T> {
        // At this point, the iteration counter has not been increment yet.
        self.learning_model
            .learn(old_weights, weights, iteration_counter + 1)
    }
}

impl<T: serde::Serialize> Parameters<T> {
    pub fn save_aggregate_results(
        &self,
        aggregate_results: &AggregateResults<T>,
        iteration_counter: u64,
        output_dir: &Path,
    ) -> Result<()> {
        let filename: PathBuf = [
            output_dir.to_str().unwrap(),
            &format!("iteration{iteration_counter}.json"),
        ]
        .iter()
        .collect();
        Ok(serde_json::to_writer(
            &File::create(&filename)?,
            &aggregate_results,
        )?)
    }

    pub fn save_iteration_results(
        &self,
        iteration_results: IterationResults<T>,
        output_dir: &Path,
    ) -> Result<()> {
        let filename: PathBuf = [output_dir.to_str().unwrap(), "results.json"]
            .iter()
            .collect();
        Ok(serde_json::to_writer(
            &File::create(&filename)?,
            &iteration_results,
        )?)
    }
}
