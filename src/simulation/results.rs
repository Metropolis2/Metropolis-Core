// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs holding the results of a simulation.
use std::fs::File;
use std::io::Write;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::path::{Path, PathBuf};

use anyhow::Result;
use hashbrown::HashMap;
use num_traits::{Float, Zero};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use time::Duration;
use ttf::TTFNum;

use crate::agent::{agent_index, Agent, AgentIndex};
use crate::event::{Event, EventQueue};
use crate::mode::trip::event::RoadEvent;
use crate::mode::{AggregateModeResults, ModeIndex, ModeResults};
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::{RoadNetwork, RoadNetworkWeights};
use crate::network::{NetworkSkim, NetworkWeights};
use crate::units::{Distribution, Time, Utility};

/// Struct to store the results of a [Simulation](super::Simulation).
#[derive(Clone, Debug, Default)]
pub struct SimulationResults<T> {
    /// [AggregateResults] of each iteration.
    pub iterations: Vec<AggregateResults<T>>,
    /// [IterationResults] of the last iteration.
    pub last_iteration: Option<IterationResults<T>>,
}

impl<T: TTFNum> SimulationResults<T> {
    /// Create an empty SimulationResults.
    pub fn new() -> Self {
        SimulationResults::default()
    }

    /// Appends the [AggregateResults] of an iteration to the [SimulationResults].
    pub fn push_iteration(&mut self, iteration: AggregateResults<T>) {
        self.iterations.push(iteration);
    }
}

/// Aggregate results summarizing the results of an iteration.
#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct AggregateResults<T> {
    /// Distribution of the surplus of the agents.
    pub surplus: Distribution<Utility<T>>,
    /// Mode-specific aggregate results.
    pub mode_results: AggregateModeResults<T>,
}

/// Detailed results of an iteration.
#[derive(Debug, Clone)]
pub struct IterationResults<T> {
    /// Agent-specific results.
    pub agent_results: AgentResults<T>,
    /// Simulated weights of the network.
    pub weights: NetworkWeights<T>,
    /// Skims of the network.
    pub skims: NetworkSkim<T>,
}

impl<T> IterationResults<T> {
    /// Creates a new IterationResults.
    pub const fn new(
        agent_results: AgentResults<T>,
        weights: NetworkWeights<T>,
        skims: NetworkSkim<T>,
    ) -> Self {
        IterationResults {
            agent_results,
            weights,
            skims,
        }
    }

    /// Returns a reference to the [AgentResults].
    pub const fn agent_results(&self) -> &AgentResults<T> {
        &self.agent_results
    }

    /// Returns a reference to the [NetworkWeights].
    pub const fn network_weights(&self) -> &NetworkWeights<T> {
        &self.weights
    }

    /// Returns the [NetworkWeights], consuming the IterationResults.
    pub fn into_network_weights(self) -> NetworkWeights<T> {
        self.weights
    }

    /// Iterates over the [AgentIndex] and [AgentResult] of the [IterationResults].
    pub fn iter_agent_results(&self) -> impl Iterator<Item = (AgentIndex, &AgentResult<T>)> {
        self.agent_results
            .iter()
            .enumerate()
            .map(|(i, r)| (agent_index(i), r))
    }
}

/// The running times for each model of an iteration.
#[derive(Clone, Debug, Default)]
pub struct IterationRunningTimes {
    /// Total running time of the iteration.
    pub total: Duration,
    /// Running time of skims computation.
    pub skims_computation: Duration,
    /// Running time of pre-day model.
    pub pre_day_model: Duration,
    /// Running time of within-day model.
    pub within_day_model: Duration,
    /// Running time of day-to-day model.
    pub day_to_day_model: Duration,
    /// Running time of aggregate results computation.
    pub aggregate_results_computation: Duration,
    /// Running time to check the stopping rules.
    pub stopping_rules_check: Duration,
}

/// Summary of the running times of a simulation.
#[derive(Clone, Debug, Default, Serialize)]
pub struct RunningTimes {
    /// Total running time of the simulation.
    pub total: Duration,
    /// Total running time of skims computation.
    pub total_skims_computation: Duration,
    /// Total running time of pre-day model.
    pub total_pre_day_model: Duration,
    /// Total running time of within-day model.
    pub total_within_day_model: Duration,
    /// Total running time of day-to-day model.
    pub total_day_to_day_model: Duration,
    /// Total running time of aggregate results computation.
    pub total_aggregate_results_computation: Duration,
    /// Total running time to check the stopping rules.
    pub total_stopping_rules_check: Duration,
    /// Total running time per iteration.
    pub per_iteration: Duration,
    /// Running time of skims computation per iteration.
    pub per_iteration_skims_computation: Duration,
    /// Running time of pre-day model.
    pub per_iteration_pre_day_model: Duration,
    /// Running time of within-day model.
    pub per_iteration_within_day_model: Duration,
    /// Running time of day-to-day model.
    pub per_iteration_day_to_day_model: Duration,
    /// Running time of skims computation per iteration.
    pub per_iteration_aggregate_results_computation: Duration,
    /// Running time to check the stopping rules per iteration.
    pub per_iteration_stopping_rules_check: Duration,
}

impl RunningTimes {
    /// Updates the total running times with the running times of an iteration.
    pub fn update(&mut self, iteration_running_times: &IterationRunningTimes) {
        self.total += iteration_running_times.total;
        self.total_skims_computation += iteration_running_times.skims_computation;
        self.total_pre_day_model += iteration_running_times.pre_day_model;
        self.total_within_day_model += iteration_running_times.within_day_model;
        self.total_day_to_day_model += iteration_running_times.day_to_day_model;
        self.total_aggregate_results_computation +=
            iteration_running_times.aggregate_results_computation;
        self.total_stopping_rules_check += iteration_running_times.stopping_rules_check;
    }

    /// Computes the running time per iteration.
    pub fn finish(&mut self, iteration_counter: u32) {
        self.per_iteration = self.total / iteration_counter;
        self.per_iteration_skims_computation = self.total_skims_computation / iteration_counter;
        self.per_iteration_pre_day_model = self.total_pre_day_model / iteration_counter;
        self.per_iteration_within_day_model = self.total_within_day_model / iteration_counter;
        self.per_iteration_day_to_day_model = self.total_day_to_day_model / iteration_counter;
        self.per_iteration_aggregate_results_computation =
            self.total_aggregate_results_computation / iteration_counter;
        self.per_iteration_stopping_rules_check =
            self.total_stopping_rules_check / iteration_counter;
    }
}

/// Results of an agent, during a single iteration.
#[derive(Debug, Clone, PartialEq, Serialize, JsonSchema)]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct AgentResult<T> {
    /// Id of the agent.
    pub(crate) id: usize,
    /// Index of the chosen mode.
    pub(crate) mode: ModeIndex,
    /// Expected utility from the trip.
    pub(crate) expected_utility: Utility<T>,
    /// Mode-specific results.
    pub(crate) mode_results: ModeResults<T>,
}

impl<T> AgentResult<T> {
    /// Creates a new AgentResult.
    pub const fn new(
        id: usize,
        mode: ModeIndex,
        expected_utility: Utility<T>,
        mode_results: ModeResults<T>,
    ) -> Self {
        AgentResult {
            id,
            mode,
            expected_utility,
            mode_results,
        }
    }

    /// Returns a reference to the [ModeResults] of the [AgentResult].
    pub fn mode_results(&self) -> &ModeResults<T> {
        &self.mode_results
    }
}

impl<T: TTFNum> AgentResult<T> {
    /// Clones and resets the results in prevision for a new day.
    pub fn reset(&self) -> Self {
        Self {
            id: self.id,
            mode: self.mode,
            expected_utility: self.expected_utility,
            mode_results: self.mode_results.reset(),
        }
    }

    /// Returns `true` if the agent has finished all its trips and activities, i.e., there is
    /// nothing more to simulate for him / her in the within-day model.
    pub fn is_finished(&self) -> bool {
        self.mode_results.is_finished()
    }

    /// Computes the absolute difference between the departure time for the current result and the
    /// departure time of a previous result.
    ///
    /// Returns zero if one of the two result does not have a departure time (i.e., for non-trip
    /// modes).
    pub fn departure_time_shift(&self, previous_result: &AgentResult<T>) -> Time<T> {
        if let (Some(dt), Some(prev_dt)) = (
            self.mode_results.departure_time(),
            previous_result.mode_results.departure_time(),
        ) {
            (dt - prev_dt).abs()
        } else {
            Time::zero()
        }
    }
}

impl<T: TTFNum> AgentResult<T> {
    /// Returns the initial event associated with an [AgentResult] (if any).
    pub fn get_event(&self, agent_id: AgentIndex) -> Option<Box<dyn Event<T>>> {
        self.mode_results.get_event(agent_id, self.mode)
    }

    /// Returns the route that the agent is expected to be taken, if any.
    pub(crate) fn get_expected_route(
        &self,
        agent: &Agent<T>,
        road_network: &RoadNetwork<T>,
        weights: &RoadNetworkWeights<T>,
        unique_vehicles: &UniqueVehicles,
    ) -> Vec<Option<Vec<RoadEvent<T>>>> {
        debug_assert_eq!(agent.id, self.id);
        let chosen_mode = &agent[self.mode];
        self.mode_results
            .get_expected_route(chosen_mode, road_network, weights, unique_vehicles)
    }
}

/// Struct to store the [AgentResult] of each agent in the Simulation.
#[derive(Debug, Default, Clone, Serialize, JsonSchema)]
#[schemars(title = "Agent Results")]
#[schemars(description = "Results for each agent in the simulation.")]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct AgentResults<T>(Vec<AgentResult<T>>);

impl<T> AgentResults<T> {
    /// Creates a new AgentResults from a vector of [AgentResult].
    pub fn from_vec(results: Vec<AgentResult<T>>) -> Self {
        AgentResults(results)
    }

    /// Creates a new empty AgentResults, with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        AgentResults(Vec::with_capacity(capacity))
    }
}

impl<T: TTFNum> AgentResults<T> {
    /// Returns an [EventQueue] with all the events resulting from the pre-day choices of the
    /// agents.
    pub fn get_event_queue(&self) -> EventQueue<T> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(id, agent_result)| agent_result.get_event(AgentIndex::new(id)))
            .collect()
    }

    /// Returns the number of agents who finished their trips.
    pub fn nb_agents_arrived(&self) -> usize {
        self.0.iter().filter(|a| a.is_finished()).count()
    }

    /// Serializes the expected routes to be taken by the agents into a JSON file.
    pub(crate) fn serialize_expected_route(
        &self,
        filename: PathBuf,
        agents: &[Agent<T>],
        road_network: &RoadNetwork<T>,
        weights: &RoadNetworkWeights<T>,
        unique_vehicles: &UniqueVehicles,
    ) -> Result<()> {
        let expected_routes: HashMap<usize, Vec<Option<Vec<RoadEvent<T>>>>> = self
            .0
            .iter()
            .zip(agents.iter())
            .map(|(agent_result, agent)| {
                (
                    agent.id,
                    agent_result.get_expected_route(agent, road_network, weights, unique_vehicles),
                )
            })
            .collect();
        let mut writer = File::create(filename)?;
        let buffer = serde_json::to_vec(&expected_routes)?;
        let encoded_buffer = zstd::encode_all(buffer.as_slice(), 0)?;
        writer.write_all(&encoded_buffer)?;
        Ok(())
    }
}

impl<T> Index<AgentIndex> for AgentResults<T> {
    type Output = AgentResult<T>;

    fn index(&self, index: AgentIndex) -> &Self::Output {
        &self.0[index.index()]
    }
}

impl<T> IndexMut<AgentIndex> for AgentResults<T> {
    fn index_mut(&mut self, index: AgentIndex) -> &mut Self::Output {
        &mut self.0[index.index()]
    }
}

impl<T> Deref for AgentResults<T> {
    type Target = Vec<AgentResult<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for AgentResults<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Stores [AggregateResults] in the given output directory.
///
/// The AggregateResults are stored in the file `iteration[counter].json`.
pub fn save_aggregate_results<T: TTFNum>(
    aggregate_results: &AggregateResults<T>,
    iteration_counter: u32,
    output_dir: &Path,
) -> Result<()> {
    let filename: PathBuf = [
        output_dir.to_str().unwrap(),
        &format!("iteration{iteration_counter}.json"),
    ]
    .iter()
    .collect();
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&aggregate_results)?;
    writer.write_all(&buffer)?;
    Ok(())
}

/// Stores [IterationResults] in the given output directory.
///
/// The IterationResults are stored in the files `agent_results.json` and `weight_results.json`.
pub fn save_iteration_results<T: TTFNum>(
    iteration_results: IterationResults<T>,
    output_dir: &Path,
) -> Result<()> {
    // Save agent results.
    let filename: PathBuf = [output_dir.to_str().unwrap(), "agent_results.json.zst"]
        .iter()
        .collect();
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&iteration_results.agent_results)?;
    let encoded_buffer = zstd::encode_all(buffer.as_slice(), 0)?;
    writer.write_all(&encoded_buffer)?;
    // Save weight results.
    let filename: PathBuf = [output_dir.to_str().unwrap(), "weight_results.json.zst"]
        .iter()
        .collect();
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&iteration_results.weights)?;
    let encoded_buffer = zstd::encode_all(buffer.as_slice(), 0)?;
    writer.write_all(&encoded_buffer)?;
    // Save skims results.
    let filename: PathBuf = [output_dir.to_str().unwrap(), "skim_results.json.zst"]
        .iter()
        .collect();
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&iteration_results.skims)?;
    let encoded_buffer = zstd::encode_all(buffer.as_slice(), 0)?;
    writer.write_all(&encoded_buffer)?;
    Ok(())
}

/// Stores [RunningTimes] in the given output directory.
///
/// The RunningTimes are stored in the file `running_times.json`.
pub fn save_running_times(running_times: RunningTimes, output_dir: &Path) -> Result<()> {
    let filename: PathBuf = [output_dir.to_str().unwrap(), "running_times.json"]
        .iter()
        .collect();
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&running_times)?;
    writer.write_all(&buffer)?;
    Ok(())
}
