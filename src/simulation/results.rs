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
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use time::Duration;
use ttf::TTFNum;

use crate::agent::{agent_index, AgentIndex};
use crate::event::{Event, EventQueue};
use crate::mode::{AggregateModeResults, Mode, ModeIndex, ModeResults, PreDayChoices};
use crate::network::{NetworkSkim, NetworkWeights};
use crate::schedule_utility::ScheduleUtility;
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

/// Results from the pre-day choices of an agent.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize, JsonSchema)]
pub struct PreDayResult<T> {
    /// Index of the chosen mode.
    mode: ModeIndex,
    /// Expected utility from the trip.
    expected_utility: Utility<T>,
    /// Mode-specific pre-day results.
    choices: PreDayChoices<T>,
}

impl<T> PreDayResult<T> {
    /// Creates a new PreDayResult.
    pub const fn new(
        mode: ModeIndex,
        expected_utility: Utility<T>,
        choices: PreDayChoices<T>,
    ) -> Self {
        PreDayResult {
            mode,
            expected_utility,
            choices,
        }
    }

    /// Returns a reference to the [PreDayChoices].
    pub const fn get_choices(&self) -> &PreDayChoices<T> {
        &self.choices
    }

    /// Returns the index of the chosen mode.
    pub const fn get_mode_index(&self) -> ModeIndex {
        self.mode
    }
}

impl<T: Copy> PreDayResult<T> {
    /// Returns the expected utility.
    pub const fn get_expected_utility(&self) -> Utility<T> {
        self.expected_utility
    }
}

impl<T: TTFNum + 'static> PreDayResult<T> {
    /// Converts the [PreDayResult] into an [AgentResult].
    pub fn into_agent_result(self, agent_id: usize) -> AgentResult<T> {
        let mode_results = self.choices.init_mode_results();
        AgentResult::new(agent_id, self, mode_results)
    }

    /// Returns the event (if any) associated with the pre-day choices.
    pub fn get_event(&self, agent: AgentIndex) -> Option<Box<dyn Event<T>>> {
        self.choices.get_event(agent)
    }
}

/// Results of an agent, during a single iteration.
#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct AgentResult<T> {
    /// Id of the agent.
    id: usize,
    /// Utility resulting from the trip.
    utility: Option<Utility<T>>,
    /// Departure time from origin.
    departure_time: Option<Time<T>>,
    /// Arrival time at destination.
    arrival_time: Option<Time<T>>,
    /// Results from the pre-day model.
    pre_day_results: PreDayResult<T>,
    /// Mode-specific results.
    mode_results: ModeResults<T>,
}

impl<T> AgentResult<T> {
    /// Creates a new AgentResult.
    pub const fn new(
        id: usize,
        pre_day_results: PreDayResult<T>,
        mode_results: ModeResults<T>,
    ) -> Self {
        AgentResult {
            id,
            utility: None,
            departure_time: None,
            arrival_time: None,
            pre_day_results,
            mode_results,
        }
    }

    /// Returns the id of the agent.
    pub const fn id(&self) -> usize {
        self.id
    }

    /// Returns a reference to the [PreDayResult].
    pub const fn pre_day_results(&self) -> &PreDayResult<T> {
        &self.pre_day_results
    }

    /// Returns a reference to the [ModeResults].
    pub const fn mode_results(&self) -> &ModeResults<T> {
        &self.mode_results
    }

    /// Returns a mutable reference to the [ModeResults].
    pub fn mut_mode_results(&mut self) -> &mut ModeResults<T> {
        &mut self.mode_results
    }

    /// Sets the departure time to the given value.
    pub fn set_departure_time(&mut self, departure_time: Time<T>) {
        self.departure_time = Some(departure_time);
    }

    /// Sets the arrival time to the given value.
    pub fn set_arrival_time(&mut self, arrival_time: Time<T>) {
        self.arrival_time = Some(arrival_time);
    }

    /// Returns `true` if the agent has arrived at destination.
    pub const fn has_arrived(&self) -> bool {
        self.arrival_time.is_some()
    }
}

impl<T: Copy> AgentResult<T> {
    /// Returns the utility of the agent.
    pub const fn utility(&self) -> Option<Utility<T>> {
        self.utility
    }

    /// Returns the departure time of the agent.
    pub const fn departure_time(&self) -> Option<Time<T>> {
        self.departure_time
    }

    /// Returns the arrival time of the agent.
    pub const fn arrival_time(&self) -> Option<Time<T>> {
        self.arrival_time
    }
}

impl<T: TTFNum> AgentResult<T> {
    /// Process the results of the agent.
    ///
    /// The utility is computed from the given [ScheduleUtility] and [Mode] description, and the
    /// stored [ModeResults].
    pub fn process_results(&mut self, schedule_utility: &ScheduleUtility<T>, mode: &Mode<T>) {
        match &mut self.mode_results {
            ModeResults::Road(road_results) => road_results.process_results(),
            ModeResults::None => (),
        }
        self.utility = Some(mode.get_utility(
            &self.mode_results,
            schedule_utility,
            self.departure_time,
            self.arrival_time,
        ));
    }
}

/// Struct to store the [AgentResult] of each agent in the Simulation.
#[derive(Debug, Default, Clone, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Agent Results")]
#[schemars(description = "Results for each agent in the simulation.")]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct AgentResults<T>(Vec<AgentResult<T>>);

impl<T> AgentResults<T> {
    /// Creates a new empty AgentResults, with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        AgentResults(Vec::with_capacity(capacity))
    }
}

impl<T: Copy> AgentResults<T> {
    /// Iterates over the departure times of the agents.
    pub fn departure_times(&self) -> impl Iterator<Item = Option<Time<T>>> + '_ {
        self.iter().map(|r| r.departure_time)
    }
}

impl<T: TTFNum + 'static> AgentResults<T> {
    /// Returns an [EventQueue] with all the events resulting from the pre-day choices of the
    /// agents.
    pub fn get_event_queue(&self) -> EventQueue<T> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(id, r)| r.pre_day_results().get_event(AgentIndex::new(id)))
            .collect()
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
