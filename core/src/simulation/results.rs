// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs holding the results of a simulation.
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use time::Duration;
use ttf::TTFNum;

use crate::agent::{agent_index, Agent, AgentIndex};
use crate::event::{Event, EventQueue};
use crate::io;
use crate::mode::{AggregateModeResults, ModeIndex, ModeResults, PreDayModeResults};
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::{RoadNetwork, RoadNetworkWeights};
use crate::network::{Network, NetworkSkim, NetworkWeights};
use crate::parameters::{Parameters, SavingFormat};
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
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AggregateResults<T> {
    /// Current value of the iteration counter.
    pub iteration_counter: u32,
    /// Distribution of the surplus of the agents.
    pub surplus: Distribution<Utility<T>>,
    /// Mode-specific aggregate results.
    pub mode_results: AggregateModeResults<T>,
    /// Root mean square difference between the simulated road-network weights of the current and
    /// previous iteration (except for the first iteration, where the expected weights are used
    /// instead).
    ///
    /// `None` if there is no road network.
    pub sim_road_network_weights_rmse: Option<Time<T>>,
    /// Root mean square difference between the simulated road-network weights of the current
    /// iteration and the expected road-network weights of the previous iteration.
    ///
    /// `None` if there is no road network.
    pub exp_road_network_weights_rmse: Option<Time<T>>,
}

/// Detailed results of an iteration.
#[derive(Debug, Clone)]
pub struct IterationResults<T> {
    /// Agent-specific results.
    pub agent_results: AgentResults<T>,
    /// Expected weights of the network, before the day-to-day model.
    pub exp_weights: NetworkWeights<T>,
    /// Simulated weights of the network, during the within-day model.
    pub sim_weights: NetworkWeights<T>,
    /// Expected weights of the network, after the day-to-day model.
    pub new_exp_weights: NetworkWeights<T>,
    /// Skims of the network.
    pub skims: NetworkSkim<T>,
}

impl<T: TTFNum> IterationResults<T> {
    /// Creates a new IterationResults.
    pub fn new(
        mut agent_results: AgentResults<T>,
        exp_weights: NetworkWeights<T>,
        sim_weights: NetworkWeights<T>,
        new_exp_weights: NetworkWeights<T>,
        network: &Network<T>,
        skims: NetworkSkim<T>,
        previous_results_opt: Option<&AgentResults<T>>,
    ) -> Self {
        if let Some(previous_agent_results) = previous_results_opt {
            agent_results.with_previous_results(previous_agent_results, network);
        }
        IterationResults {
            agent_results,
            exp_weights,
            sim_weights,
            new_exp_weights,
            skims,
        }
    }
}

impl<T> IterationResults<T> {
    /// Returns a reference to the [AgentResults].
    pub const fn agent_results(&self) -> &AgentResults<T> {
        &self.agent_results
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
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct AgentResult<T> {
    /// Id of the agent.
    pub(crate) id: usize,
    /// Id of the chosen mode.
    pub(crate) mode_id: usize,
    /// Index of the chosen mode.
    pub(crate) mode_index: ModeIndex,
    /// Expected utility from the trip.
    pub(crate) expected_utility: Utility<T>,
    /// Mode-specific results.
    pub(crate) mode_results: ModeResults<T>,
    /// Did the agent shifted to another mode from previous to current iteration?
    pub(crate) shifted_mode: bool,
}

impl<T> AgentResult<T> {
    /// Creates a new AgentResult.
    pub const fn new(
        id: usize,
        mode_id: usize,
        mode: ModeIndex,
        expected_utility: Utility<T>,
        mode_results: ModeResults<T>,
    ) -> Self {
        AgentResult {
            id,
            mode_id,
            mode_index: mode,
            expected_utility,
            mode_results,
            shifted_mode: false,
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
            mode_id: 0,
            mode_index: ModeIndex::new(0),
            expected_utility: self.expected_utility,
            mode_results: self.mode_results.reset(),
            shifted_mode: false,
        }
    }

    /// Returns `true` if the agent has finished all its trips and activities, i.e., there is
    /// nothing more to simulate for him / her in the within-day model.
    pub fn is_finished(&self) -> bool {
        self.mode_results.is_finished()
    }

    pub(crate) fn with_previous_results(&mut self, previous_result: &Self, network: &Network<T>) {
        if self.mode_index == previous_result.mode_index {
            self.shifted_mode = false;
            self.mode_results
                .with_previous_results(&previous_result.mode_results, network);
        } else {
            self.shifted_mode = true;
        }
    }

    /// Returns the initial event associated with an [AgentResult] (if any).
    pub fn get_event(&self, agent_id: AgentIndex) -> Option<Box<dyn Event<T>>> {
        self.mode_results.get_event(agent_id, self.mode_index)
    }
}

/// Struct to store the [AgentResult] of each agent in the Simulation.
#[derive(Debug, Default, Clone, Serialize)]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct AgentResults<T>(pub(crate) Vec<AgentResult<T>>);

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

    /// Computes some additional values using the results of the previous iteration (if needed).
    pub fn with_previous_results(&mut self, previous_results: &Self, network: &Network<T>) {
        for (ar, prev_ar) in self.iter_mut().zip(previous_results.iter()) {
            ar.with_previous_results(prev_ar, network);
        }
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

/// Pre-day results of an agent.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct PreDayAgentResult<T> {
    /// Id of the agent.
    pub(crate) id: usize,
    /// Id of the chosen mode.
    pub(crate) mode_id: usize,
    /// Index of the chosen mode.
    pub(crate) mode_index: ModeIndex,
    /// Expected utility from the trip.
    pub(crate) expected_utility: Utility<T>,
    /// Mode-specific pre-day results.
    pub(crate) mode_results: PreDayModeResults<T>,
}

impl<T> From<AgentResult<T>> for PreDayAgentResult<T> {
    fn from(value: AgentResult<T>) -> Self {
        Self {
            id: value.id,
            mode_id: value.mode_id,
            mode_index: value.mode_index,
            expected_utility: value.expected_utility,
            mode_results: value.mode_results.into(),
        }
    }
}

impl<T: TTFNum> PreDayAgentResult<T> {
    fn add_expected_route(
        &mut self,
        agent: &Agent<T>,
        road_network: &RoadNetwork<T>,
        weights: &RoadNetworkWeights<T>,
        unique_vehicles: &UniqueVehicles,
    ) {
        debug_assert_eq!(agent.id, self.id);
        let chosen_mode = &agent[self.mode_index];
        self.mode_results
            .add_expected_route(chosen_mode, road_network, weights, unique_vehicles)
    }
}

/// Struct to store the [PreDayAgentResult] of each agent in the Simulation.
#[derive(Debug, Default, Clone, Serialize)]
#[serde(bound(serialize = "T: TTFNum"))]
pub struct PreDayAgentResults<T>(pub(crate) Vec<PreDayAgentResult<T>>);

impl<T> PreDayAgentResults<T> {
    /// Creates a new PreDayAgentResults from a vector of partially initialized [AgentResult].
    pub(crate) fn from_agent_results(results: Vec<AgentResult<T>>) -> Self {
        Self(results.into_iter().map(|ar| ar.into()).collect())
    }
}

impl<T: TTFNum> PreDayAgentResults<T> {
    pub(crate) fn add_expected_routes(
        &mut self,
        agents: &[Agent<T>],
        road_network: &RoadNetwork<T>,
        weights: &RoadNetworkWeights<T>,
        unique_vehicles: &UniqueVehicles,
    ) {
        for (agent_result, agent) in self.0.iter_mut().zip(agents.iter()) {
            agent_result.add_expected_route(agent, road_network, weights, unique_vehicles);
        }
    }
}

/// Stores [AggregateResults] in the given output directory.
///
/// The AggregateResults are stored in the file `iteration[counter].json`.
pub fn save_aggregate_results<T: TTFNum>(
    aggregate_results: &AggregateResults<T>,
    parameters: &Parameters<T>,
) -> Result<()> {
    match parameters.saving_format {
        SavingFormat::JSON => {
            io::json::append_json(
                aggregate_results.clone(),
                &parameters.output_directory,
                "iteration_results",
            )?;
        }
        SavingFormat::Parquet => {
            io::parquet::append_parquet(
                aggregate_results.clone(),
                &parameters.output_directory,
                "iteration_results",
            )?;
        }
        SavingFormat::CSV => {
            io::csv::append_csv(
                aggregate_results.clone(),
                &parameters.output_directory,
                "iteration_results",
            )?;
        }
    }
    Ok(())
}

/// Stores [IterationResults] in the given output directory.
pub fn save_iteration_results<T: TTFNum>(
    iteration_results: &IterationResults<T>,
    parameters: &Parameters<T>,
    subdirectory: Option<String>,
) -> Result<()> {
    let output_dir: PathBuf = if let Some(subdir) = subdirectory {
        [parameters.output_directory.clone(), PathBuf::from(subdir)]
            .iter()
            .collect()
    } else {
        parameters.output_directory.clone()
    };
    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(&output_dir)
        .with_context(|| format!("Failed to create output directory `{:?}`", output_dir))?;

    match parameters.saving_format {
        SavingFormat::JSON => {
            io::json::write_compressed_json(
                &iteration_results.agent_results,
                &output_dir,
                "agent_results",
            )?;
            io::json::write_compressed_json(
                &iteration_results.exp_weights,
                &output_dir,
                "exp_weight_results",
            )?;
            io::json::write_compressed_json(
                &iteration_results.sim_weights,
                &output_dir,
                "sim_weight_results",
            )?;
            io::json::write_compressed_json(
                &iteration_results.new_exp_weights,
                &output_dir,
                "next_exp_weight_results",
            )?;
        }
        SavingFormat::Parquet => {
            io::parquet::write_parquet(&iteration_results.agent_results, &output_dir)?;
            io::parquet::write_parquet_with_prefix(
                &iteration_results.exp_weights,
                &output_dir,
                "net_cond_exp_",
            )?;
            io::parquet::write_parquet_with_prefix(
                &iteration_results.sim_weights,
                &output_dir,
                "net_cond_sim_",
            )?;
            io::parquet::write_parquet_with_prefix(
                &iteration_results.new_exp_weights,
                &output_dir,
                "net_cond_next_exp_",
            )?;
        }
        SavingFormat::CSV => {
            io::csv::write_csv(&iteration_results.agent_results, &output_dir)?;
            io::csv::write_csv_with_prefix(
                &iteration_results.exp_weights,
                &output_dir,
                "net_cond_exp_",
            )?;
            io::csv::write_csv_with_prefix(
                &iteration_results.sim_weights,
                &output_dir,
                "net_cond_sim_",
            )?;
            io::csv::write_csv_with_prefix(
                &iteration_results.new_exp_weights,
                &output_dir,
                "net_cond_next_exp_",
            )?;
        }
    }
    // Save skims results.
    io::json::write_compressed_json(&iteration_results.skims, &output_dir, "skim_results")?;
    Ok(())
}

/// Stores [RunningTimes] in the given output directory.
///
/// The RunningTimes are stored in the file `running_times.json`.
pub fn save_running_times(running_times: RunningTimes, output_dir: &Path) -> Result<()> {
    io::json::write_json(running_times, output_dir, "running_times")?;
    Ok(())
}

/// Stores [AgentResults] in the given output directory.
pub fn save_choices<T: TTFNum>(
    agent_results: &PreDayAgentResults<T>,
    parameters: &Parameters<T>,
) -> Result<()> {
    match parameters.saving_format {
        SavingFormat::JSON => {
            io::json::write_compressed_json(
                agent_results,
                &parameters.output_directory,
                "agent_results",
            )?;
        }
        SavingFormat::Parquet => {
            io::parquet::write_parquet(agent_results, &parameters.output_directory)?;
        }
        SavingFormat::CSV => {
            io::csv::write_csv(agent_results, &parameters.output_directory)?;
        }
    }
    Ok(())
}
