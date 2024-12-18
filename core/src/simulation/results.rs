// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs holding the results of a simulation.
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Result};
use serde::Serialize;

use crate::event::{Event, EventQueue};
use crate::io;
use crate::mode::{AggregateModeResults, ModeIndex, ModeResults, PreDayModeResults};
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::RoadNetworkWeights;
use crate::network::{NetworkSkim, NetworkWeights};
use crate::parameters::SavingFormat;
use crate::population::{agent_index, AgentIndex};
use crate::units::{Distribution, NonNegativeSeconds, Utility};

/// Struct to store the results of a [Simulation](super::Simulation).
#[derive(Clone, Debug, Default)]
pub(crate) struct SimulationResults {
    /// [AggregateResults] of each iteration.
    pub(crate) iterations: Vec<AggregateResults>,
    /// [IterationResults] of the last iteration.
    pub(crate) last_iteration: Option<IterationResults>,
}

impl SimulationResults {
    /// Create an empty SimulationResults.
    pub(crate) fn new() -> Self {
        SimulationResults::default()
    }

    /// Appends the [AggregateResults] of an iteration to the [SimulationResults].
    pub(crate) fn push_iteration(&mut self, iteration: AggregateResults) {
        self.iterations.push(iteration);
    }
}

/// Aggregate results summarizing the results of an iteration.
#[derive(Debug, Clone)]
pub(crate) struct AggregateResults {
    /// Current value of the iteration counter.
    pub(crate) iteration_counter: u32,
    /// Distribution of the surplus of the agents.
    pub(crate) surplus: Distribution<Utility>,
    /// Mode-specific aggregate results.
    pub(crate) mode_results: AggregateModeResults,
    /// Root mean square difference between the simulated road-network weights of the current and
    /// previous iteration (except for the first iteration, where the expected weights are used
    /// instead).
    ///
    /// `None` if there is no road network.
    pub(crate) sim_road_network_weights_rmse: Option<NonNegativeSeconds>,
    /// Root mean square difference between the simulated road-network weights of the current
    /// iteration and the expected road-network weights of the previous iteration.
    ///
    /// `None` if there is no road network.
    pub(crate) exp_road_network_weights_rmse: Option<NonNegativeSeconds>,
}

/// Detailed results of an iteration.
#[derive(Debug, Clone)]
pub struct IterationResults {
    /// Agent-specific results.
    pub agent_results: AgentResults,
    /// Expected weights of the network, before the day-to-day model.
    pub exp_weights: NetworkWeights,
    /// Simulated weights of the network, during the supply model.
    pub sim_weights: NetworkWeights,
    /// Expected weights of the network, after the learning model.
    pub new_exp_weights: NetworkWeights,
    /// Skims of the network.
    pub skims: NetworkSkim,
}

impl IterationResults {
    /// Creates a new IterationResults.
    pub fn new(
        mut agent_results: AgentResults,
        exp_weights: NetworkWeights,
        sim_weights: NetworkWeights,
        new_exp_weights: NetworkWeights,
        skims: NetworkSkim,
        previous_results_opt: Option<&AgentResults>,
    ) -> Self {
        if let Some(previous_agent_results) = previous_results_opt {
            agent_results.with_previous_results(previous_agent_results);
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

impl IterationResults {
    /// Returns a reference to the [AgentResults].
    pub const fn agent_results(&self) -> &AgentResults {
        &self.agent_results
    }

    /// Iterates over the [AgentIndex] and [AgentResult] of the [IterationResults].
    pub fn iter_agent_results(&self) -> impl Iterator<Item = (AgentIndex, &AgentResult)> {
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
    /// Running time of demand model.
    pub demand_model: Duration,
    /// Running time of supply model.
    pub supply_model: Duration,
    /// Running time of learning model.
    pub learning_model: Duration,
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
    /// Total running time of demand model.
    pub total_demand_model: Duration,
    /// Total running time of supply model.
    pub total_supply_model: Duration,
    /// Total running time of learning model.
    pub total_learning_model: Duration,
    /// Total running time of aggregate results computation.
    pub total_aggregate_results_computation: Duration,
    /// Total running time to check the stopping rules.
    pub total_stopping_rules_check: Duration,
    /// Total running time per iteration.
    pub per_iteration: Duration,
    /// Running time of skims computation per iteration.
    pub per_iteration_skims_computation: Duration,
    /// Running time of demand model.
    pub per_iteration_demand_model: Duration,
    /// Running time of supply model.
    pub per_iteration_supply_model: Duration,
    /// Running time of learning model.
    pub per_iteration_learning_model: Duration,
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
        self.total_demand_model += iteration_running_times.demand_model;
        self.total_supply_model += iteration_running_times.supply_model;
        self.total_learning_model += iteration_running_times.learning_model;
        self.total_aggregate_results_computation +=
            iteration_running_times.aggregate_results_computation;
        self.total_stopping_rules_check += iteration_running_times.stopping_rules_check;
    }

    /// Computes the running time per iteration.
    pub fn finish(&mut self, iteration_counter: u32) {
        self.per_iteration = self.total / iteration_counter;
        self.per_iteration_skims_computation = self.total_skims_computation / iteration_counter;
        self.per_iteration_demand_model = self.total_demand_model / iteration_counter;
        self.per_iteration_supply_model = self.total_supply_model / iteration_counter;
        self.per_iteration_learning_model = self.total_learning_model / iteration_counter;
        self.per_iteration_aggregate_results_computation =
            self.total_aggregate_results_computation / iteration_counter;
        self.per_iteration_stopping_rules_check =
            self.total_stopping_rules_check / iteration_counter;
    }
}

/// Results of an agent, during a single iteration.
#[derive(Debug, Clone, PartialEq)]
pub struct AgentResult {
    /// Id of the agent.
    pub(crate) id: usize,
    /// Id of the chosen mode.
    pub(crate) mode_id: usize,
    /// Index of the chosen mode.
    pub(crate) mode_index: ModeIndex,
    /// Expected utility from the trip.
    pub(crate) expected_utility: Utility,
    /// Mode-specific results.
    pub(crate) mode_results: ModeResults,
    /// Did the agent shifted to another mode from previous to current iteration?
    pub(crate) shifted_mode: bool,
}

impl AgentResult {
    /// Creates a new AgentResult.
    pub const fn new(
        id: usize,
        mode_id: usize,
        mode: ModeIndex,
        expected_utility: Utility,
        mode_results: ModeResults,
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
    pub fn mode_results(&self) -> &ModeResults {
        &self.mode_results
    }
}

impl AgentResult {
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
    /// nothing more to simulate for him / her in the supply model.
    pub fn is_finished(&self) -> bool {
        self.mode_results.is_finished()
    }

    pub(crate) fn with_previous_results(&mut self, previous_result: &Self) {
        if self.mode_index == previous_result.mode_index {
            self.shifted_mode = false;
            self.mode_results
                .with_previous_results(&previous_result.mode_results);
        } else {
            self.shifted_mode = true;
        }
    }

    /// Returns the initial event associated with an [AgentResult] (if any).
    pub(crate) fn get_event(&self, agent_id: AgentIndex) -> Option<Box<dyn Event>> {
        self.mode_results.get_event(agent_id, self.mode_index)
    }
}

/// Struct to store the [AgentResult] of each agent in the Simulation.
#[derive(Debug, Default, Clone)]
pub struct AgentResults(pub(crate) Vec<AgentResult>);

impl AgentResults {
    /// Creates a new AgentResults from a vector of [AgentResult].
    pub fn from_vec(results: Vec<AgentResult>) -> Self {
        AgentResults(results)
    }

    /// Creates a new empty AgentResults, with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        AgentResults(Vec::with_capacity(capacity))
    }
}

impl AgentResults {
    /// Returns an [EventQueue] with all the events resulting from the pre-day choices of the
    /// agents.
    pub(crate) fn get_event_queue(&self) -> EventQueue {
        EventQueue::new(
            self.0
                .iter()
                .enumerate()
                .filter_map(|(id, agent_result)| agent_result.get_event(AgentIndex::new(id))),
            crate::parameters::period(),
        )
    }

    /// Returns the number of agents who finished their trips.
    pub fn nb_agents_arrived(&self) -> usize {
        self.0.iter().filter(|a| a.is_finished()).count()
    }

    /// Computes some additional values using the results of the previous iteration (if needed).
    pub fn with_previous_results(&mut self, previous_results: &Self) {
        for (ar, prev_ar) in self.iter_mut().zip(previous_results.iter()) {
            ar.with_previous_results(prev_ar);
        }
    }
}

impl Index<AgentIndex> for AgentResults {
    type Output = AgentResult;

    fn index(&self, index: AgentIndex) -> &Self::Output {
        &self.0[index.index()]
    }
}

impl IndexMut<AgentIndex> for AgentResults {
    fn index_mut(&mut self, index: AgentIndex) -> &mut Self::Output {
        &mut self.0[index.index()]
    }
}

impl Deref for AgentResults {
    type Target = Vec<AgentResult>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for AgentResults {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Pre-day results of an agent.
#[derive(Debug, Clone, PartialEq)]
pub struct PreDayAgentResult {
    /// Id of the agent.
    pub(crate) id: usize,
    /// Id of the chosen mode.
    pub(crate) mode_id: usize,
    /// Index of the chosen mode.
    pub(crate) mode_index: ModeIndex,
    /// Expected utility from the trip.
    pub(crate) expected_utility: Utility,
    /// Mode-specific pre-day results.
    pub(crate) mode_results: PreDayModeResults,
}

impl From<AgentResult> for PreDayAgentResult {
    fn from(value: AgentResult) -> Self {
        Self {
            id: value.id,
            mode_id: value.mode_id,
            mode_index: value.mode_index,
            expected_utility: value.expected_utility,
            mode_results: value.mode_results.into(),
        }
    }
}

impl PreDayAgentResult {
    fn add_expected_route(
        &mut self,
        i: usize,
        weights: &RoadNetworkWeights,
        unique_vehicles: &UniqueVehicles,
    ) {
        let chosen_mode = crate::population::agent_alternative(i, self.mode_index);
        self.mode_results
            .add_expected_route(chosen_mode, weights, unique_vehicles)
    }
}

/// Struct to store the [PreDayAgentResult] of each agent in the Simulation.
#[derive(Debug, Default, Clone)]
pub struct PreDayAgentResults(pub(crate) Vec<PreDayAgentResult>);

impl PreDayAgentResults {
    /// Creates a new PreDayAgentResults from a vector of partially initialized [AgentResult].
    pub(crate) fn from_agent_results(results: Vec<AgentResult>) -> Self {
        Self(results.into_iter().map(|ar| ar.into()).collect())
    }
}

impl PreDayAgentResults {
    pub(crate) fn add_expected_routes(
        &mut self,
        weights: &RoadNetworkWeights,
        unique_vehicles: &UniqueVehicles,
    ) {
        for (i, agent_result) in self.0.iter_mut().enumerate() {
            agent_result.add_expected_route(i, weights, unique_vehicles);
        }
    }
}

/// Stores [AggregateResults] in the given output directory.
///
/// The AggregateResults are stored in the file `iteration[counter].json`.
pub(crate) fn save_aggregate_results(aggregate_results: &AggregateResults) -> Result<()> {
    match crate::parameters::saving_format() {
        SavingFormat::Parquet => {
            io::parquet::append_parquet(
                aggregate_results.clone(),
                crate::parameters::output_directory(),
                "iteration_results",
            )?;
        }
        SavingFormat::CSV => {
            io::csv::append_csv(
                aggregate_results.clone(),
                crate::parameters::output_directory(),
                "iteration_results",
            )?;
        }
    }
    Ok(())
}

/// Stores [IterationResults] in the given output directory.
pub fn save_iteration_results(
    iteration_results: &IterationResults,
    subdirectory: Option<String>,
) -> Result<()> {
    let output_dir: PathBuf = if let Some(subdir) = subdirectory {
        [
            crate::parameters::output_directory().to_path_buf(),
            PathBuf::from(subdir),
        ]
        .iter()
        .collect()
    } else {
        crate::parameters::output_directory().to_path_buf()
    };
    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(&output_dir)
        .with_context(|| format!("Failed to create output directory `{:?}`", output_dir))?;

    match crate::parameters::saving_format() {
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
pub fn save_running_times(running_times: RunningTimes) -> Result<()> {
    io::json::write_json(
        running_times,
        crate::parameters::output_directory(),
        "running_times",
    )?;
    Ok(())
}

/// Stores [AgentResults] in the given output directory.
pub fn save_choices(agent_results: &PreDayAgentResults) -> Result<()> {
    match crate::parameters::saving_format() {
        SavingFormat::Parquet => {
            io::parquet::write_parquet(agent_results, crate::parameters::output_directory())?;
        }
        SavingFormat::CSV => {
            io::csv::write_csv(agent_results, crate::parameters::output_directory())?;
        }
    }
    Ok(())
}
