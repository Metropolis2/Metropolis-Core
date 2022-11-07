// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to simulations.
pub mod results;

use std::ops::Deref;
use std::path::Path;

use anyhow::Result;
use indicatif::{ProgressBar, ProgressStyle};
use log::{debug, info, log_enabled, Level};
use object_pool::Pool;
use rand::prelude::*;
use rand_xorshift::XorShiftRng;
use rayon::prelude::*;
use results::{AgentResults, AggregateResults, IterationResults, PreDayResult, SimulationResults};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::agent::Agent;
use crate::mode::road::AggregateRoadResults;
use crate::mode::{AggregateConstantResults, AggregateModeResults, Mode};
use crate::network::{Network, NetworkPreprocessingData, NetworkSkim, NetworkWeights};
use crate::parameters::Parameters;
use crate::report;
use crate::units::Distribution;

/// An abstract representation of an area to be simulated.
///
/// A simulation is composed of the following items:
///
/// - A set of [agents](Agent) performing trips.
/// - A representation of the [Network], where trips can take place.
/// - A [Parameters] instance.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[schemars(title = "Simulation")]
#[schemars(description = "")]
pub struct Simulation<T> {
    #[serde(default)]
    agents: Vec<Agent<T>>,
    network: Network<T>,
    parameters: Parameters<T>,
}

impl<T> Simulation<T> {
    /// Create a new Simulation.
    pub fn new(agents: Vec<Agent<T>>, network: Network<T>, parameters: Parameters<T>) -> Self {
        Self {
            agents,
            network,
            parameters,
        }
    }

    /// Return a reference to the [Network] of the simulation.
    pub const fn get_network(&self) -> &Network<T> {
        &self.network
    }

    /// Return a reference to the [Parameters] of the simulation.
    pub const fn get_parameters(&self) -> &Parameters<T> {
        &self.parameters
    }
}

impl<T: TTFNum + Serialize + 'static> Simulation<T> {
    /// Run the simulation, starting from free-flow weights.
    pub fn run(&self, output_dir: &Path) -> Result<()> {
        let weights = self.network.get_free_flow_weights();
        self.run_from_weights(weights, output_dir)
    }

    /// Run the simulation, using the given [NetworkWeights] as initial weights of the network.
    pub fn run_from_weights(
        &self,
        init_weights: NetworkWeights<T>,
        output_dir: &Path,
    ) -> Result<()> {
        let preprocess_data = self.preprocess();
        let mut weights = init_weights;
        let mut prev_agent_results = None;
        let mut iteration_counter: u64 = 1;
        let mut sim_results = SimulationResults::new();
        loop {
            info!("===== Iteration {} =====", iteration_counter);
            info!("Computing skims");
            let skims = self.network.compute_skims(
                &weights,
                &preprocess_data.network,
                &self.parameters.network,
            )?;
            let iteration_results = self.run_iteration(
                &weights,
                skims,
                prev_agent_results.as_ref(),
                iteration_counter,
            )?;
            let aggregate_results =
                self.compute_aggregate_results(&iteration_results, prev_agent_results.as_ref());
            self.parameters.save_aggregate_results(
                &aggregate_results,
                iteration_counter,
                output_dir,
            )?;
            sim_results.push_iteration(aggregate_results);
            info!("Checking stopping rules");
            if self.parameters.stop(
                iteration_counter,
                iteration_results.agent_results(),
                prev_agent_results.as_ref(),
            ) {
                info!("Stopping simulation");
                sim_results.last_iteration = Some(iteration_results);
                info!("Writing report");
                report::write_report(&sim_results, output_dir)?;
                info!("Saving detailed results");
                self.parameters
                    .save_iteration_results(sim_results.last_iteration.unwrap(), output_dir)?;
                break;
            }
            iteration_counter += 1;
            info!("Computing weights");
            (weights, prev_agent_results) = (
                iteration_results.weights,
                Some(iteration_results.agent_results),
            );
        }
        Ok(())
    }

    /// Compute everything that can be computed before the first iteration of the simulation and
    /// return a [PreprocessingData] instance with the results of these computations.
    pub fn preprocess(&self) -> PreprocessingData {
        // Run the preprocessing stuff related to the network.
        let network = self.network.preprocess(&self.agents);
        PreprocessingData { network }
    }

    /// Runs an iteration given the current [NetworkWeights], the associated [NetworkSkim] and the
    /// [IterationResults] of the previous iteration (if any).
    ///
    /// An iteration consist in running successively the pre-day model, the within-day model and
    /// the day-to-day model.
    pub fn run_iteration(
        &self,
        weights: &NetworkWeights<T>,
        skims: NetworkSkim<T>,
        previous_results_opt: Option<&AgentResults<T>>,
        iteration_counter: u64,
    ) -> Result<IterationResults<T>> {
        let pre_day_results =
            self.run_pre_day_model(&skims, previous_results_opt, iteration_counter)?;
        info!("Running within-day model");
        let (sim_weights, within_day_results) = self.run_within_day_model(pre_day_results, &skims);
        info!("Running day-to-day model");
        let new_weights = self.run_day_to_day_model(weights, &sim_weights, iteration_counter);
        crate::show_stats();
        Ok(IterationResults::new(within_day_results, new_weights))
    }

    /// Runs the pre-day model, using the given [NetworkSkim] and the [AgentResults] of the
    /// previous iteration (if any).
    /// Returns a Vec of [PreDayResult].
    ///
    /// The pre-day model represents the decisions made by the agents before the start of a
    /// simulated day. In particular, agents choose their mode and departure time.
    pub fn run_pre_day_model(
        &self,
        exp_skims: &NetworkSkim<T>,
        previous_results_opt: Option<&AgentResults<T>>,
        iteration_counter: u64,
    ) -> Result<Vec<PreDayResult<T>>> {
        let pool = Pool::new(rayon::current_num_threads(), Default::default);
        info!("Running pre-day model");
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(self.agents.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        let results = if let Some(previous_results) = previous_results_opt {
            let updates = self.get_update_vector(iteration_counter);
            (&self.agents, previous_results.deref(), updates)
                .into_par_iter()
                .map_init(
                    || pool.pull(Default::default),
                    |alloc, (agent, prev_agent_result, update)| {
                        bp.inc(1);
                        agent.make_pre_day_choice(
                            exp_skims,
                            Some(prev_agent_result.pre_day_results()),
                            update,
                            alloc,
                        )
                    },
                )
                .collect::<Result<Vec<_>, _>>()?
        } else {
            // Everyone has to make a choice.
            self.agents
                .par_iter()
                .map_init(
                    || pool.pull(Default::default),
                    |alloc, agent| {
                        bp.inc(1);
                        agent.make_pre_day_choice(exp_skims, None, true, alloc)
                    },
                )
                .collect::<Result<Vec<_>, _>>()?
        };
        bp.finish_and_clear();
        Ok(results)
    }

    /// Runs the within-day model, using the given Vec of [PreDayResult] and [NetworkSkim].
    /// Returns the resulting [NetworkWeights] and [AgentResults].
    ///
    /// In the within-day model, the movements of agents and vehicles on the network is simulated,
    /// given their pre-day choices.
    pub fn run_within_day_model(
        &self,
        pre_day_results: Vec<PreDayResult<T>>,
        skims: &NetworkSkim<T>,
    ) -> (NetworkWeights<T>, AgentResults<T>) {
        debug!("Initializing variables");
        let mut state = self.network.get_blank_state();
        let mut results = self.init_agent_results(pre_day_results);
        let mut events = results.get_event_queue();
        let mut nb_events = 0;
        info!("Executing events");
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(events.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        while let Some(event) = events.pop() {
            nb_events += 1;
            if let Some(result) = event.get_agent_index().map(|id| &mut results[id]) {
                // The event is associated to an agent.
                event.execute(&self.network, skims, &mut state, Some(result), &mut events);
                if result.has_arrived() {
                    bp.inc(1);
                }
            } else {
                event.execute(&self.network, skims, &mut state, None, &mut events);
            }
        }
        bp.finish_and_clear();
        // Drop the events queue (it is empty) so that it no longer borrows the results.
        drop(events);
        debug!("Succesfully executed {} events", nb_events);
        // Compute network weights.
        debug!("Computing network weights");
        let weights = state.get_weights(&self.parameters);
        // Compute agent utilities.
        debug!("Computing agent utilities");
        for (i, r) in results.iter_mut().enumerate() {
            let chosen_mode = r.pre_day_results().get_mode_index();
            r.compute_utility(
                self.agents[i].schedule_utility(),
                &self.agents[i][chosen_mode],
            );
        }
        (weights, results)
    }

    /// Runs the day-to-day model, using the given old [NetworkWeights] (from the previous
    /// iteration) and simulated [NetworkWeights] (from the within-day model).
    /// Returns the [NetworkWeights] for the next iteration.
    pub fn run_day_to_day_model(
        &self,
        old_weights: &NetworkWeights<T>,
        weights: &NetworkWeights<T>,
        iteration_counter: u64,
    ) -> NetworkWeights<T> {
        self.parameters
            .learn(old_weights, weights, iteration_counter)
    }

    /// Returns [AggregateResults] given the [IterationResults] of the current iteration and the
    /// [AgentResults] of the previous iteration (if any).
    pub fn compute_aggregate_results(
        &self,
        results: &IterationResults<T>,
        prev_agent_results_opt: Option<&AgentResults<T>>,
    ) -> AggregateResults<T> {
        let surplus = Distribution::from_iterator(
            results
                .iter_agent_results()
                .map(|(_agent_id, r)| r.pre_day_results().get_expected_utility()),
        )
        .unwrap();
        let mut road_entries = Vec::with_capacity(self.agents.len());
        let mut cst_entries = Vec::with_capacity(self.agents.len());
        if let Some(prev_agent_results) = prev_agent_results_opt {
            for ((agent_id, agent_result), prev_agent_result) in
                results.iter_agent_results().zip(prev_agent_results.iter())
            {
                let mode_id = agent_result.pre_day_results().get_mode_index();
                match &self.agents[agent_id.index()][mode_id] {
                    Mode::Road(road_mode) => {
                        road_entries.push((road_mode, agent_result, Some(prev_agent_result)))
                    }
                    Mode::Constant(_) => cst_entries.push(agent_result),
                }
            }
        } else {
            for (agent_id, agent_result) in results.iter_agent_results() {
                let mode_id = agent_result.pre_day_results().get_mode_index();
                match &self.agents[agent_id.index()][mode_id] {
                    Mode::Road(road_mode) => road_entries.push((road_mode, agent_result, None)),
                    Mode::Constant(_) => cst_entries.push(agent_result),
                }
            }
        }
        let road_results = if road_entries.is_empty() {
            None
        } else {
            Some(AggregateRoadResults::from_agent_results(
                road_entries,
                self.network
                    .get_road_network()
                    .expect("Found RoadResults but no road network"),
            ))
        };
        let cst_results = if cst_entries.is_empty() {
            None
        } else {
            Some(AggregateConstantResults::from_agent_results(cst_entries))
        };
        let mode_results = AggregateModeResults {
            road: road_results,
            constant: cst_results,
        };
        AggregateResults {
            surplus,
            mode_results,
        }
    }

    /// Converts a Vec of [PreDayResult] into [AgentResults].
    fn init_agent_results(&self, pre_day_results: Vec<PreDayResult<T>>) -> AgentResults<T> {
        let mut results = AgentResults::with_capacity(pre_day_results.len());
        for (agent, pre_day_result) in self.agents.iter().zip(pre_day_results.into_iter()) {
            results.push(pre_day_result.into_agent_result(agent.id));
        }
        results
    }

    /// Builds a vector of boolean indicating the agents that can switch their choice for the next
    /// iteration.
    fn get_update_vector(&self, iteration_counter: u64) -> Vec<bool> {
        // To change the seed from one iteration to another, we add the iteration number to the
        // default seed.
        let mut rng = self
            .parameters
            .random_seed
            .map_or_else(XorShiftRng::from_entropy, |seed| {
                XorShiftRng::seed_from_u64(seed + iteration_counter)
            });
        let mut updates = vec![true; self.agents.len()];
        // Number of agents that will be able to switch their choice.
        let n = (self.parameters.update_ratio * self.agents.len() as f64) as usize;
        updates[n..].fill(false);
        updates.shuffle(&mut rng);
        updates
    }
}

/// Additional input data for the simulation which is computed before running the simulation.
#[derive(Clone, Debug)]
pub struct PreprocessingData {
    /// Network-specific pre-processing data.
    pub network: NetworkPreprocessingData,
}
