// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to simulations.
pub mod results;

use std::ops::Deref;
use std::path::Path;

use anyhow::{bail, Result};
use log::{debug, info};
use rand::prelude::*;
use rand_xorshift::XorShiftRng;
use rayon::prelude::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use time::{Duration, Instant};
use ttf::TTFNum;

use self::results::{
    AgentResults, AggregateResults, IterationResults, IterationRunningTimes, RunningTimes,
    SimulationResults,
};
use crate::agent::{agent_index, Agent};
use crate::event::{EventAlloc, EventInput};
use crate::io;
use crate::mode::trip::results::AggregateTripResults;
use crate::mode::{AggregateConstantResults, AggregateModeResults, Mode, ModeResults};
use crate::network::road_network::skim::EAAllocation;
use crate::network::{Network, NetworkPreprocessingData, NetworkSkim, NetworkWeights};
use crate::parameters::Parameters;
use crate::progress_bar::MetroProgressBar;
use crate::report;
use crate::simulation::results::PreDayAgentResults;
use crate::units::Distribution;

/// Number of events before the time on the within-day progress bar is refreshed.
const UPDATE: usize = 500;

/// An abstract representation of an area to be simulated.
///
/// A simulation is composed of the following items:
///
/// - A set of [agents](Agent) performing trips.
/// - A representation of the [Network], where trips can take place.
/// - A [Parameters] instance.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(title = "Simulation")]
#[schemars(description = "")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
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

impl<T: TTFNum> Simulation<T> {
    /// Runs the simulation.
    pub fn run(&self) -> Result<()> {
        // Initialize the global rayon thread pool.
        rayon::ThreadPoolBuilder::new()
            .num_threads(self.parameters.nb_threads)
            .build_global()
            .unwrap();

        if self.network.get_road_network().is_some()
            && self.parameters.network.road_network.is_none()
        {
            bail!("The road-network parameters are mandatory when a road-network is used.");
        }

        // Pre-process the simulation.
        let preprocess_data = self.preprocess()?;

        let rn_weights = if let Some(road_network) = self.network.get_road_network() {
            // Read the input road-network conditions or create free-flow conditions if no file is
            // given.
            Some(
                if let Some(path) = self.parameters.input_files.road_network_conditions.as_ref() {
                    io::read_rn_weights(
                        path,
                        self.parameters.period,
                        self.parameters
                            .network
                            .road_network
                            .as_ref()
                            .unwrap()
                            .recording_interval,
                        road_network,
                        &preprocess_data
                            .network
                            .get_road_network()
                            .unwrap()
                            .unique_vehicles,
                    )
                    .unwrap()
                } else {
                    road_network.get_free_flow_weights(
                        self.parameters.period,
                        self.parameters.network.road_network.as_ref().unwrap(),
                        preprocess_data.network.get_road_network().unwrap(),
                    )
                },
            )
        } else {
            None
        };

        let mut exp_weights = NetworkWeights::new(rn_weights);
        let mut prev_agent_results = None;
        let mut prev_sim_weights = None;
        let mut iteration_counter: u32 = self.parameters.init_iteration_counter;
        let mut sim_results = SimulationResults::new();
        let mut running_times = RunningTimes::default();
        loop {
            info!("===== Iteration {} =====", iteration_counter);
            let iteration_output = self.run_iteration(
                std::mem::take(&mut exp_weights),
                std::mem::take(&mut prev_sim_weights),
                std::mem::take(&mut prev_agent_results),
                iteration_counter,
                &preprocess_data,
            )?;
            info!("Saving aggregate results");
            results::save_aggregate_results(&iteration_output.aggregate_results, &self.parameters)?;
            // TODO: add this as an option.
            // results::save_iteration_results(
            // &iteration_output.iteration_results,
            // &self.parameters,
            // Some(format!("iter{iteration_counter}")),
            // )?;
            sim_results.push_iteration(iteration_output.aggregate_results);
            running_times.update(&iteration_output.running_times);
            if iteration_output.stop_simulation {
                info!("Stopping simulation");
                sim_results.last_iteration = Some(iteration_output.iteration_results);
                running_times.finish(iteration_counter);
                info!("Writing report");
                report::write_report(&sim_results, &self.parameters.output_directory)?;
                info!("Saving detailed results");
                results::save_running_times(running_times, &self.parameters.output_directory)?;
                results::save_iteration_results(
                    sim_results.last_iteration.as_ref().unwrap(),
                    &self.parameters,
                    None,
                )?;
                info!("Done");
                break;
            }
            (exp_weights, prev_sim_weights, prev_agent_results) = (
                iteration_output.iteration_results.new_exp_weights,
                Some(iteration_output.iteration_results.sim_weights),
                Some(iteration_output.iteration_results.agent_results),
            );
            iteration_counter += 1;
        }
        Ok(())
    }

    /// Compute everything that can be computed before the first iteration of the simulation and
    /// return a [PreprocessingData] instance with the results of these computations.
    pub fn preprocess(&self) -> Result<PreprocessingData<T>> {
        info!("Pre-processing simulation");
        // Run the preprocessing stuff related to the network.
        let network = self.network.preprocess(
            &self.agents,
            self.parameters.period,
            &self.parameters.network,
        )?;
        Ok(PreprocessingData { network })
    }

    /// Runs an iteration given the current [NetworkWeights], the associated [NetworkSkim] and the
    /// [IterationResults] of the previous iteration (if any).
    ///
    /// An iteration consist in running successively the pre-day model, the within-day model and
    /// the day-to-day model.
    pub fn run_iteration(
        &self,
        exp_weights: NetworkWeights<T>,
        prev_sim_weights: Option<NetworkWeights<T>>,
        previous_results_opt: Option<AgentResults<T>>,
        iteration_counter: u32,
        preprocess_data: &PreprocessingData<T>,
    ) -> Result<IterationOutput<T>> {
        let now = Instant::now();
        info!("Computing skims");
        let (skims, t1) = record_time(|| {
            self.network.compute_skims(
                &exp_weights,
                &preprocess_data.network,
                &self.parameters.network,
            )
        })?;
        info!("Running demand model");
        let (mut agent_results, t2) = record_time(|| {
            self.run_pre_day_model(
                &exp_weights,
                &skims,
                preprocess_data,
                previous_results_opt.as_ref(),
                iteration_counter,
            )
        })?;
        info!("Running supply model");
        let (sim_weights, t3) =
            record_time(|| self.run_within_day_model(&mut agent_results, &skims, preprocess_data))?;
        info!("Running learning model");
        let (new_exp_weights, t4) = record_time(|| {
            Ok(self.run_day_to_day_model(&exp_weights, &sim_weights, iteration_counter))
        })?;
        let iteration_results = IterationResults::new(
            agent_results,
            exp_weights,
            sim_weights,
            new_exp_weights,
            &self.network,
            skims,
            previous_results_opt.as_ref(),
        );
        let (aggregate_results, t5) = record_time(|| {
            Ok(self.compute_aggregate_results(
                iteration_counter,
                &iteration_results,
                prev_sim_weights.as_ref(),
            ))
        })?;
        let (stop_simulation, t6) = record_time(|| {
            Ok(self
                .parameters
                .stop(iteration_counter, iteration_results.agent_results()))
        })?;
        crate::show_stats();
        let running_times = IterationRunningTimes {
            skims_computation: t1,
            pre_day_model: t2,
            within_day_model: t3,
            day_to_day_model: t4,
            aggregate_results_computation: t5,
            stopping_rules_check: t6,
            total: now.elapsed(),
        };
        Ok(IterationOutput {
            iteration_results,
            aggregate_results,
            stop_simulation,
            running_times,
        })
    }

    /// Runs the pre-day model, using the given [NetworkSkim] and the [AgentResults] of the
    /// previous iteration (if any).
    /// Returns [AgentResults].
    ///
    /// The pre-day model represents the decisions made by the agents before the start of a
    /// simulated day. In particular, agents choose their mode and departure time.
    pub fn run_pre_day_model(
        &self,
        weights: &NetworkWeights<T>,
        exp_skims: &NetworkSkim<T>,
        preprocess_data: &PreprocessingData<T>,
        previous_results_opt: Option<&AgentResults<T>>,
        iteration_counter: u32,
    ) -> Result<AgentResults<T>> {
        let bp = MetroProgressBar::new(self.agents.len());
        let results = if let Some(previous_results) = previous_results_opt {
            let updates = self.get_update_vector(iteration_counter);
            (&self.agents, previous_results.deref(), updates)
                .into_par_iter()
                .panic_fuse()
                .map_init(
                    EAAllocation::default,
                    |alloc, (agent, prev_agent_result, update)| {
                        bp.inc();
                        agent.make_pre_day_choice(
                            &self.network,
                            self.parameters.period,
                            weights,
                            exp_skims,
                            preprocess_data,
                            Some(prev_agent_result),
                            update,
                            bp.clone(),
                            alloc,
                        )
                    },
                )
                .collect::<Result<Vec<_>, _>>()?
        } else {
            // Everyone has to make a choice.
            self.agents
                .par_iter()
                .panic_fuse()
                .map_init(EAAllocation::default, |alloc, agent| {
                    bp.inc();
                    agent.make_pre_day_choice(
                        &self.network,
                        self.parameters.period,
                        weights,
                        exp_skims,
                        preprocess_data,
                        None,
                        true,
                        bp.clone(),
                        alloc,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        bp.finish();
        Ok(AgentResults::from_vec(results))
    }

    /// Runs the within-day model, using the given [AgentResults] and [NetworkSkim].
    /// Returns the resulting [NetworkWeights] and [AgentResults].
    ///
    /// In the within-day model, the movements of agents and vehicles on the network is simulated,
    /// given their pre-day choices.
    pub fn run_within_day_model(
        &self,
        agent_results: &mut AgentResults<T>,
        skims: &NetworkSkim<T>,
        preprocess_data: &PreprocessingData<T>,
    ) -> Result<NetworkWeights<T>> {
        debug!("Initializing variables");
        let mut state = self.network.get_blank_state(&self.parameters);
        let mut events = agent_results.get_event_queue();
        let mut nb_events = 0;
        info!("Executing events");
        let bp = MetroProgressBar::new(events.len())
            .with_message(self.parameters.period.start().to_string());
        let mut input = EventInput {
            agents: &self.agents,
            network: &self.network,
            preprocess_data,
            skims,
            agent_results,
            progress_bar: bp.clone(),
        };
        let mut alloc = EventAlloc::default();
        while let Some(event) = events.pop() {
            nb_events += 1;
            if nb_events % UPDATE == 0 {
                bp.set_message(format!("{}", event.get_time()));
            }
            let agent_has_arrived = event.execute(
                &mut input,
                state.get_mut_road_network().unwrap(),
                &mut alloc,
                &mut events,
            )?;
            if agent_has_arrived {
                bp.inc();
            }
        }
        bp.finish();
        debug_assert_eq!(agent_results.len(), agent_results.nb_agents_arrived());
        debug!("Succesfully executed {} events", nb_events);
        // Compute network weights.
        debug!("Computing network weights");
        let weights = state.into_weights(
            &self.network,
            self.parameters.period,
            &self.parameters.network,
            &preprocess_data.network,
        );
        Ok(weights)
    }

    /// Runs the day-to-day model, using the given old [NetworkWeights] (from the previous
    /// iteration) and simulated [NetworkWeights] (from the within-day model).
    /// Returns the [NetworkWeights] for the next iteration.
    pub fn run_day_to_day_model(
        &self,
        old_weights: &NetworkWeights<T>,
        weights: &NetworkWeights<T>,
        iteration_counter: u32,
    ) -> NetworkWeights<T> {
        self.parameters
            .learn(old_weights, weights, iteration_counter)
    }

    /// Returns [AggregateResults] given the [IterationResults] of the current iteration and the
    /// [AgentResults] of the previous iteration (if any).
    pub fn compute_aggregate_results(
        &self,
        iteration_counter: u32,
        results: &IterationResults<T>,
        prev_sim_weights: Option<&NetworkWeights<T>>,
    ) -> AggregateResults<T> {
        let surplus = Distribution::from_iterator(
            results
                .iter_agent_results()
                .map(|(_agent_id, r)| r.expected_utility),
        )
        .unwrap();
        let mut trip_entries = Vec::with_capacity(self.agents.len());
        let mut cst_utilities = Vec::with_capacity(self.agents.len());
        for i in 0..(results.agent_results().len()) {
            let agent_result = &results.agent_results()[agent_index(i)];
            let mode_id = agent_result.mode_index;
            match (&self.agents[i][mode_id], &agent_result.mode_results) {
                (Mode::Trip(trip_mode), ModeResults::Trip(trip_result)) => {
                    trip_entries.push((trip_mode, trip_result));
                }
                (&Mode::Constant((_, utility)), ModeResults::None) => cst_utilities.push(utility),
                _ => panic!("Unsupported mode and mode results combination"),
            }
        }
        trip_entries.shrink_to_fit();
        cst_utilities.shrink_to_fit();
        let road_results = if trip_entries.is_empty() {
            None
        } else {
            Some(AggregateTripResults::from_agent_results(trip_entries))
        };
        let cst_results = if cst_utilities.is_empty() {
            None
        } else {
            Some(AggregateConstantResults::from_utilities(cst_utilities))
        };
        let mode_results = AggregateModeResults {
            trip_modes: road_results,
            constant: cst_results,
        };
        // The RMSE for simulated road-network weights use the expected weights for the first
        // iteration (whenever `prev_sim_weights` is `None`).
        let sim_road_network_weights_rmse = results.sim_weights.road_network().map(|w| {
            w.rmse(
                prev_sim_weights
                    .unwrap_or(&results.exp_weights)
                    .road_network()
                    .unwrap(),
            )
        });
        let exp_road_network_weights_rmse = results
            .sim_weights
            .road_network()
            .map(|w| w.rmse(results.exp_weights.road_network().unwrap()));
        AggregateResults {
            iteration_counter,
            surplus,
            mode_results,
            sim_road_network_weights_rmse,
            exp_road_network_weights_rmse,
        }
    }

    /// Builds a vector of boolean indicating the agents that can switch their choice for the next
    /// iteration.
    fn get_update_vector(&self, iteration_counter: u32) -> Vec<bool> {
        // To change the seed from one iteration to another, we add the iteration number to the
        // default seed.
        let mut rng = self
            .parameters
            .random_seed
            .map_or_else(XorShiftRng::from_entropy, |seed| {
                XorShiftRng::seed_from_u64(seed + iteration_counter as u64)
            });
        let mut updates = vec![true; self.agents.len()];
        // Number of agents that will be able to switch their choice.
        let n = (self.parameters.update_ratio * self.agents.len() as f64) as usize;
        if n < self.agents.len() {
            updates[n..].fill(false);
            updates.shuffle(&mut rng);
        }
        updates
    }
}

impl<T: TTFNum + Into<f64>> Simulation<T> {
    /// Computes the pre-day choices, using the given [NetworkWeights] as initial weights of the
    /// network, and stores the results in the output directory.
    ///
    /// If `init_weights` is `None`, free-flow weights are used to initialize the simulation.
    pub fn compute_and_store_choices(
        &self,
        init_weights: Option<NetworkWeights<T>>,
        output_dir: &Path,
    ) -> Result<()> {
        // Initialize the global rayon thread pool.
        rayon::ThreadPoolBuilder::new()
            .num_threads(self.parameters.nb_threads)
            .build_global()
            .unwrap();
        let preprocess_data = self.preprocess()?;
        let weights = if let Some(weights) = init_weights {
            weights
        } else {
            self.network.get_free_flow_weights(
                self.parameters.period,
                &self.parameters.network,
                &preprocess_data.network,
            )
        };
        info!("Computing skims");
        let skims = self.network.compute_skims(
            &weights,
            &preprocess_data.network,
            &self.parameters.network,
        )?;
        info!("Running pre-day model");
        let bp = MetroProgressBar::new(self.agents.len());
        let mut pre_day_agent_results = PreDayAgentResults::from_agent_results(
            self.agents
                .par_iter()
                .panic_fuse()
                .map_init(EAAllocation::default, |alloc, agent| {
                    bp.inc();
                    agent.make_pre_day_choice(
                        &self.network,
                        self.parameters.period,
                        &weights,
                        &skims,
                        &preprocess_data,
                        None,
                        true,
                        bp.clone(),
                        alloc,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        bp.finish();
        // At this point, we have the pre-day agent results but the route, route length and route
        // free-flow travel time is empty. We compute them now (if `pre_compute_route` is `true`).
        if let (Some(road_network), Some(rn_weights)) =
            (self.network.get_road_network(), weights.road_network())
        {
            let unique_vehicles = &preprocess_data
                .network
                .get_road_network()
                .unwrap()
                .unique_vehicles;
            pre_day_agent_results.add_expected_routes(
                &self.agents,
                road_network,
                rn_weights,
                unique_vehicles,
            );
        }
        info!("Saving results");
        results::save_choices(&pre_day_agent_results, output_dir, &self.parameters)?;
        info!("Done");
        Ok(())
    }
}

/// Additional input data for the simulation which is computed before running the simulation.
#[derive(Clone, Debug, Default)]
pub struct PreprocessingData<T> {
    /// Network-specific pre-processing data.
    pub network: NetworkPreprocessingData<T>,
}

/// Output of an iteration run.
#[derive(Clone, Debug)]
pub struct IterationOutput<T> {
    /// Detailed results of the iteration.
    pub iteration_results: IterationResults<T>,
    /// Aggregate results of the iteration.
    pub aggregate_results: AggregateResults<T>,
    /// If `true`, the simulation should be stop (one stopping criterion was activated).
    pub stop_simulation: bool,
    /// The running times of the iteration.
    pub running_times: IterationRunningTimes,
}

fn record_time<T>(func: impl FnOnce() -> Result<T>) -> Result<(T, Duration)> {
    let now = Instant::now();
    let result = func()?;
    Ok((result, now.elapsed()))
}
