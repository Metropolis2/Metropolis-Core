// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to simulations.
pub mod results;

use std::fs::File;
use std::io::{Read, Write};
use std::ops::Deref;
use std::path::{Path, PathBuf};

use anyhow::Result;
use log::{debug, info, LevelFilter};
use rand::prelude::*;
use rand_xorshift::XorShiftRng;
use rayon::prelude::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use simplelog::{ColorChoice, CombinedLogger, Config, TermLogger, TerminalMode, WriteLogger};
use time::{Duration, Instant};
use ttf::TTFNum;

use self::results::{
    AgentResults, AggregateResults, IterationResults, IterationRunningTimes, RunningTimes,
    SimulationResults,
};
use crate::agent::{agent_index, Agent};
use crate::event::{EventAlloc, EventInput};
use crate::mode::trip::results::AggregateTripResults;
use crate::mode::{AggregateConstantResults, AggregateModeResults, Mode, ModeResults};
use crate::network::road_network::skim::EAAllocation;
use crate::network::road_network::RoadNetwork;
use crate::network::{Network, NetworkPreprocessingData, NetworkSkim, NetworkWeights};
use crate::parameters::Parameters;
use crate::progress_bar::MetroProgressBar;
use crate::report;
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
    /// Run the simulation, using the given [NetworkWeights] as initial weights of the network.
    ///
    /// If `init_weights` is `None`, free-flow weights are used to initialize the simulation.
    pub fn run_from_weights(
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
        let mut weights = if let Some(weights) = init_weights {
            weights
        } else {
            self.network.get_free_flow_weights(&preprocess_data.network)
        };
        let mut prev_agent_results = None;
        let mut iteration_counter: u32 = self.parameters.init_iteration_counter;
        let mut sim_results = SimulationResults::new();
        let mut running_times = RunningTimes::default();
        loop {
            info!("===== Iteration {} =====", iteration_counter);
            let iteration_output = self.run_iteration(
                &weights,
                prev_agent_results.as_ref(),
                iteration_counter,
                &preprocess_data,
            )?;
            results::save_aggregate_results(
                &iteration_output.aggregate_results,
                iteration_counter,
                output_dir,
            )?;
            sim_results.push_iteration(iteration_output.aggregate_results);
            running_times.update(&iteration_output.running_times);
            if iteration_output.stop_simulation {
                info!("Stopping simulation");
                sim_results.last_iteration = Some(iteration_output.iteration_results);
                running_times.finish(iteration_counter);
                info!("Writing report");
                report::write_report(&sim_results, output_dir)?;
                info!("Saving detailed results");
                results::save_running_times(running_times, output_dir)?;
                results::save_iteration_results(sim_results.last_iteration.unwrap(), output_dir)?;
                info!("Done");
                break;
            }
            (weights, prev_agent_results) = (
                iteration_output.iteration_results.weights,
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
        let network = self
            .network
            .preprocess(&self.agents, &self.parameters.network)?;
        Ok(PreprocessingData { network })
    }

    /// Runs an iteration given the current [NetworkWeights], the associated [NetworkSkim] and the
    /// [IterationResults] of the previous iteration (if any).
    ///
    /// An iteration consist in running successively the pre-day model, the within-day model and
    /// the day-to-day model.
    pub fn run_iteration(
        &self,
        weights: &NetworkWeights<T>,
        previous_results_opt: Option<&AgentResults<T>>,
        iteration_counter: u32,
        preprocess_data: &PreprocessingData<T>,
    ) -> Result<IterationOutput<T>> {
        let now = Instant::now();
        info!("Computing skims");
        let (skims, t1) = record_time(|| {
            self.network
                .compute_skims(weights, &preprocess_data.network, &self.parameters.network)
        })?;
        info!("Running pre-day model");
        let (mut agent_results, t2) = record_time(|| {
            self.run_pre_day_model(
                &skims,
                preprocess_data,
                previous_results_opt,
                iteration_counter,
            )
        })?;
        info!("Running within-day model");
        let (sim_weights, t3) =
            record_time(|| self.run_within_day_model(&mut agent_results, &skims, preprocess_data))?;
        info!("Running day-to-day model");
        let (new_weights, t4) = record_time(|| {
            Ok(self.run_day_to_day_model(weights, &sim_weights, iteration_counter))
        })?;
        let iteration_results = IterationResults::new(agent_results, new_weights, skims);
        info!("Computing aggregate results");
        let (aggregate_results, t5) = record_time(|| {
            Ok(self.compute_aggregate_results(&iteration_results, previous_results_opt))
        })?;
        info!("Checking stopping rules");
        let (stop_simulation, t6) = record_time(|| {
            Ok(self.parameters.stop(
                iteration_counter,
                iteration_results.agent_results(),
                previous_results_opt,
            ))
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
        let weights = state.into_weights(&self.network, &preprocess_data.network);
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
        results: &IterationResults<T>,
        prev_agent_results: Option<&AgentResults<T>>,
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
            let mode_id = agent_result.mode;
            match (&self.agents[i][mode_id], &agent_result.mode_results) {
                (Mode::Trip(trip_mode), ModeResults::Trip(trip_result)) => {
                    let prev_trip_result = if let Some(ModeResults::Trip(prev_trip_result)) =
                        prev_agent_results.map(|r| &r[agent_index(i)].mode_results)
                    {
                        Some(prev_trip_result)
                    } else {
                        None
                    };
                    trip_entries.push((trip_mode, trip_result, prev_trip_result));
                }
                (&Mode::Constant(utility), ModeResults::None) => cst_utilities.push(utility),
                _ => panic!("Unsupported mode and mode results combination"),
            }
        }
        let road_results = if trip_entries.is_empty() {
            None
        } else {
            Some(AggregateTripResults::from_agent_results(
                trip_entries,
                &self.network,
            ))
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
        AggregateResults {
            surplus,
            mode_results,
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
            self.network.get_free_flow_weights(&preprocess_data.network)
        };
        info!("Computing skims");
        let skims = self.network.compute_skims(
            &weights,
            &preprocess_data.network,
            &self.parameters.network,
        )?;

        info!("Running pre-day model");
        let agent_results = self.run_pre_day_model(
            &skims,
            &preprocess_data,
            None,
            self.parameters.init_iteration_counter,
        )?;
        info!("Saving results");
        let filename: PathBuf = [output_dir.to_str().unwrap(), "agent_results.json.zst"]
            .iter()
            .collect();
        let mut writer = File::create(filename)?;
        let buffer = serde_json::to_vec(&agent_results)?;
        let encoded_buffer = zstd::encode_all(buffer.as_slice(), 0)?;
        writer.write_all(&encoded_buffer)?;
        info!("Done");
        Ok(())
    }
}

/// Initializes logging to a file and terminal.
fn initialize_logging(output: &Path) {
    let log_filename: PathBuf = [output.to_str().unwrap(), "log.txt"].iter().collect();
    let log_file = File::create(log_filename).expect("Failed to create log file");
    CombinedLogger::init(vec![
        TermLogger::new(
            LevelFilter::Info,
            Config::default(),
            TerminalMode::Mixed,
            ColorChoice::Auto,
        ),
        WriteLogger::new(LevelFilter::Debug, Config::default(), log_file),
    ])
    .expect("Failed to initialize logging");
}

/// Deserializes a simulation from JSON files.
fn get_simulation_from_json_files(
    agents: &Path,
    parameters: &Path,
    road_network: Option<&Path>,
) -> Simulation<f64> {
    // Read input files.
    info!("Reading input files");
    let mut bytes = Vec::new();
    File::open(agents)
        .unwrap_or_else(|err| panic!("Unable to open agents file `{agents:?}`: {err}"))
        .read_to_end(&mut bytes)
        .unwrap_or_else(|err| panic!("Unable to read agents file `{agents:?}`: {err}"));
    let agents: Vec<Agent<f64>> = serde_json::from_slice(&bytes).expect("Unable to parse agents");

    let mut bytes = Vec::new();
    File::open(parameters)
        .unwrap_or_else(|err| panic!("Unable to open parameters file `{parameters:?}`: {err}"))
        .read_to_end(&mut bytes)
        .unwrap_or_else(|err| panic!("Unable to read parameters file `{parameters:?}`: {err}"));
    let parameters: Parameters<f64> =
        serde_json::from_slice(&bytes).expect("Unable to parse parameters");

    let road_network: Option<RoadNetwork<f64>> = if let Some(rn) = road_network {
        let mut bytes = Vec::new();
        File::open(rn)
            .unwrap_or_else(|err| panic!("Unable to open road network file `{rn:?}`: {err}"))
            .read_to_end(&mut bytes)
            .unwrap_or_else(|err| panic!("Unable to read road network file `{rn:?}`: {err}"));
        Some(serde_json::from_slice(&bytes).expect("Unable to parse road network"))
    } else {
        None
    };

    let network = Network::new(road_network);
    Simulation::new(agents, network, parameters)
}

/// Deserializes [NetworkWeights] from a JSON file.
fn get_weights_from_json_file(weights: &Path) -> NetworkWeights<f64> {
    let mut file = File::open(weights)
        .unwrap_or_else(|err| panic!("Unable to open network weights file `{weights:?}`: {err}"));
    let bytes = if weights.extension().and_then(|s| s.to_str()) == Some("zst") {
        zstd::decode_all(&file).unwrap_or_else(|err| {
            panic!("Unable to decode network weights file `{weights:?}`: {err}")
        })
    } else {
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes).unwrap_or_else(|err| {
            panic!("Unable to read network weights file `{weights:?}`: {err}")
        });
        bytes
    };
    serde_json::from_slice(&bytes).expect("Unable to parse network weights")
}

/// Deserializes a simulation from JSON input files, computes the pre-day choices and stores them
/// in the given output directory.
pub fn get_choices_from_json_files(
    agents: &Path,
    parameters: &Path,
    road_network: Option<&Path>,
    weights: Option<&Path>,
    output: &Path,
) -> Result<()> {
    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(output)?;

    initialize_logging(output);

    let simulation = get_simulation_from_json_files(agents, parameters, road_network);

    let weights = weights.map(get_weights_from_json_file);

    // Run the simulation.
    simulation.compute_and_store_choices(weights, output)
}

/// Deserializes a simulation from JSON input files, runs it and stores the results to a given
/// output directory.
pub fn run_simulation_from_json_files(
    agents: &Path,
    parameters: &Path,
    road_network: Option<&Path>,
    weights: Option<&Path>,
    output: &Path,
) -> Result<()> {
    // Create output directory if it does not exists yet.
    std::fs::create_dir_all(output)?;

    initialize_logging(output);

    let simulation = get_simulation_from_json_files(agents, parameters, road_network);

    let weights = weights.map(get_weights_from_json_file);

    // Run the simulation.
    simulation.run_from_weights(weights, output)
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
