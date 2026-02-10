// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Everything related to simulations.
pub mod results;

use std::ops::Deref;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use hashbrown::HashSet;
use log::{debug, info, warn};
use rand::prelude::*;
use rand_xorshift::XorShiftRng;
use rayon::prelude::*;

use self::results::{
    AgentResults, AggregateResults, IterationResults, IterationRunningTimes, RunningTimes,
    SimulationResults,
};
use crate::event::{EventAlloc, EventInput};
use crate::io;
use crate::mode::trip::results::AggregateTripResults;
use crate::mode::{AggregateConstantResults, AggregateModeResults, Mode, ModeResults};
use crate::network::road_network::skim::EAAllocation;
use crate::network::{NetworkPreprocessingData, NetworkSkim, NetworkWeights};
use crate::population::agent_index;
use crate::progress_bar::MetroProgressBar;
use crate::report;
use crate::simulation::results::PreDayAgentResults;
use crate::units::Distribution;

/// Number of events before the time on the within-day progress bar is refreshed.
const UPDATE: usize = 100000;

/// Returns the path of the iteration results file of the simulation.
fn iteration_results_filename() -> PathBuf {
    let extension = crate::parameters::saving_format().extension();
    [
        crate::parameters::output_directory().to_str().unwrap(),
        &format!("iteration_results.{extension}"),
    ]
    .iter()
    .collect()
}

/// Runs the simulation.
pub fn run() -> Result<()> {
    if crate::parameters::only_compute_decisions() {
        compute_and_store_choices()
    } else {
        run_impl()
    }
}

fn run_impl() -> Result<()> {
    // The previous iteration_results file need to be removed if it exists.
    let filename = iteration_results_filename();
    if filename.is_file() {
        warn!("Removing already existing file `{filename:?}`");
        std::fs::remove_file(&filename)
            .with_context(|| format!("Failed to remove file: `{filename:?}`"))?;
    }

    let (preprocess_data, mut exp_weights) = initialize()?;
    let mut prev_agent_results = None;
    let mut prev_sim_weights = None;
    let mut iteration_counter: u32 = crate::parameters::init_iteration_counter();
    let mut sim_results = SimulationResults::new();
    let mut running_times = RunningTimes::default();
    loop {
        info!("===== Iteration {} =====", iteration_counter);
        let iteration_output = run_iteration(
            std::mem::take(&mut exp_weights),
            std::mem::take(&mut prev_sim_weights),
            std::mem::take(&mut prev_agent_results),
            iteration_counter,
            &preprocess_data,
        )?;
        info!("Saving aggregate results");
        results::save_aggregate_results(&iteration_output.aggregate_results)?;
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
            report::write_report(&sim_results)?;
            info!("Saving detailed results");
            results::save_running_times(running_times)?;
            results::save_iteration_results(sim_results.last_iteration.as_ref().unwrap(), None)?;
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
pub fn preprocess() -> Result<PreprocessingData> {
    info!("Pre-processing simulation");
    // Run the preprocessing stuff related to the network.
    let network = crate::network::preprocess()?;
    Ok(PreprocessingData { network })
}

/// Runs an iteration given the current [NetworkWeights], the associated [NetworkSkim] and the
/// [IterationResults] of the previous iteration (if any).
///
/// An iteration consist in running successively the pre-day model, the within-day model and
/// the day-to-day model.
pub fn run_iteration(
    exp_weights: NetworkWeights,
    prev_sim_weights: Option<NetworkWeights>,
    previous_results_opt: Option<AgentResults>,
    iteration_counter: u32,
    preprocess_data: &PreprocessingData,
) -> Result<IterationOutput> {
    let now = Instant::now();
    info!("Computing skims");
    let (skims, t1) =
        record_time(|| crate::network::compute_skims(&exp_weights, &preprocess_data.network))?;
    info!("Running demand model");
    let (mut agent_results, t2) = record_time(|| {
        run_pre_day_model(
            &exp_weights,
            &skims,
            preprocess_data,
            previous_results_opt.as_ref(),
            iteration_counter,
        )
    })?;
    info!("Running supply model");
    let (sim_weights, t3) =
        record_time(|| run_within_day_model(&mut agent_results, &skims, preprocess_data))?;
    info!("Running learning model");
    let (new_exp_weights, t4) = record_time(|| {
        Ok(run_day_to_day_model(
            &exp_weights,
            &sim_weights,
            iteration_counter,
        ))
    })?;
    let iteration_results = IterationResults::new(
        agent_results,
        exp_weights,
        sim_weights,
        new_exp_weights,
        skims,
        previous_results_opt.as_ref(),
    );
    let (aggregate_results, t5) = record_time(|| {
        Ok(compute_aggregate_results(
            iteration_counter,
            &iteration_results,
            prev_sim_weights.as_ref(),
        ))
    })?;
    let (stop_simulation, t6) =
        record_time(|| Ok(stop(iteration_counter, iteration_results.agent_results())))?;
    let running_times = IterationRunningTimes {
        skims_computation: t1,
        demand_model: t2,
        supply_model: t3,
        learning_model: t4,
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
    weights: &NetworkWeights,
    exp_skims: &NetworkSkim,
    preprocess_data: &PreprocessingData,
    previous_results_opt: Option<&AgentResults>,
    iteration_counter: u32,
) -> Result<AgentResults> {
    let bp = MetroProgressBar::new(crate::population::nb_agents());
    let results = if let Some(previous_results) = previous_results_opt {
        let updates = get_update_vector(iteration_counter);
        (
            crate::population::agents(),
            previous_results.deref(),
            updates,
        )
            .into_par_iter()
            .panic_fuse()
            .map_init(
                EAAllocation::default,
                |alloc, (agent, prev_agent_result, update)| {
                    bp.inc();
                    agent.make_pre_day_choice(
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
        crate::population::agents()
            .par_iter()
            .panic_fuse()
            .map_init(EAAllocation::default, |alloc, agent| {
                bp.inc();
                agent.make_pre_day_choice(
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
    agent_results: &mut AgentResults,
    skims: &NetworkSkim,
    preprocess_data: &PreprocessingData,
) -> Result<NetworkWeights> {
    debug!("Initializing variables");
    let mut state = crate::network::blank_state();
    let mut events = agent_results.get_event_queue();
    let mut nb_events = 0;
    info!("Executing events");
    let bp = MetroProgressBar::new(events.len())
        .with_message(crate::parameters::period().start().to_string());
    let mut input = EventInput {
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
    let weights = state.into_weights(&preprocess_data.network);
    Ok(weights)
}

/// Runs the day-to-day model, using the given old [NetworkWeights] (from the previous
/// iteration) and simulated [NetworkWeights] (from the within-day model).
/// Returns the [NetworkWeights] for the next iteration.
pub fn run_day_to_day_model(
    old_weights: &NetworkWeights,
    weights: &NetworkWeights,
    iteration_counter: u32,
) -> NetworkWeights {
    // At this point, the iteration counter has not been increment yet.
    crate::parameters::learning_model().learn(old_weights, weights, iteration_counter + 1)
}

/// Returns [AggregateResults] given the [IterationResults] of the current iteration and the
/// [AgentResults] of the previous iteration (if any).
pub(crate) fn compute_aggregate_results(
    iteration_counter: u32,
    results: &IterationResults,
    prev_sim_weights: Option<&NetworkWeights>,
) -> AggregateResults {
    let surplus = Distribution::from_iterator(
        results
            .iter_agent_results()
            .map(|(_agent_id, r)| r.expected_utility),
    )
    .unwrap();
    let mut trip_entries = Vec::with_capacity(crate::population::nb_agents());
    let mut cst_utilities = Vec::with_capacity(crate::population::nb_agents());
    for i in 0..(results.agent_results().len()) {
        let agent_result = &results.agent_results()[agent_index(i)];
        let mode_id = agent_result.mode_index;
        match (
            crate::population::agent_alternative(i, mode_id),
            &agent_result.mode_results,
        ) {
            (Mode::Trip(trip_mode), ModeResults::Trip(trip_result)) => {
                trip_entries.push((trip_mode, trip_result));
            }
            (Mode::Constant(_), &ModeResults::Constant(utility)) => cst_utilities.push(utility),
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
fn get_update_vector(iteration_counter: u32) -> Vec<bool> {
    // To change the seed from one iteration to another, we add the iteration number to the
    // default seed.
    let mut rng = crate::parameters::random_seed().map_or_else(rand::make_rng, |seed| {
        XorShiftRng::seed_from_u64(seed + iteration_counter as u64)
    });
    let nb_agents = crate::population::nb_agents();
    let mut updates = vec![true; nb_agents];
    // Number of agents that will be able to switch their choice.
    let n = (crate::parameters::update_ratio() * nb_agents as f64) as usize;
    if n < nb_agents {
        updates[n..].fill(false);
        updates.shuffle(&mut rng);
    }
    updates
}

/// Initializes the simulation before running it.
fn initialize() -> Result<(PreprocessingData, NetworkWeights)> {
    // Initialize the global rayon thread pool.
    rayon::ThreadPoolBuilder::new()
        .num_threads(crate::parameters::nb_threads())
        .build_global()
        .unwrap();
    // Check that the simulation is valid.
    check_validity()?;
    // Pre-process the simulation.
    let preprocess_data = preprocess()?;
    let rn_weights = if crate::network::has_road_network() {
        // Read the input road-network conditions or create free-flow conditions if no file is
        // given.
        Some(
            if let Some(path) = crate::parameters::input_files()
                .road_network_conditions
                .as_ref()
            {
                io::read_rn_weights(
                    path,
                    &preprocess_data
                        .network
                        .get_road_network()
                        .unwrap()
                        .unique_vehicles,
                )
                .unwrap()
            } else {
                crate::network::road_network::free_flow_weights(
                    preprocess_data.network.get_road_network().unwrap(),
                )
            },
        )
    } else {
        None
    };
    let weights = NetworkWeights::new(rn_weights);
    Ok((preprocess_data, weights))
}

/// Performs some validity checks that can only be done when all the simulation input has been
/// imported.
fn check_validity() -> Result<()> {
    // Check the validity of the simulation parameters.
    crate::parameters::check_validity()?;
    if crate::network::has_road_network() {
        // Check that all road trips' origins and destinations are part of the road network.
        let origins: HashSet<_> = crate::population::all_road_trips_origins();
        let destinations: HashSet<_> = crate::population::all_road_trips_destinations();
        let road_network_nodes: HashSet<_> =
            crate::network::road_network::iter_original_node_ids().collect();
        let invalid_origins: HashSet<_> = origins.difference(&road_network_nodes).collect();
        if !invalid_origins.is_empty() {
            let invalid_origins_as_vec: Vec<_> = invalid_origins
                .into_iter()
                .map(|n| format!("{}", n))
                .collect();
            let invalid_ids = if invalid_origins_as_vec.len() > 10 {
                format!("{}, ...", invalid_origins_as_vec[..10].join(", "))
            } else {
                invalid_origins_as_vec.join(", ")
            };
            let msg =
            "The following node ids are used as trip origin but are not part of the road network";
            bail!("{msg}: {invalid_ids}");
        }
        let invalid_destinations: HashSet<_> =
            destinations.difference(&road_network_nodes).collect();
        if !invalid_destinations.is_empty() {
            let invalid_destinations_as_vec: Vec<_> = invalid_destinations
                .into_iter()
                .map(|n| format!("{}", n))
                .collect();
            let invalid_ids = if invalid_destinations_as_vec.len() > 10 {
                format!("{}, ...", invalid_destinations_as_vec[..10].join(", "))
            } else {
                invalid_destinations_as_vec.join(", ")
            };
            let msg = "The following node ids are used as trip destination \
                   but are not part of the road network";
            bail!("{msg}: {invalid_ids}");
        }
    }
    Ok(())
}

/// Computes the pre-day choices of the simulation.
pub fn compute_and_store_choices() -> Result<()> {
    let (preprocess_data, weights) = initialize()?;
    info!("Computing skims");
    let skims = crate::network::compute_skims(&weights, &preprocess_data.network)?;
    info!("Running demand model");
    let bp = MetroProgressBar::new(crate::population::nb_agents());
    let mut pre_day_agent_results = PreDayAgentResults::from_agent_results(
        crate::population::agents()
            .par_iter()
            .panic_fuse()
            .map_init(EAAllocation::default, |alloc, agent| {
                bp.inc();
                agent.make_pre_day_choice(
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
    if let Some(rn_weights) = weights.road_network() {
        let unique_vehicles = &preprocess_data
            .network
            .get_road_network()
            .unwrap()
            .unique_vehicles;
        pre_day_agent_results.add_expected_routes(rn_weights, unique_vehicles);
    }
    info!("Saving results");
    results::save_choices(&pre_day_agent_results)?;
    info!("Done");
    Ok(())
}

/// Returns `true` if the Simulation must be stopped.
fn stop(iteration_counter: u32, _results: &AgentResults) -> bool {
    debug_assert!(iteration_counter >= crate::parameters::init_iteration_counter());
    let nb_iterations = 1 + iteration_counter - crate::parameters::init_iteration_counter();
    nb_iterations >= crate::parameters::max_iterations()
}

/// Additional input data for the simulation which is computed before running the simulation.
#[derive(Clone, Debug, Default)]
pub struct PreprocessingData {
    /// Network-specific pre-processing data.
    pub network: NetworkPreprocessingData,
}

/// Output of an iteration run.
#[derive(Clone, Debug)]
pub struct IterationOutput {
    /// Detailed results of the iteration.
    pub iteration_results: IterationResults,
    /// Aggregate results of the iteration.
    pub(crate) aggregate_results: AggregateResults,
    /// If `true`, the simulation should be stop (one stopping criterion was activated).
    pub(crate) stop_simulation: bool,
    /// The running times of the iteration.
    pub(crate) running_times: IterationRunningTimes,
}

fn record_time<Res>(func: impl FnOnce() -> Result<Res>) -> Result<(Res, Duration)> {
    let now = Instant::now();
    let result = func()?;
    Ok((result, now.elapsed()))
}
