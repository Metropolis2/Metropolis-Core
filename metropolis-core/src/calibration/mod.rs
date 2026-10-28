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

//! Road-capacity calibration: bottleneck capacities are calibrated by edge category so that the
//! queueing delays of target routes match observed delays.
mod optimizer;
mod output;
pub mod parameters;
mod surrogate;

use std::time::{Duration, Instant};

use anyhow::{anyhow, bail, Context, Result};
use log::{info, warn};
use num_traits::ConstZero;
use petgraph::graph::EdgeIndex;

use self::parameters::{
    Capacities, CapacityCalibrationParameters, CategoryCapacity, IdValue, OptimizerParameters,
};
use self::surrogate::{MeanSurrogate, RecordingGrid, Surrogate};
use crate::hash::{HashMap, HashSet};
use crate::mode::trip::results::LegTypeResults;
use crate::mode::trip::DepartureTimeModel;
use crate::mode::{Mode, ModeResults};
use crate::network::road_network::arrival_curve::ArrivalCurves;
use crate::network::road_network::node_order::NodeOrderCache;
use crate::network::road_network::vehicle::Vehicle;
use crate::network::road_network::{BottleneckFlows, OriginalEdgeId, RoadEdge, RoadNetworkState};
use crate::network::{NetworkState, NetworkWeights};
use crate::population::Agent;
use crate::simulation::results::AgentResults;
use crate::simulation::{check_ids_exist, format_ids, PreprocessingData};
use crate::units::*;

/// Runs the road-capacity calibration.
pub fn run() -> Result<()> {
    crate::simulation::init_thread_pool();
    crate::simulation::check_validity()?;
    let params = crate::parameters::capacity_calibration()
        .expect("The capacity-calibration parameters are not set");
    let path = crate::parameters::input_files()
        .target_routes
        .as_ref()
        .expect("The target-routes file is not set");
    let target_routes = crate::io::read_target_routes(path)?;
    let results = calibrate(params, target_routes)?;
    info!("Saving the results of the capacity calibration");
    output::save(&results)?;
    info!("Capacity calibration done");
    Ok(())
}

/// Calibrates the capacity of the edge categories, so that the queueing delays of the target
/// routes reproduce their target delays.
///
/// Returns the calibrated capacity of each category, with the id of the category (`None` for the
/// single category used when no edge has a category), and the diagnostics of the calibration.
///
/// The input of the simulation (parameters, population and network) must be initialized.
///
/// The calibration runs the day-to-day model (pre-day model, within-day model and learning, with
/// the iteration counter increasing from `init_iteration_counter`). The first `warmup_days` days
/// are simulated with the initial capacities and are not used otherwise. After each following day:
///
/// - the surrogate model of the day (its arrival curves at the edges of the target routes) joins
///   those of the previous days, up to `surrogate_days` days;
/// - the day is scored by the fit of the mean delays predicted by these surrogate models at the
///   capacities of the day (RMSE of the delays);
/// - the capacities are optimized on these surrogate models, within a trust region equal to
///   `optimizer.trust_region_scale` times the weight of the day in the expected network conditions
///   of the next day, so that the capacities move only as fast as the expected network conditions
///   (and so the routes) can follow;
/// - the next day is simulated with the optimized capacities.
///
/// The calibration stops after `stopping.max_days` days, or when the mean capacities of the last
/// `stopping.window` days differ by at most `stopping.tolerance` from those of the `window` days
/// before (see [stable_capacities]). The calibrated capacities are the mean capacities of the last
/// `window` days (after the warm-up days).
///
/// The capacities are also optimized after the last day, and the results include them with the
/// expected network conditions of the next day: a new calibration started from them (as initial
/// capacities and road-network conditions), with the next iteration counter and no warm-up day,
/// continues this one (only the surrogate models of the previous days are lost).
///
/// With spillback, the surrogate models also hold fixed the times at which the vehicles waiting for
/// space were released, which depend on the capacities further on: the optimization of a day does
/// not see how a capacity changes the spillback upstream of it, but the next days do.
pub fn calibrate(
    params: &CapacityCalibrationParameters,
    target_routes: Vec<TargetRoute>,
) -> Result<CalibrationResults> {
    check_population(crate::population::agents())?;
    let edges: Vec<_> = crate::network::road_network::iter_edges().collect();
    let categories = EdgeCategories::new(&edges, &params.capacities)?;
    check_loop_parameters(params)?;
    check_bottleneck_model(
        &edges,
        crate::network::road_network::parameters::constrain_inflow(),
    )?;
    let vehicle = calibration_vehicle(
        crate::network::road_network::vehicles(),
        params.vehicle_type.as_ref(),
    )?;
    check_target_routes(&target_routes)?;
    info!(
        "Capacity calibration with {} target routes and vehicle type `{}`",
        target_routes.len(),
        vehicle.id
    );
    categories.log_summary();
    let paths: Vec<Vec<EdgeIndex>> = target_routes
        .iter()
        .map(|r| {
            r.path
                .iter()
                .map(|&e| crate::network::road_network::edge_index_of(e))
                .collect()
        })
        .collect();
    let recorded_edges: HashSet<EdgeIndex> = paths.iter().flatten().copied().collect();
    let nb_infinite = recorded_edges
        .iter()
        .filter(|&&e| {
            categories.category_of(e).is_none() && !edges[e.index()].has_bottleneck_flow()
        })
        .count();
    if nb_infinite > 0 {
        if crate::network::road_network::parameters::spillback() {
            info!(
                "{nb_infinite} edges of the target routes have an infinite bottleneck flow (the \
                vehicles only wait for space there)"
            );
        } else {
            info!(
                "{nb_infinite} edges of the target routes have an infinite bottleneck flow (no \
                arrival curve is recorded)"
            );
        }
    }
    let mut crossed = vec![false; categories.ids.len()];
    for &e in recorded_edges.iter() {
        if let Some(cat) = categories.category_of(e) {
            crossed[cat] = true;
        }
    }
    let uncrossed: Vec<_> = (0..crossed.len())
        .filter(|&j| !crossed[j])
        .map(|j| categories.name(j))
        .collect();
    if !uncrossed.is_empty() {
        warn!(
            "{} categories are crossed by no target route: their capacity is not calibrated (it \
            keeps its initial value): {}",
            uncrossed.len(),
            uncrossed.join(", ")
        );
    }
    let target_delays: Vec<_> = target_routes.iter().map(|r| r.target_delay).collect();
    let new_surrogate = |curves| {
        Surrogate::new(
            curves,
            &edges,
            &categories,
            vehicle,
            target_routes
                .iter()
                .zip(paths.iter())
                .map(|(r, path)| (r.departure_time, path.clone())),
            RecordingGrid::new(
                crate::parameters::period(),
                crate::network::road_network::parameters::recording_interval(),
            ),
        )
    };
    let (preprocess_data, mut exp_weights, mut node_orders) = crate::simulation::prepare()?;
    let simulator = Simulator {
        edges: &edges,
        categories: &categories,
        preprocess_data: &preprocess_data,
        recorded_edges: &recorded_edges,
    };
    let surrogate_days = params.surrogate_days as usize;
    let window = params.stopping.window as usize;
    let warmup_days = params.warmup_days as usize;
    let mut capacities = categories.initial_capacities.clone();
    // Surrogate models of the last `surrogate_days` simulated days.
    let mut surrogate: Option<MeanSurrogate> = None;
    // Predicted delays of the first day, at the initial capacities.
    let mut initial_predicted_delays = None;
    let mut days = Vec::new();
    let mut previous_results: Option<AgentResults> = None;
    let mut stop_reason = "maximum number of days";
    for day in 1..=params.stopping.max_days {
        info!("===== Day {day} =====");
        let mut stop = false;
        // Iteration counter of the learning model, increasing from `init_iteration_counter`.
        let iteration_counter = crate::parameters::init_iteration_counter() + (day - 1) as u32;
        let SimulatedDay {
            results,
            curves,
            weights,
        } = simulator.day(
            &exp_weights,
            previous_results.as_ref(),
            iteration_counter,
            &capacities,
            &mut node_orders,
        )?;
        let conditions_rmse = weights
            .road_network()
            .expect("The calibration requires a road network")
            .rmse(exp_weights.road_network().unwrap());
        let travel_time_gap = relative_travel_time_gap(&results);
        info!(
            "Day {day} (iteration counter {iteration_counter}): RMSE between the expected and \
            simulated network conditions {:.3} s, relative gap between the expected and simulated \
            travel times of the road trips {}",
            f64::from(conditions_rmse),
            travel_time_gap.map_or_else(|| "-".to_owned(), |g| format!("{:.3}%", 100. * g)),
        );
        let learning_weight = crate::simulation::day_to_day_weight(iteration_counter);
        if day <= params.warmup_days {
            // Warm-up day: its routes are still far from the equilibrium (e.g., from free-flow
            // conditions, the first day takes the free-flow routes), so it does not join the
            // surrogate models.
            info!("Day {day}: warm-up day, the capacities are not optimized");
            days.push(DayResults {
                day,
                iteration_counter,
                conditions_rmse,
                travel_time_gap,
                learning_weight,
                trust_region: 0.,
                nb_surrogate_days: 0,
                score: None,
                score_noise: None,
                capacities: capacities.clone(),
            });
        } else {
            let day_surrogate = new_surrogate(curves);
            if let Some(surrogate) = surrogate.as_mut() {
                surrogate.push(day_surrogate, surrogate_days);
            } else {
                surrogate = Some(MeanSurrogate::new(day_surrogate));
            }
            let surrogate = surrogate.as_mut().unwrap();
            // The day is scored by the fit of the mean predicted delays of the last days, at the
            // capacities of the day.
            let nb_surrogate_days = surrogate.len();
            let start = Instant::now();
            let day_delays = surrogate.predict_days(&capacities);
            let predicted_delays = mean_delays(&day_delays);
            let score = log_fit(
                &format!(
                    "Day {day}: mean of the surrogate models of the last {nb_surrogate_days} days"
                ),
                &target_delays,
                &predicted_delays,
                start.elapsed(),
            );
            let score_noise = noise_of_mean(&day_delays).map(NonNegativeSeconds::new_unchecked);
            drop(day_delays);
            if let Some(noise) = score_noise {
                info!(
                    "Day {day}: noise of the mean predicted delays {:.3} s",
                    f64::from(noise)
                );
            }
            if initial_predicted_delays.is_none() {
                let start = Instant::now();
                let (predicted_delays, jacobian) = surrogate.predict_with_jacobian(&capacities);
                log_sensitivity(
                    &categories,
                    &target_delays,
                    &predicted_delays,
                    &jacobian,
                    start.elapsed(),
                );
                initial_predicted_delays = Some(predicted_delays);
            }
            let trust_region = params.optimizer.trust_region_scale * learning_weight;
            days.push(DayResults {
                day,
                iteration_counter,
                conditions_rmse,
                travel_time_gap,
                learning_weight,
                trust_region,
                nb_surrogate_days: nb_surrogate_days as u64,
                score: Some(score),
                score_noise,
                capacities: capacities.clone(),
            });
            // The warm-up days are not part of the stability test.
            let history: Vec<&[FlowPerLane]> = days[warmup_days..]
                .iter()
                .map(|d| d.capacities.as_slice())
                .collect();
            if stable_capacities(&history, window, params.stopping.tolerance) {
                stop_reason = "stable capacities";
                stop = true;
            }
            // The capacities are also optimized after the last day, so that the calibration can be
            // resumed from its output (see [CalibrationResults::next_capacities]).
            let optimized = optimizer::optimize_capacities(
                surrogate,
                &target_delays,
                &capacities,
                trust_region,
                &params.optimizer,
                &categories,
            );
            info!(
                "Day {day}: trust region {:.2}% (weight of the day in the expected network \
            conditions {:.2}%), maximum change of the capacities {:.2}%",
                100. * trust_region,
                100. * learning_weight,
                100. * max_relative_change(&capacities, &optimized),
            );
            capacities = optimized;
        }
        let new_exp_weights =
            crate::simulation::run_day_to_day_model(&exp_weights, &weights, iteration_counter);
        crate::simulation::record_weights_drift(&mut node_orders, &exp_weights, &new_exp_weights);
        exp_weights = new_exp_weights;
        previous_results = Some(results);
        if stop {
            break;
        }
    }
    let next_capacities = capacities;
    let nb_days = days.len();
    // The warm-up days are not averaged (there is at least one day after them).
    let nb_averaged = window.min(nb_days - warmup_days);
    let history: Vec<&[FlowPerLane]> = days.iter().map(|d| d.capacities.as_slice()).collect();
    let capacities = mean_capacities(&history[nb_days - nb_averaged..]);
    info!(
        "Capacity calibration stopped ({stop_reason}) after {nb_days} days ({warmup_days} warm-up \
        days); calibrated capacities: mean of the capacities of the last {nb_averaged} days"
    );
    for (j, (&capacity, &initial)) in capacities
        .iter()
        .zip(categories.initial_capacities.iter())
        .enumerate()
    {
        info!(
            "Category {}: calibrated capacity of {:.5} PCE/s per lane ({:.0} PCE/h per lane), \
            {:+.2}% from the initial capacity",
            categories.name(j),
            f64::from(capacity),
            3600. * f64::from(capacity),
            100. * (f64::from(capacity) / f64::from(initial) - 1.),
        );
    }
    let surrogate = surrogate.as_mut().expect("At least one day is simulated");
    let start = Instant::now();
    let predicted_delays = mean_delays(&surrogate.predict_days(&capacities));
    log_fit(
        &format!(
            "Mean of the surrogate models of the last {} days at the calibrated capacities",
            surrogate.len()
        ),
        &target_delays,
        &predicted_delays,
        start.elapsed(),
    );
    let delays = target_routes
        .iter()
        .zip(initial_predicted_delays.unwrap())
        .zip(predicted_delays)
        .map(
            |((route, initial_predicted_delay), predicted_delay)| TargetDelay {
                id: route.id,
                departure_time: route.departure_time,
                target_delay: route.target_delay,
                initial_predicted_delay,
                predicted_delay,
            },
        )
        .collect();
    Ok(CalibrationResults {
        capacities: categories.ids.iter().copied().zip(capacities).collect(),
        next_capacities: categories
            .ids
            .iter()
            .copied()
            .zip(next_capacities)
            .collect(),
        next_exp_weights: exp_weights,
        days,
        delays,
        category_ids: categories.ids.clone(),
    })
}

/// Results of the capacity calibration.
#[derive(Clone, Debug)]
pub struct CalibrationResults {
    /// Calibrated capacity of each category, with the id of the category (`None` for the single
    /// category used when no edge has a category).
    pub capacities: Vec<(Option<MetroId>, FlowPerLane)>,
    /// Capacity of each category optimized after the last day, i.e., the capacities of the next
    /// day if the calibration were continued (same format as `capacities`).
    pub next_capacities: Vec<(Option<MetroId>, FlowPerLane)>,
    /// Expected network conditions of the next day (learned from the last day).
    next_exp_weights: NetworkWeights,
    /// Diagnostics of each simulated day.
    days: Vec<DayResults>,
    /// Target and predicted delay of each target route.
    delays: Vec<TargetDelay>,
    /// Id of each category (`None` for the single category used when no edge has a category).
    category_ids: Vec<Option<MetroId>>,
}

/// Diagnostics of a simulated day of the capacity calibration.
#[derive(Clone, Debug)]
struct DayResults {
    /// Index of the day (starting at 1).
    day: u64,
    /// Iteration counter of the learning model at the day.
    iteration_counter: u32,
    /// RMSE between the expected and simulated network conditions of the day.
    conditions_rmse: NonNegativeSeconds,
    /// Relative gap between the expected and simulated travel times of the road trips of the day
    /// (see [relative_travel_time_gap]).
    travel_time_gap: Option<f64>,
    /// Weight of the day in the expected network conditions of the next day.
    learning_weight: f64,
    /// Trust region of the optimization after the day (maximum relative change of the
    /// capacities, 0 on a warm-up day).
    trust_region: f64,
    /// Number of days whose surrogate models are averaged (the day and the previous ones, 0 on a
    /// warm-up day).
    nb_surrogate_days: u64,
    /// Score of the day: fit of the mean delays predicted by the surrogate models of the last days
    /// (RMSE of the delays), at the capacities of the day (`None` on a warm-up day).
    score: Option<NonNegativeSeconds>,
    /// Noise of the mean predicted delays of the last days (`None` on a warm-up day or with a
    /// single day, see [noise_of_mean]).
    score_noise: Option<NonNegativeSeconds>,
    /// Capacity of each category during the day.
    capacities: Vec<FlowPerLane>,
}

/// Target and predicted delays of a target route.
#[derive(Clone, Debug)]
struct TargetDelay {
    /// Id of the target route.
    id: MetroId,
    /// Departure time from the first edge of the path.
    departure_time: NonNegativeSeconds,
    /// Observed delay of the route.
    target_delay: NonNegativeSeconds,
    /// Delay predicted on the first day, at the initial capacities.
    initial_predicted_delay: NonNegativeSeconds,
    /// Mean delay predicted by the surrogate models of the last days, at the calibrated
    /// capacities.
    predicted_delay: NonNegativeSeconds,
}

/// Returns the largest relative change from `old` to `new` capacities.
fn max_relative_change(old: &[FlowPerLane], new: &[FlowPerLane]) -> f64 {
    old.iter()
        .zip(new)
        .map(|(&o, &n)| (f64::from(n) / f64::from(o) - 1.).abs())
        .fold(0., f64::max)
}

/// Returns the mean capacity of each category over the given days (capacities of each day).
fn mean_capacities(capacities: &[&[FlowPerLane]]) -> Vec<FlowPerLane> {
    let nb_days = capacities.len() as f64;
    let nb_categories = capacities.first().map_or(0, |c| c.len());
    (0..nb_categories)
        .map(|j| {
            let sum: f64 = capacities.iter().map(|c| f64::from(c[j])).sum();
            FlowPerLane::new_unchecked(sum / nb_days)
        })
        .collect()
}

/// Returns `true` if the capacities are stable, given the capacities of each simulated day: the
/// mean capacities of the last `window` days differ by at most `tolerance` (relative) from the
/// mean capacities of the `window` days before, for all the categories.
///
/// Returns `false` without tolerance or with less than `2·window` days.
fn stable_capacities(capacities: &[&[FlowPerLane]], window: usize, tolerance: Option<f64>) -> bool {
    let Some(tolerance) = tolerance else {
        return false;
    };
    let nb_days = capacities.len();
    if window == 0 || nb_days < 2 * window {
        return false;
    }
    let previous = mean_capacities(&capacities[nb_days - 2 * window..nb_days - window]);
    let last = mean_capacities(&capacities[nb_days - window..]);
    max_relative_change(&previous, &last) <= tolerance
}

/// Returns the noise of the mean of the delays predicted on several days (at the same capacities),
/// `√(σ̄²/K)`, where `K` is the number of days and `σ̄²` is the variance (with `K - 1` degrees of
/// freedom) of the predicted delay of a target route between the days, averaged over the target
/// routes.
///
/// Returns `None` with less than two days or without target routes.
fn noise_of_mean(day_delays: &[Vec<NonNegativeSeconds>]) -> Option<f64> {
    let nb_days = day_delays.len();
    let nb_routes = day_delays.first()?.len();
    if nb_days < 2 || nb_routes == 0 {
        return None;
    }
    let sum_variances: f64 = (0..nb_routes)
        .map(|n| {
            let delays = day_delays.iter().map(|d| f64::from(d[n]));
            let mean = delays.clone().sum::<f64>() / nb_days as f64;
            delays.map(|d| (d - mean).powi(2)).sum::<f64>() / (nb_days - 1) as f64
        })
        .sum();
    let mean_variance = sum_variances / nb_routes as f64;
    Some((mean_variance / nb_days as f64).sqrt())
}

/// Returns the mean of the delays predicted on several days, for each target route.
fn mean_delays(day_delays: &[Vec<NonNegativeSeconds>]) -> Vec<NonNegativeSeconds> {
    let nb_days = day_delays.len() as f64;
    let nb_routes = day_delays.first().map_or(0, |d| d.len());
    (0..nb_routes)
        .map(|n| {
            let sum: f64 = day_delays.iter().map(|d| f64::from(d[n])).sum();
            NonNegativeSeconds::new_unchecked(sum / nb_days)
        })
        .collect()
}

/// Returns the relative gap between the expected and simulated travel times of the road legs of a
/// simulated day: the sum over the legs of the absolute difference between the expected and the
/// simulated travel time, divided by the sum of the simulated travel times.
///
/// Returns `None` if there is no road leg (or if all travel times are zero).
fn relative_travel_time_gap(results: &AgentResults) -> Option<f64> {
    let legs = results
        .iter()
        .filter_map(|r| match r.mode_results() {
            ModeResults::Trip(trip) => Some(trip.legs.iter()),
            ModeResults::Constant(_) => None,
        })
        .flatten()
        .filter_map(|leg| match &leg.class {
            LegTypeResults::Road(road) => Some((
                f64::from(road.exp_arrival_time) - f64::from(leg.departure_time),
                f64::from(leg.arrival_time) - f64::from(leg.departure_time),
            )),
            _ => None,
        });
    relative_gap(legs)
}

/// Returns the sum of the absolute differences between the expected and the simulated travel
/// times, divided by the sum of the simulated travel times, given `(expected, simulated)` pairs.
fn relative_gap(travel_times: impl Iterator<Item = (f64, f64)>) -> Option<f64> {
    let (sum_diff, sum_simulated) = travel_times
        .fold((0., 0.), |(diff, sim), (expected, simulated)| {
            (diff + (expected - simulated).abs(), sim + simulated)
        });
    (sum_simulated > 0.).then(|| sum_diff / sum_simulated)
}

/// Checks the parameters of the optimization of the capacities, of the surrogate models and of the
/// stopping criteria.
fn check_loop_parameters(params: &CapacityCalibrationParameters) -> Result<()> {
    check_optimizer_parameters(&params.optimizer)?;
    if params.surrogate_days == 0 {
        bail!("The parameter `surrogate_days` must be positive");
    }
    if params.stopping.max_days == 0 {
        bail!("The parameter `stopping.max_days` must be positive");
    }
    if params.stopping.window == 0 {
        bail!("The parameter `stopping.window` must be positive");
    }
    if params.warmup_days >= params.stopping.max_days {
        bail!("The parameter `warmup_days` must be smaller than `stopping.max_days`");
    }
    if params
        .stopping
        .tolerance
        .is_some_and(|t| t.is_nan() || t <= 0.)
    {
        bail!("The parameter `stopping.tolerance` must be positive");
    }
    Ok(())
}

/// Checks the parameters of the optimization of the capacities.
fn check_optimizer_parameters(optimizer: &OptimizerParameters) -> Result<()> {
    // The weight of a day in the expected network conditions is at most 1, so the trust region is
    // below 1 (the capacities stay positive).
    if optimizer.trust_region_scale <= 0. || optimizer.trust_region_scale >= 1. {
        bail!("The parameter `optimizer.trust_region_scale` must be between 0 and 1");
    }
    if optimizer.step_tolerance <= 0. {
        bail!("The parameter `optimizer.step_tolerance` must be positive");
    }
    if optimizer.max_iterations == 0 {
        bail!("The parameter `optimizer.max_iterations` must be positive");
    }
    if optimizer.penalty < 0. || !optimizer.penalty.is_finite() {
        bail!("The parameter `optimizer.penalty` must be non-negative");
    }
    Ok(())
}

/// Checks that the bottleneck model is supported by the capacity calibration, which models the
/// queues at the edge entries only.
fn check_bottleneck_model(edges: &[&RoadEdge], constrain_inflow: bool) -> Result<()> {
    if !constrain_inflow {
        bail!(
            "The capacity calibration requires the road-network parameter `constrain_inflow` to \
            be `true` (only the queues at the edge entries are modeled)"
        );
    }
    let no_overtaking: Vec<_> = edges
        .iter()
        .filter(|e| !e.overtaking_is_allowed())
        .map(|e| e.id())
        .collect();
    if !no_overtaking.is_empty() {
        warn!(
            "{} edges do not allow overtaking: a vehicle waiting to enter the next edge blocks \
            their exit, which the capacity calibration does not model: {}",
            no_overtaking.len(),
            format_ids(no_overtaking),
        );
    }
    Ok(())
}

/// Logs the fit of the predicted delays of the target routes to their target delays, with the
/// given description of the predicted delays, and the time taken to predict them.
///
/// Returns the RMSE of the delays.
fn log_fit(
    description: &str,
    target_delays: &[NonNegativeSeconds],
    predicted_delays: &[NonNegativeSeconds],
    duration: Duration,
) -> NonNegativeSeconds {
    debug_assert_eq!(target_delays.len(), predicted_delays.len());
    if target_delays.is_empty() {
        return NonNegativeSeconds::ZERO;
    }
    let n = target_delays.len() as f64;
    let errors: Vec<f64> = predicted_delays
        .iter()
        .zip(target_delays)
        .map(|(&p, &t)| f64::from(p) - f64::from(t))
        .collect();
    let rmse = optimizer::rmse(optimizer::half_sum_of_squares(&errors), errors.len());
    let mean_error = errors.iter().sum::<f64>() / n;
    let max_error = errors.iter().fold(0.0f64, |m, e| m.max(e.abs()));
    let mean_target = target_delays.iter().map(|&d| f64::from(d)).sum::<f64>() / n;
    info!(
        "{description}: RMSE of the delays {rmse:.3} s, mean error \
        (predicted - target) {mean_error:.3} s, maximum absolute error {max_error:.3} s, mean \
        target delay {mean_target:.3} s (evaluated in {:.1} ms)",
        duration.as_secs_f64() * 1e3,
    );
    NonNegativeSeconds::new_unchecked(rmse)
}

/// Logs, for each category, the number of target routes whose predicted delay depends on its
/// capacity and the change of the RMSE of the delays for a capacity 1% lower or higher, predicted
/// by the linearized delays (from the Jacobian matrix of the predicted delays at the initial
/// capacities), and the time taken by the surrogate model to compute the predicted delays and the
/// Jacobian.
fn log_sensitivity(
    categories: &EdgeCategories,
    target_delays: &[NonNegativeSeconds],
    predicted_delays: &[NonNegativeSeconds],
    jacobian: &[f64],
    duration: Duration,
) {
    let nb_categories = categories.initial_capacities.len();
    debug_assert_eq!(jacobian.len(), target_delays.len() * nb_categories);
    if target_delays.is_empty() {
        return;
    }
    let residuals: Vec<f64> = predicted_delays
        .iter()
        .zip(target_delays)
        .map(|(&p, &t)| f64::from(p) - f64::from(t))
        .collect();
    let rmse = |shifts: &mut dyn Iterator<Item = f64>| {
        let shifted: Vec<f64> = residuals.iter().zip(shifts).map(|(r, d)| r + d).collect();
        optimizer::rmse(optimizer::half_sum_of_squares(&shifted), shifted.len())
    };
    let initial_rmse = rmse(&mut std::iter::repeat(0.));
    for (j, &capacity) in categories.initial_capacities.iter().enumerate() {
        let column = || jacobian.iter().skip(j).step_by(nb_categories);
        let nb_routes = column().filter(|&&d| d != 0.).count();
        // Change of the RMSE with the linearized delays d_n + J_nj * dc.
        let change = |relative_change: f64| {
            let dc = relative_change * f64::from(capacity);
            rmse(&mut column().map(|d| d * dc)) - initial_rmse
        };
        info!(
            "Category {}: the delay of {nb_routes} target routes depends on its capacity; \
            change of the RMSE (linearized) for a 1% lower / higher capacity: {:+.3} s / {:+.3} s",
            categories.name(j),
            change(-0.01),
            change(0.01),
        );
    }
    info!(
        "Predicted delays and Jacobian evaluated in {:.1} ms",
        duration.as_secs_f64() * 1e3
    );
}

/// Results of a simulated day of the calibration.
struct SimulatedDay {
    /// Results of the agents.
    results: AgentResults,
    /// Arrival curves at the entry of the edges of the target routes.
    curves: ArrivalCurves,
    /// Simulated network conditions.
    weights: NetworkWeights,
}

/// Simulates the days of the calibration.
struct Simulator<'a> {
    /// Edges of the road network, ordered by `EdgeIndex`.
    edges: &'a [&'a RoadEdge],
    categories: &'a EdgeCategories,
    preprocess_data: &'a PreprocessingData,
    /// Edges whose arrival curves are recorded (the edges of the target routes).
    recorded_edges: &'a HashSet<EdgeIndex>,
}

impl Simulator<'_> {
    /// Simulates a day of the day-to-day model with the given capacities (by category): skims and
    /// pre-day model from the given expected network conditions (and the results of the previous
    /// day, if any), then within-day model, recording the arrival curves at the entry of the edges
    /// of the target routes.
    ///
    /// The routes taken are not recorded in the results.
    fn day(
        &self,
        exp_weights: &NetworkWeights,
        previous_results: Option<&AgentResults>,
        iteration_counter: u32,
        capacities: &[FlowPerLane],
        node_orders: &mut NodeOrderCache,
    ) -> Result<SimulatedDay> {
        info!("Computing skims");
        let skims =
            crate::network::compute_skims(exp_weights, &self.preprocess_data.network, node_orders)?;
        info!("Running demand model");
        let mut results = crate::simulation::run_pre_day_model(
            exp_weights,
            &skims,
            self.preprocess_data,
            previous_results,
            iteration_counter,
        )?;
        let mut rn_state =
            RoadNetworkState::init(&self.categories.bottleneck_flows(self.edges, capacities));
        rn_state.record_arrivals(self.recorded_edges.iter().copied());
        info!("Running supply model");
        let mut state = crate::simulation::run_within_day_model(
            &mut results,
            &skims,
            self.preprocess_data,
            NetworkState::new(Some(rn_state)),
            false,
        )?;
        let curves = state
            .get_mut_road_network()
            .expect("The road-network state is set")
            .take_arrival_curves();
        curves.log_summary();
        let weights = state.into_weights(&self.preprocess_data.network);
        Ok(SimulatedDay {
            results,
            curves,
            weights,
        })
    }
}

/// A route with an observed queueing delay, that the calibrated capacities must reproduce.
#[derive(Clone, Debug)]
pub struct TargetRoute {
    /// Id of the route.
    pub id: MetroId,
    /// Departure time from the first edge of the path.
    pub departure_time: NonNegativeSeconds,
    /// Observed delay of the route: its travel time minus its free-flow travel time.
    pub target_delay: NonNegativeSeconds,
    /// Edges of the route, in order.
    pub path: Vec<OriginalEdgeId>,
}

impl TargetRoute {
    /// Creates a new TargetRoute from deserialized values.
    pub fn from_values(
        id: MetroId,
        departure_time: Option<f64>,
        target_delay: Option<f64>,
        path: Option<Vec<OriginalEdgeId>>,
    ) -> Result<Self> {
        let departure_time = NonNegativeSeconds::try_from(
            departure_time.ok_or_else(|| anyhow!("Value `departure_time` is mandatory"))?,
        )
        .context("Value `departure_time` does not satisfy the constraints")?;
        let target_delay = NonNegativeSeconds::try_from(
            target_delay.ok_or_else(|| anyhow!("Value `target_delay` is mandatory"))?,
        )
        .context("Value `target_delay` does not satisfy the constraints")?;
        let path = path.ok_or_else(|| anyhow!("Value `path` is mandatory"))?;
        if path.is_empty() {
            bail!("Value `path` cannot be empty");
        }
        Ok(Self {
            id,
            departure_time,
            target_delay,
            path,
        })
    }
}

/// Returns an error if some agents cannot be used in the capacity calibration.
///
/// The calibration requires agents with a single alternative and, for trips with road legs, an
/// exogenous departure time and routes computed in the pre-day model.
fn check_population(agents: &[Agent]) -> Result<()> {
    let mut several_alternatives = Vec::new();
    let mut endogenous_departure_time = Vec::new();
    let mut no_pre_computed_route = Vec::new();
    for agent in agents {
        if agent.modes.len() > 1 {
            several_alternatives.push(agent.id);
            continue;
        }
        if let Some(Mode::Trip(trip)) = agent.modes.first() {
            if trip.nb_road_legs() == 0 {
                // Virtual-only trips are ignored by the calibration.
                continue;
            }
            if !matches!(trip.departure_time_model, DepartureTimeModel::Constant(_)) {
                endogenous_departure_time.push(agent.id);
            }
            if !trip.pre_compute_route {
                no_pre_computed_route.push(agent.id);
            }
        }
    }
    for (ids, msg) in [
        (several_alternatives, "agents have several alternatives"),
        (
            endogenous_departure_time,
            "agents have a departure-time model which is not `Constant`",
        ),
        (
            no_pre_computed_route,
            "agents have a trip with `pre_compute_route = false`",
        ),
    ] {
        if !ids.is_empty() {
            bail!(
                "The capacity calibration does not support these agents: {} {msg}: {}",
                ids.len(),
                format_ids(ids),
            );
        }
    }
    Ok(())
}

/// Edge categories of the capacity calibration: all the edges in a category have the same
/// capacity per lane.
#[derive(Clone, Debug)]
struct EdgeCategories {
    /// Id of each category (`None` for the single category used when no edge has a category).
    ids: Vec<Option<MetroId>>,
    /// Initial capacity of each category.
    initial_capacities: Vec<FlowPerLane>,
    /// Minimum capacity of each category (`None` if there is no minimum).
    min_capacities: Vec<Option<FlowPerLane>>,
    /// Maximum capacity of each category (`None` if there is no maximum).
    max_capacities: Vec<Option<FlowPerLane>>,
    /// Category index of each edge (`None` if the edge is not calibrated), indexed by `EdgeIndex`.
    edge_categories: Vec<Option<usize>>,
}

impl EdgeCategories {
    /// Creates the [EdgeCategories] from the edges of the road network (ordered by `EdgeIndex`)
    /// and the capacities of the parameters (initial values and bounds).
    ///
    /// If no edge has a category, all the edges form a single category.
    /// Otherwise, the edges without a category are not calibrated and keep their input bottleneck
    /// flow.
    fn new(edges: &[&RoadEdge], capacities: &Capacities) -> Result<Self> {
        let non_free_flow: Vec<_> = edges
            .iter()
            .filter(|e| !e.has_free_flow_speed())
            .map(|e| e.id())
            .collect();
        if !non_free_flow.is_empty() {
            bail!(
                "The capacity calibration requires the `FreeFlow` speed-density function on all \
                edges, but {} edges have another function: {}",
                non_free_flow.len(),
                format_ids(non_free_flow),
            );
        }
        let categories = if edges.iter().any(|e| e.category().is_some()) {
            Self::from_edge_categories(edges, capacities)?
        } else {
            let &Capacities::Uniform(capacity) = capacities else {
                bail!(
                    "The parameter `capacities` must be a single value when no edge has a \
                    category"
                );
            };
            Self::from_capacities(vec![None], vec![capacity], vec![Some(0); edges.len()])?
        };
        let nb_ignored_flows = edges
            .iter()
            .zip(categories.edge_categories.iter())
            .filter(|(e, cat)| cat.is_some() && e.has_bottleneck_flow())
            .count();
        if nb_ignored_flows > 0 {
            warn!(
                "The input bottleneck flows of {nb_ignored_flows} edges are ignored: their \
                capacity is calibrated"
            );
        }
        Ok(categories)
    }

    /// Creates the [EdgeCategories] when some edges have a category.
    fn from_edge_categories(edges: &[&RoadEdge], capacities: &Capacities) -> Result<Self> {
        let mut ids = Vec::new();
        let mut index_of: HashMap<MetroId, usize> = HashMap::default();
        let mut time_dependent = Vec::new();
        let edge_categories: Vec<_> = edges
            .iter()
            .map(|e| {
                if let Some(cat) = e.category() {
                    Some(*index_of.entry(cat).or_insert_with(|| {
                        ids.push(Some(cat));
                        ids.len() - 1
                    }))
                } else {
                    if e.has_time_dependent_flow() {
                        time_dependent.push(e.id());
                    }
                    None
                }
            })
            .collect();
        if !time_dependent.is_empty() {
            bail!(
                "The capacity calibration does not support time-dependent bottleneck flows on \
                edges without a category, but {} edges have one: {}",
                time_dependent.len(),
                format_ids(time_dependent),
            );
        }
        let capacities = match capacities {
            &Capacities::Uniform(capacity) => vec![capacity; ids.len()],
            Capacities::ByCategory(capacities) => {
                // The categories of the parameters are compared to the categories of the edges
                // through their string representation.
                let names: HashSet<String> = ids.iter().map(|id| id.unwrap().to_string()).collect();
                let keys: HashSet<String> = capacities.keys().cloned().collect();
                check_ids_exist(
                    &names,
                    &keys,
                    "The following edge categories have no value in the parameter `capacities`",
                )?;
                check_ids_exist(
                    &keys,
                    &names,
                    "The following categories of the parameter `capacities` are not the category \
                    of any edge",
                )?;
                ids.iter()
                    .map(|id| capacities[&id.unwrap().to_string()])
                    .collect()
            }
        };
        Self::from_capacities(ids, capacities, edge_categories)
    }

    /// Creates the [EdgeCategories] from the id and the capacity of each category and the
    /// category index of each edge.
    ///
    /// Returns an error if an initial capacity is not between the bounds of its category.
    fn from_capacities(
        ids: Vec<Option<MetroId>>,
        capacities: Vec<CategoryCapacity>,
        edge_categories: Vec<Option<usize>>,
    ) -> Result<Self> {
        let categories = Self {
            ids,
            initial_capacities: capacities.iter().map(|c| c.initial).collect(),
            min_capacities: capacities.iter().map(|c| c.min).collect(),
            max_capacities: capacities.iter().map(|c| c.max).collect(),
            edge_categories,
        };
        let outside: Vec<_> = capacities
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.is_within_bounds())
            .map(|(i, _)| categories.name(i))
            .collect();
        if !outside.is_empty() {
            bail!(
                "The initial capacity of {} categories is not between their minimum and maximum \
                capacities: {}",
                outside.len(),
                outside.join(", "),
            );
        }
        Ok(categories)
    }

    /// Returns the capacity per lane of each edge (`None` if the edge is not calibrated), given
    /// the capacity of each category.
    fn edge_capacities<'a>(
        &'a self,
        capacities: &'a [FlowPerLane],
    ) -> impl Iterator<Item = Option<FlowPerLane>> + 'a {
        debug_assert_eq!(capacities.len(), self.ids.len());
        self.edge_categories
            .iter()
            .map(|cat| cat.map(|i| capacities[i]))
    }

    /// Returns the category index of the given edge (`None` if the edge is not calibrated).
    fn category_of(&self, edge: EdgeIndex) -> Option<usize> {
        self.edge_categories[edge.index()]
    }

    /// Returns the bottleneck flows of the edges (ordered by `EdgeIndex`), given the capacity of
    /// each category (the edges that are not calibrated keep their input flow).
    fn bottleneck_flows(&self, edges: &[&RoadEdge], capacities: &[FlowPerLane]) -> BottleneckFlows {
        BottleneckFlows::from_capacities(edges, self.edge_capacities(capacities))
    }

    /// Returns the name of the given category, for the logs (its id, or "all edges" for the single
    /// category used when no edge has a category).
    fn name(&self, category: usize) -> String {
        self.ids[category].map_or_else(|| "all edges".to_owned(), |id| format!("`{id}`"))
    }

    /// Logs the number of edges, the initial capacity and the bounds of each category.
    fn log_summary(&self) {
        let mut nb_edges = vec![0; self.ids.len()];
        let mut nb_uncalibrated_edges = 0;
        for &cat in self.edge_categories.iter() {
            if let Some(i) = cat {
                nb_edges[i] += 1;
            } else {
                nb_uncalibrated_edges += 1;
            }
        }
        for (i, (capacity, n)) in self.initial_capacities.iter().zip(nb_edges).enumerate() {
            let bound = |name: &str, value: Option<FlowPerLane>| {
                value.map_or_else(String::new, |v| format!(", {name} {}", f64::from(v)))
            };
            info!(
                "Category {}: {n} edges, initial capacity of {} PCE/s per lane{}{}",
                self.name(i),
                f64::from(capacity),
                bound("minimum", self.min_capacities[i]),
                bound("maximum", self.max_capacities[i]),
            );
        }
        if nb_uncalibrated_edges > 0 {
            info!(
                "{nb_uncalibrated_edges} edges without a category keep their input bottleneck flow"
            );
        }
    }
}

/// Returns the vehicle type used to compute the free-flow travel times of the target routes.
///
/// The `vehicle_type` parameter is compared to the vehicle ids through their string
/// representation. It is optional if there is a single vehicle type.
fn calibration_vehicle<'a>(
    vehicles: &'a [Vehicle],
    vehicle_type: Option<&IdValue>,
) -> Result<&'a Vehicle> {
    if let Some(vehicle_type) = vehicle_type {
        let name = vehicle_type.to_string();
        vehicles
            .iter()
            .find(|v| v.id.to_string() == name)
            .ok_or_else(|| {
                anyhow!("The vehicle type `{name}` of the parameter `vehicle_type` does not exist")
            })
    } else if let [vehicle] = vehicles {
        Ok(vehicle)
    } else {
        bail!("The parameter `vehicle_type` is mandatory when there are several vehicle types")
    }
}

/// Checks that the edges of the target routes exist and warns about the target routes that depart
/// outside of the simulated period.
fn check_target_routes(target_routes: &[TargetRoute]) -> Result<()> {
    let used_edges: HashSet<OriginalEdgeId> = target_routes
        .iter()
        .flat_map(|r| r.path.iter().copied())
        .collect();
    let edges: HashSet<OriginalEdgeId> =
        crate::network::road_network::iter_original_edge_ids().collect();
    check_ids_exist(
        &used_edges,
        &edges,
        "The following edge ids are used in target routes but are not part of the road network",
    )?;
    let period = crate::parameters::period();
    let outside_period: Vec<_> = target_routes
        .iter()
        .filter(|r| !period.contains(r.departure_time))
        .map(|r| r.id)
        .collect();
    if !outside_period.is_empty() {
        warn!(
            "{} target routes have a departure time outside of the simulated period: {}",
            outside_period.len(),
            format_ids(outside_period),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use choice::ContinuousChoiceModel;
    use num_traits::{ConstOne, ConstZero};

    use super::*;
    use crate::mode::trip::{Leg, LegType, RoadLeg, TravelingMode};
    use crate::network::road_network::vehicle::SpeedFunction;
    use crate::schedule_utility::ScheduleUtility;
    use crate::travel_utility::TravelUtility;

    fn road_trip(departure_time_model: DepartureTimeModel) -> TravelingMode {
        let leg = Leg::new(
            1,
            LegType::Road(RoadLeg::new(0, 1, 1)),
            NonNegativeSeconds::ZERO,
            TravelUtility::default(),
            ScheduleUtility::None,
        );
        TravelingMode::new(
            1,
            vec![leg],
            NonNegativeSeconds::ZERO,
            departure_time_model,
            TravelUtility::default(),
            ScheduleUtility::None,
            ScheduleUtility::None,
        )
    }

    fn constant_trip() -> TravelingMode {
        road_trip(DepartureTimeModel::Constant(NonNegativeSeconds::ZERO))
    }

    fn continuous_trip() -> TravelingMode {
        road_trip(DepartureTimeModel::Continuous {
            period: None,
            choice_model: ContinuousChoiceModel::from_values(Some("Logit"), Some(0.5), Some(1.0))
                .unwrap(),
        })
    }

    #[test]
    fn check_population_test() {
        let valid_agents = vec![
            Agent::new(0, vec![Mode::Trip(constant_trip())], None),
            // Agents with a constant mode or with virtual-only trips are ignored.
            Agent::new(
                1,
                vec![Mode::Constant((MetroId::from(1i64), Utility::ZERO))],
                None,
            ),
            Agent::new(
                2,
                vec![Mode::Trip(TravelingMode::new(
                    1,
                    vec![],
                    NonNegativeSeconds::ZERO,
                    continuous_trip().departure_time_model,
                    TravelUtility::default(),
                    ScheduleUtility::None,
                    ScheduleUtility::None,
                ))],
                None,
            ),
        ];
        assert!(check_population(&valid_agents).is_ok());

        let agents = vec![Agent::new(
            0,
            vec![Mode::Trip(constant_trip()), Mode::Trip(constant_trip())],
            None,
        )];
        let msg = check_population(&agents).unwrap_err().to_string();
        assert!(
            msg.contains("1 agents have several alternatives: 0"),
            "{msg}"
        );

        let agents = vec![
            Agent::new(0, vec![Mode::Trip(constant_trip())], None),
            Agent::new(1, vec![Mode::Trip(continuous_trip())], None),
        ];
        let msg = check_population(&agents).unwrap_err().to_string();
        assert!(msg.contains("which is not `Constant`: 1"), "{msg}");

        let mut trip = constant_trip();
        trip.pre_compute_route = false;
        let agents = vec![Agent::new(0, vec![Mode::Trip(trip)], None)];
        let msg = check_population(&agents).unwrap_err().to_string();
        assert!(msg.contains("`pre_compute_route = false`: 0"), "{msg}");
    }

    /// Creates an edge with the given id, speed-density function, (per-lane) bottleneck flows and
    /// category.
    fn edge(
        id: i64,
        speed_density_type: &str,
        bottleneck_flow: Option<f64>,
        time_dependent_flows: bool,
        category: Option<&str>,
    ) -> RoadEdge {
        let (times, flows) = if time_dependent_flows {
            (Some(vec![0.0, 10.0]), Some(vec![1.0, 2.0]))
        } else {
            (None, None)
        };
        RoadEdge::from_values(
            MetroId::from(id),
            Some(1.0),
            Some(1.0),
            Some(2.0),
            Some(speed_density_type),
            Some(1.0),
            None,
            None,
            None,
            None,
            bottleneck_flow,
            flows,
            times,
            None,
            None,
            category.map(MetroId::from),
        )
        .unwrap()
    }

    fn capacity(value: f64) -> FlowPerLane {
        FlowPerLane::try_from(value).unwrap()
    }

    fn category_capacity(value: f64) -> CategoryCapacity {
        CategoryCapacity {
            initial: capacity(value),
            min: None,
            max: None,
        }
    }

    fn uniform(value: f64) -> Capacities {
        Capacities::Uniform(category_capacity(value))
    }

    fn by_category(values: &[(&str, f64)]) -> Capacities {
        Capacities::ByCategory(
            values
                .iter()
                .map(|&(name, value)| (name.to_owned(), category_capacity(value)))
                .collect(),
        )
    }

    #[test]
    fn edge_categories_test() {
        // No category: all the edges form a single category.
        let e0 = edge(0, "FreeFlow", Some(1.0), false, None);
        let e1 = edge(1, "FreeFlow", None, true, None);
        let edges = [&e0, &e1];
        let categories = EdgeCategories::new(&edges, &uniform(0.5)).unwrap();
        assert_eq!(categories.ids, vec![None]);
        assert_eq!(categories.initial_capacities, vec![capacity(0.5)]);
        assert_eq!(categories.edge_categories, vec![Some(0), Some(0)]);
        // Capacities by category are not allowed when no edge has a category.
        assert!(EdgeCategories::new(&edges, &by_category(&[("a", 0.5)])).is_err());

        // With categories (in order of first appearance); edges without a category are not
        // calibrated.
        let e0 = edge(0, "FreeFlow", Some(1.0), false, Some("b"));
        let e1 = edge(1, "FreeFlow", None, false, None);
        let e2 = edge(2, "FreeFlow", None, true, Some("a"));
        let e3 = edge(3, "FreeFlow", Some(1.0), false, Some("b"));
        let edges = [&e0, &e1, &e2, &e3];
        let categories =
            EdgeCategories::new(&edges, &by_category(&[("a", 0.5), ("b", 0.6)])).unwrap();
        assert_eq!(
            categories.ids,
            vec![Some(MetroId::from("b")), Some(MetroId::from("a"))]
        );
        assert_eq!(
            categories.initial_capacities,
            vec![capacity(0.6), capacity(0.5)]
        );
        assert_eq!(
            categories.edge_categories,
            vec![Some(0), None, Some(1), Some(0)]
        );
        let categories = EdgeCategories::new(&edges, &uniform(0.5)).unwrap();
        assert_eq!(categories.initial_capacities, vec![capacity(0.5); 2]);
        assert_eq!(categories.min_capacities, vec![None; 2]);
        assert_eq!(categories.max_capacities, vec![None; 2]);

        // Bounds by category.
        let bounded = |initial: f64, min: Option<f64>, max: Option<f64>| CategoryCapacity {
            initial: capacity(initial),
            min: min.map(capacity),
            max: max.map(capacity),
        };
        let capacities = |a: CategoryCapacity, b: CategoryCapacity| {
            Capacities::ByCategory(
                [("a".to_owned(), a), ("b".to_owned(), b)]
                    .into_iter()
                    .collect(),
            )
        };
        let categories = EdgeCategories::new(
            &edges,
            &capacities(bounded(0.5, Some(0.1), None), bounded(0.6, None, Some(0.8))),
        )
        .unwrap();
        assert_eq!(categories.min_capacities, vec![None, Some(capacity(0.1))]);
        assert_eq!(categories.max_capacities, vec![Some(capacity(0.8)), None]);
        // The initial capacities must be within the bounds.
        let msg = EdgeCategories::new(
            &edges,
            &capacities(bounded(0.5, Some(0.6), None), bounded(0.6, None, Some(0.5))),
        )
        .unwrap_err()
        .to_string();
        assert!(
            msg.ends_with(
                "2 categories is not between their minimum and maximum capacities: `b`, `a`"
            ),
            "{msg}"
        );

        // Missing or extra category in the parameters.
        let msg = EdgeCategories::new(&edges, &by_category(&[("a", 0.5)]))
            .unwrap_err()
            .to_string();
        assert!(
            msg.ends_with("no value in the parameter `capacities`: b"),
            "{msg}"
        );
        let msg = EdgeCategories::new(&edges, &by_category(&[("a", 0.5), ("b", 0.6), ("c", 0.7)]))
            .unwrap_err()
            .to_string();
        assert!(msg.ends_with("not the category of any edge: c"), "{msg}");

        // Time-dependent flows are not allowed on the edges without a category.
        let e1 = edge(1, "FreeFlow", None, true, None);
        let edges = [&e0, &e1];
        let msg = EdgeCategories::new(&edges, &uniform(0.5))
            .unwrap_err()
            .to_string();
        assert!(msg.contains("1 edges have one: 1"), "{msg}");

        // All the edges must have a `FreeFlow` speed-density function.
        let e1 = edge(1, "Bottleneck", None, false, Some("b"));
        let edges = [&e0, &e1];
        let msg = EdgeCategories::new(&edges, &uniform(0.5))
            .unwrap_err()
            .to_string();
        assert!(msg.contains("1 edges have another function: 1"), "{msg}");
    }

    #[test]
    fn edge_capacities_test() {
        // Single category.
        let e0 = edge(0, "FreeFlow", Some(1.0), false, None);
        let e1 = edge(1, "FreeFlow", None, false, None);
        let edges = [&e0, &e1];
        let categories = EdgeCategories::new(&edges, &uniform(0.5)).unwrap();
        let capacities: Vec<_> = categories.edge_capacities(&[capacity(0.3)]).collect();
        assert_eq!(capacities, vec![Some(capacity(0.3)); 2]);

        // With categories: the edges without a category are not calibrated.
        let e0 = edge(0, "FreeFlow", Some(1.0), false, Some("b"));
        let e1 = edge(1, "FreeFlow", Some(1.0), false, None);
        let e2 = edge(2, "FreeFlow", None, false, Some("a"));
        let edges = [&e0, &e1, &e2];
        let categories = EdgeCategories::new(&edges, &uniform(0.5)).unwrap();
        let capacities: Vec<_> = categories
            .edge_capacities(&[capacity(0.3), capacity(0.4)])
            .collect();
        assert_eq!(
            capacities,
            vec![Some(capacity(0.3)), None, Some(capacity(0.4))]
        );
    }

    #[test]
    fn check_optimizer_parameters_test() {
        assert!(check_optimizer_parameters(&OptimizerParameters::default()).is_ok());
        for (optimizer, name) in [
            (r#"{"trust_region_scale": 0.0}"#, "trust_region_scale"),
            (r#"{"trust_region_scale": 1.0}"#, "trust_region_scale"),
            (r#"{"step_tolerance": 0.0}"#, "step_tolerance"),
            (r#"{"max_iterations": 0}"#, "max_iterations"),
            (r#"{"penalty": -0.01}"#, "penalty"),
        ] {
            let msg = check_optimizer_parameters(&serde_json::from_str(optimizer).unwrap())
                .unwrap_err()
                .to_string();
            assert!(msg.contains(&format!("`optimizer.{name}`")), "{msg}");
        }
    }

    #[test]
    fn check_loop_parameters_test() {
        let parse = |json: &str| -> CapacityCalibrationParameters {
            serde_json::from_str(&format!(r#"{{"capacities": 0.5, {json}}}"#)).unwrap()
        };
        assert!(check_loop_parameters(&parse(r#""vehicle_type": 1"#)).is_ok());
        for (json, name) in [
            (
                r#""optimizer": {"trust_region_scale": 0.0}"#,
                "optimizer.trust_region_scale",
            ),
            (r#""surrogate_days": 0"#, "surrogate_days"),
            (r#""stopping": {"max_days": 0}"#, "stopping.max_days"),
            (r#""stopping": {"window": 0}"#, "stopping.window"),
            (
                r#""warmup_days": 3, "stopping": {"max_days": 3}"#,
                "warmup_days",
            ),
            (r#""stopping": {"tolerance": 0.0}"#, "stopping.tolerance"),
        ] {
            let msg = check_loop_parameters(&parse(json)).unwrap_err().to_string();
            assert!(msg.contains(&format!("`{name}`")), "{msg}");
        }
    }

    #[test]
    fn stable_capacities_test() {
        let days = |values: &[[f64; 2]]| -> Vec<Vec<FlowPerLane>> {
            values.iter().map(|c| c.map(capacity).to_vec()).collect()
        };
        let history = days(&[[1.0, 2.0], [1.2, 2.0], [1.0, 2.2], [1.0, 2.2]]);
        let history: Vec<&[FlowPerLane]> = history.iter().map(|c| c.as_slice()).collect();
        // Mean of the capacities of each category.
        assert_eq!(
            mean_capacities(&history[1..]),
            vec![capacity(3.2 / 3.), capacity(6.4 / 3.)]
        );
        // Windows of 2 days: (1.1, 2.0), then (1.0, 2.2), a change of 10%.
        assert!(stable_capacities(&history, 2, Some(0.1 + 1e-9)));
        assert!(!stable_capacities(&history, 2, Some(0.09)));
        // Without tolerance or with less than two windows of days: not stable.
        assert!(!stable_capacities(&history, 2, None));
        assert!(!stable_capacities(&history[1..], 2, Some(1.)));
        // Windows of 1 day: the last two days are equal.
        assert!(stable_capacities(&history, 1, Some(1e-12)));
    }

    #[test]
    fn noise_of_mean_test() {
        let delays = |values: &[&[f64]]| -> Vec<Vec<NonNegativeSeconds>> {
            values
                .iter()
                .map(|day| {
                    day.iter()
                        .map(|&d| NonNegativeSeconds::try_from(d).unwrap())
                        .collect()
                })
                .collect()
        };
        assert_eq!(noise_of_mean(&[]), None);
        assert_eq!(noise_of_mean(&delays(&[&[1., 2.]])), None);
        assert_eq!(noise_of_mean(&delays(&[&[], &[]])), None);
        assert_eq!(noise_of_mean(&delays(&[&[1., 2.], &[1., 2.]])), Some(0.));
        // Route 0: 1, 3 and 5 (variance 4); route 1: 2, 2 and 8 (variance 12); mean variance 8,
        // divided by 3 days.
        let noise = noise_of_mean(&delays(&[&[1., 2.], &[3., 2.], &[5., 8.]])).unwrap();
        assert!((noise - (8f64 / 3.).sqrt()).abs() < 1e-12, "{noise}");
        let mean = mean_delays(&delays(&[&[1., 2.], &[3., 2.], &[5., 8.]]));
        assert_eq!(mean, delays(&[&[3., 4.]])[0]);
    }

    #[test]
    fn relative_gap_test() {
        assert_eq!(relative_gap(std::iter::empty()), None);
        assert_eq!(relative_gap([(10., 0.)].into_iter()), None);
        assert_eq!(relative_gap([(10., 10.), (20., 20.)].into_iter()), Some(0.));
        // |12 - 10| + |15 - 20| = 7, divided by 10 + 20.
        let gap = relative_gap([(12., 10.), (15., 20.)].into_iter()).unwrap();
        assert!((gap - 7. / 30.).abs() < 1e-12, "{gap}");
    }

    #[test]
    fn max_relative_change_test() {
        let c =
            |values: &[f64]| -> Vec<FlowPerLane> { values.iter().map(|&v| capacity(v)).collect() };
        assert_eq!(max_relative_change(&c(&[0.5, 0.2]), &c(&[0.5, 0.2])), 0.);
        let change = max_relative_change(&c(&[0.5, 0.2]), &c(&[0.45, 0.21]));
        assert!((change - 0.1).abs() < 1e-12, "{change}");
    }

    #[test]
    fn check_bottleneck_model_test() {
        let e0 = edge(0, "FreeFlow", Some(1.0), false, None);
        assert!(check_bottleneck_model(&[&e0], true).is_ok());
        let msg = check_bottleneck_model(&[&e0], false)
            .unwrap_err()
            .to_string();
        assert!(msg.contains("`constrain_inflow`"), "{msg}");
    }

    fn vehicle(id: i64) -> Vehicle {
        Vehicle::new(
            id,
            NonNegativeMeters::ZERO,
            PCE::ONE,
            SpeedFunction::Base,
            HashSet::default(),
            HashSet::default(),
        )
    }

    #[test]
    fn calibration_vehicle_test() {
        let vehicles = [vehicle(1)];
        assert_eq!(
            calibration_vehicle(&vehicles, None).unwrap().id,
            MetroId::from(1i64)
        );
        let vehicles = [vehicle(1), vehicle(2)];
        assert!(calibration_vehicle(&vehicles, None).is_err());
        let vehicle_type = IdValue::Integer(2);
        assert_eq!(
            calibration_vehicle(&vehicles, Some(&vehicle_type))
                .unwrap()
                .id,
            MetroId::from(2i64)
        );
        let vehicle_type = IdValue::String("2".to_owned());
        assert_eq!(
            calibration_vehicle(&vehicles, Some(&vehicle_type))
                .unwrap()
                .id,
            MetroId::from(2i64)
        );
        let vehicle_type = IdValue::Integer(3);
        assert!(calibration_vehicle(&vehicles, Some(&vehicle_type)).is_err());
    }
}
