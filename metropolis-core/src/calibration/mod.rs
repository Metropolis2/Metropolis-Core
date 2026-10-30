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

//! Road-capacity calibration: the bottleneck capacities of the edges are the product of a fixed
//! capacity and of calibrated factors, so that the queueing delays of target routes match observed
//! delays.
mod optimizer;
mod output;
pub mod parameters;
mod surrogate;

use std::time::{Duration, Instant};

use anyhow::{anyhow, bail, Context, Result};
use log::{info, warn};
use num_traits::ConstZero;
use petgraph::graph::EdgeIndex;

use self::parameters::{CapacityCalibrationParameters, Factor, IdValue, OptimizerParameters};
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
    let path = crate::parameters::input_files()
        .capacity_factors
        .as_ref()
        .expect("The capacity-factors file is not set");
    let edge_factors = crate::io::read_capacity_factors(path)?;
    let results = calibrate(params, target_routes, &edge_factors)?;
    info!("Saving the results of the capacity calibration");
    output::save(&results)?;
    info!("Capacity calibration done");
    Ok(())
}

/// Calibrates the capacity factors, so that the queueing delays of the target routes reproduce
/// their target delays.
///
/// The capacity per lane of an edge with factors (`edge_factors`) is the parameter `capacity` times
/// the product of the values of its factors; the edges without a factor keep their input
/// bottleneck flow. Returns the calibrated value of each factor, the resulting capacities of the
/// edges, and the diagnostics of the calibration.
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
/// - the factors are optimized on these surrogate models, within a trust region equal to
///   `optimizer.trust_region_scale` times the weight of the day in the expected network conditions
///   of the next day, so that the capacities move only as fast as the expected network conditions
///   (and so the routes) can follow;
/// - the next day is simulated with the optimized capacities.
///
/// The calibration stops after `stopping.max_days` days, or when the mean factors of the last
/// `stopping.window` days differ by at most `stopping.tolerance` from those of the `window` days
/// before (see [stable_factors]). The calibrated factors are the mean factors of the last `window`
/// days (after the warm-up days).
///
/// The factors are also optimized after the last day, and the results include them with the
/// expected network conditions of the next day: a new calibration started from them (as initial
/// factors and road-network conditions), with the next iteration counter and no warm-up day,
/// continues this one (only the surrogate models of the previous days are lost).
///
/// With spillback, the surrogate models also hold fixed the times at which the vehicles waiting for
/// space were released, which depend on the capacities further on: the optimization of a day does
/// not see how a capacity changes the spillback upstream of it, but the next days do.
pub fn calibrate(
    params: &CapacityCalibrationParameters,
    target_routes: Vec<TargetRoute>,
    edge_factors: &[EdgeFactor],
) -> Result<CalibrationResults> {
    check_population(crate::population::agents())?;
    let edges: Vec<_> = crate::network::road_network::iter_edges().collect();
    let factors = CapacityFactors::new(&edges, params.capacity, &params.factors, edge_factors)?;
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
    factors.log_summary();
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
            factors.combination_of(e).is_none() && !edges[e.index()].has_bottleneck_flow()
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
    let mut crossed = vec![false; factors.ids.len()];
    for &e in recorded_edges.iter() {
        if let Some(c) = factors.combination_of(e) {
            factors.combinations[c]
                .iter()
                .for_each(|&j| crossed[j] = true);
        }
    }
    let uncrossed: Vec<_> = (0..crossed.len())
        .filter(|&j| !crossed[j])
        .map(|j| factors.name(j))
        .collect();
    if !uncrossed.is_empty() {
        warn!(
            "{} factors have no edge crossed by a target route: they are not calibrated (they \
            keep their initial value): {}",
            uncrossed.len(),
            uncrossed.join(", ")
        );
    }
    let target_delays: Vec<_> = target_routes.iter().map(|r| r.target_delay).collect();
    let new_surrogate = |curves| {
        Surrogate::new(
            curves,
            &edges,
            &factors,
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
        factors: &factors,
        preprocess_data: &preprocess_data,
        recorded_edges: &recorded_edges,
    };
    let surrogate_days = params.surrogate_days as usize;
    let window = params.stopping.window as usize;
    let warmup_days = params.warmup_days as usize;
    let mut values = factors.initial.clone();
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
            &values,
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
            info!("Day {day}: warm-up day, the factors are not optimized");
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
                factors: values.clone(),
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
            // factors of the day.
            let nb_surrogate_days = surrogate.len();
            let start = Instant::now();
            let day_delays = surrogate.predict_days(&values);
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
                let (predicted_delays, jacobian) = surrogate.predict_with_jacobian(&values);
                log_sensitivity(
                    &factors,
                    &values,
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
                factors: values.clone(),
            });
            // The warm-up days are not part of the stability test.
            let history: Vec<&[f64]> = days[warmup_days..]
                .iter()
                .map(|d| d.factors.as_slice())
                .collect();
            if stable_factors(&history, window, params.stopping.tolerance) {
                stop_reason = "stable factors";
                stop = true;
            }
            // The factors are also optimized after the last day, so that the calibration can be
            // resumed from its output (see [CalibrationResults::next_factors]).
            let optimized = optimizer::optimize_factors(
                surrogate,
                &target_delays,
                &values,
                trust_region,
                &params.optimizer,
                &factors,
            );
            info!(
                "Day {day}: trust region {:.2}% (weight of the day in the expected network \
            conditions {:.2}%), maximum change of the factors {:.2}%",
                100. * trust_region,
                100. * learning_weight,
                100. * max_relative_change(&values, &optimized),
            );
            values = optimized;
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
    let next_values = values;
    let nb_days = days.len();
    // The warm-up days are not averaged (there is at least one day after them).
    let nb_averaged = window.min(nb_days - warmup_days);
    let history: Vec<&[f64]> = days.iter().map(|d| d.factors.as_slice()).collect();
    let values = mean_factors(&history[nb_days - nb_averaged..]);
    info!(
        "Capacity calibration stopped ({stop_reason}) after {nb_days} days ({warmup_days} warm-up \
        days); calibrated factors: mean of the factors of the last {nb_averaged} days"
    );
    for (j, (&value, &initial)) in values.iter().zip(factors.initial.iter()).enumerate() {
        info!(
            "Factor {}: calibrated value {value:.5}, {:+.2}% from the initial value",
            factors.name(j),
            100. * (value / initial - 1.),
        );
    }
    factors.log_capacity_range("Calibrated", &values);
    let surrogate = surrogate.as_mut().expect("At least one day is simulated");
    let start = Instant::now();
    let predicted_delays = mean_delays(&surrogate.predict_days(&values));
    log_fit(
        &format!(
            "Mean of the surrogate models of the last {} days at the calibrated factors",
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
    let edge_capacities = edges
        .iter()
        .zip(factors.edge_capacities(&values))
        .filter_map(|(e, c)| c.map(|c| (e.id(), c, c * e.lanes())))
        .collect();
    Ok(CalibrationResults {
        capacity: params.capacity,
        factors: factors.ids.iter().copied().zip(values).collect(),
        next_factors: factors.ids.iter().copied().zip(next_values).collect(),
        edge_capacities,
        next_exp_weights: exp_weights,
        days,
        delays,
    })
}

/// Results of the capacity calibration.
#[derive(Clone, Debug)]
pub struct CalibrationResults {
    /// Capacity per lane of an edge whose factors are all equal to 1 (parameter `capacity`).
    pub capacity: FlowPerLane,
    /// Calibrated value of each factor, with the id of the factor.
    pub factors: Vec<(MetroId, f64)>,
    /// Value of each factor optimized after the last day, i.e., the factors of the next day if the
    /// calibration were continued (same format as `factors`).
    pub next_factors: Vec<(MetroId, f64)>,
    /// Calibrated capacity per lane and bottleneck flow (over all the lanes) of each edge with
    /// factors, with the id of the edge.
    pub edge_capacities: Vec<(OriginalEdgeId, FlowPerLane, Flow)>,
    /// Expected network conditions of the next day (learned from the last day).
    next_exp_weights: NetworkWeights,
    /// Diagnostics of each simulated day.
    days: Vec<DayResults>,
    /// Target and predicted delay of each target route.
    delays: Vec<TargetDelay>,
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
    /// Trust region of the optimization after the day (maximum relative change of the factors, 0
    /// on a warm-up day).
    trust_region: f64,
    /// Number of days whose surrogate models are averaged (the day and the previous ones, 0 on a
    /// warm-up day).
    nb_surrogate_days: u64,
    /// Score of the day: fit of the mean delays predicted by the surrogate models of the last days
    /// (RMSE of the delays), at the factors of the day (`None` on a warm-up day).
    score: Option<NonNegativeSeconds>,
    /// Noise of the mean predicted delays of the last days (`None` on a warm-up day or with a
    /// single day, see [noise_of_mean]).
    score_noise: Option<NonNegativeSeconds>,
    /// Value of each factor during the day.
    factors: Vec<f64>,
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
    /// Mean delay predicted by the surrogate models of the last days, at the calibrated factors.
    predicted_delay: NonNegativeSeconds,
}

/// Returns the largest relative change from `old` to `new` factors.
fn max_relative_change(old: &[f64], new: &[f64]) -> f64 {
    old.iter()
        .zip(new)
        .map(|(&o, &n)| (n / o - 1.).abs())
        .fold(0., f64::max)
}

/// Returns the mean value of each factor over the given days (factors of each day).
fn mean_factors(factors: &[&[f64]]) -> Vec<f64> {
    let nb_days = factors.len() as f64;
    let nb_factors = factors.first().map_or(0, |f| f.len());
    (0..nb_factors)
        .map(|j| factors.iter().map(|f| f[j]).sum::<f64>() / nb_days)
        .collect()
}

/// Returns `true` if the factors are stable, given the factors of each simulated day: the mean
/// factors of the last `window` days differ by at most `tolerance` (relative) from the mean factors
/// of the `window` days before, for all the factors.
///
/// Returns `false` without tolerance or with less than `2·window` days.
fn stable_factors(factors: &[&[f64]], window: usize, tolerance: Option<f64>) -> bool {
    let Some(tolerance) = tolerance else {
        return false;
    };
    let nb_days = factors.len();
    if window == 0 || nb_days < 2 * window {
        return false;
    }
    let previous = mean_factors(&factors[nb_days - 2 * window..nb_days - window]);
    let last = mean_factors(&factors[nb_days - window..]);
    max_relative_change(&previous, &last) <= tolerance
}

/// Returns the noise of the mean of the delays predicted on several days (at the same factors),
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

/// Logs, for each factor, the number of target routes whose predicted delay depends on it and the
/// change of the RMSE of the delays for a factor 1% lower or higher, predicted by the linearized
/// delays (from the Jacobian matrix of the predicted delays at the given factors), and the time
/// taken by the surrogate model to compute the predicted delays and the Jacobian.
fn log_sensitivity(
    factors: &CapacityFactors,
    values: &[f64],
    target_delays: &[NonNegativeSeconds],
    predicted_delays: &[NonNegativeSeconds],
    jacobian: &[f64],
    duration: Duration,
) {
    let nb_factors = values.len();
    debug_assert_eq!(jacobian.len(), target_delays.len() * nb_factors);
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
    for (j, &value) in values.iter().enumerate() {
        let column = || jacobian.iter().skip(j).step_by(nb_factors);
        let nb_routes = column().filter(|&&d| d != 0.).count();
        // Change of the RMSE with the linearized delays d_n + J_nj * df.
        let change = |relative_change: f64| {
            let df = relative_change * value;
            rmse(&mut column().map(|d| d * df)) - initial_rmse
        };
        info!(
            "Factor {}: the delay of {nb_routes} target routes depends on it; change of the RMSE \
            (linearized) for a 1% lower / higher factor: {:+.3} s / {:+.3} s",
            factors.name(j),
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
    factors: &'a CapacityFactors,
    preprocess_data: &'a PreprocessingData,
    /// Edges whose arrival curves are recorded (the edges of the target routes).
    recorded_edges: &'a HashSet<EdgeIndex>,
}

impl Simulator<'_> {
    /// Simulates a day of the day-to-day model with the given factors: skims and
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
        values: &[f64],
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
            RoadNetworkState::init(&self.factors.bottleneck_flows(self.edges, values));
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

/// A factor of the capacity of an edge (a row of the input file `capacity_factors`).
#[derive(Clone, Debug)]
pub struct EdgeFactor {
    /// Id of the edge.
    pub edge_id: OriginalEdgeId,
    /// Id of the factor.
    pub factor: MetroId,
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

/// Capacity factors of the capacity calibration: the capacity per lane of an edge with factors is
/// the fixed capacity `C` times the product of the values of its factors.
///
/// The edges with the same set of factors (a combination) have the same capacity per lane.
#[derive(Clone, Debug)]
struct CapacityFactors {
    /// Capacity per lane of an edge whose factors are all equal to 1.
    capacity: FlowPerLane,
    /// Id of each factor.
    ids: Vec<MetroId>,
    /// Initial value of each factor.
    initial: Vec<f64>,
    /// Minimum value of each factor (`None` if there is no minimum).
    min: Vec<Option<f64>>,
    /// Maximum value of each factor (`None` if there is no maximum).
    max: Vec<Option<f64>>,
    /// Factor indices of each combination (in increasing order, each combination is distinct).
    combinations: Vec<Vec<usize>>,
    /// Combination index of each edge (`None` if the edge has no factor and is not calibrated),
    /// indexed by `EdgeIndex`.
    edge_combinations: Vec<Option<usize>>,
}

impl CapacityFactors {
    /// Creates the [CapacityFactors] from the edges of the road network (ordered by `EdgeIndex`),
    /// the parameters `capacity` and `factors` (initial values and bounds by factor id, 1 without
    /// bounds for the factors that are not given) and the factors of the edges.
    ///
    /// The edges without a factor are not calibrated and keep their input bottleneck flow.
    fn new(
        edges: &[&RoadEdge],
        capacity: FlowPerLane,
        params: &HashMap<String, Factor>,
        edge_factors: &[EdgeFactor],
    ) -> Result<Self> {
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
        if edge_factors.is_empty() {
            bail!("The capacity calibration requires at least one capacity factor");
        }
        let edge_index: HashMap<OriginalEdgeId, usize> =
            edges.iter().enumerate().map(|(i, e)| (e.id(), i)).collect();
        let used_edges: HashSet<OriginalEdgeId> = edge_factors.iter().map(|f| f.edge_id).collect();
        check_ids_exist(
            &used_edges,
            &edge_index.keys().copied().collect(),
            "The following edge ids have capacity factors but are not part of the road network",
        )?;
        // Factors in order of first appearance, and factor indices of each edge.
        let mut ids = Vec::new();
        let mut index_of: HashMap<MetroId, usize> = HashMap::default();
        let mut factors_of_edge: Vec<Vec<usize>> = vec![Vec::new(); edges.len()];
        let mut duplicates = Vec::new();
        for f in edge_factors {
            let j = *index_of.entry(f.factor).or_insert_with(|| {
                ids.push(f.factor);
                ids.len() - 1
            });
            let factors = &mut factors_of_edge[edge_index[&f.edge_id]];
            if factors.contains(&j) {
                duplicates.push(format!("({}, {})", f.edge_id, f.factor));
            } else {
                factors.push(j);
            }
        }
        if !duplicates.is_empty() {
            bail!(
                "{} capacity factors are given several times for the same edge: {}",
                duplicates.len(),
                format_ids(duplicates),
            );
        }
        // The factors of the parameters are compared to the factors of the edges through their
        // string representation.
        let names: HashSet<String> = ids.iter().map(|id| id.to_string()).collect();
        let keys: HashSet<String> = params.keys().cloned().collect();
        check_ids_exist(
            &keys,
            &names,
            "The following factors of the parameter `factors` are not the factor of any edge",
        )?;
        let values: Vec<Factor> = ids
            .iter()
            .map(|id| params.get(&id.to_string()).copied().unwrap_or_default())
            .collect();
        let outside: Vec<_> = ids
            .iter()
            .zip(values.iter())
            .filter(|(_, f)| !f.is_within_bounds())
            .map(|(id, _)| format!("`{id}`"))
            .collect();
        if !outside.is_empty() {
            bail!(
                "The initial value of {} factors is not between their minimum and maximum: {}",
                outside.len(),
                outside.join(", "),
            );
        }
        let mut combinations = Vec::new();
        let mut combination_index: HashMap<Vec<usize>, usize> = HashMap::default();
        let mut time_dependent = Vec::new();
        let edge_combinations: Vec<_> = factors_of_edge
            .into_iter()
            .zip(edges)
            .map(|(mut factors, e)| {
                if factors.is_empty() {
                    if e.has_time_dependent_flow() {
                        time_dependent.push(e.id());
                    }
                    return None;
                }
                factors.sort_unstable();
                Some(*combination_index.entry(factors).or_insert_with_key(|f| {
                    combinations.push(f.clone());
                    combinations.len() - 1
                }))
            })
            .collect();
        if !time_dependent.is_empty() {
            bail!(
                "The capacity calibration does not support time-dependent bottleneck flows on \
                edges without a capacity factor, but {} edges have one: {}",
                time_dependent.len(),
                format_ids(time_dependent),
            );
        }
        let factors = Self {
            capacity,
            ids,
            initial: values.iter().map(|f| f64::from(f.initial)).collect(),
            min: values.iter().map(|f| f.min.map(f64::from)).collect(),
            max: values.iter().map(|f| f.max.map(f64::from)).collect(),
            combinations,
            edge_combinations,
        };
        factors.warn_identical_factors();
        let nb_ignored_flows = edges
            .iter()
            .zip(factors.edge_combinations.iter())
            .filter(|(e, c)| c.is_some() && e.has_bottleneck_flow())
            .count();
        if nb_ignored_flows > 0 {
            warn!(
                "The input bottleneck flows of {nb_ignored_flows} edges are ignored: their \
                capacity is calibrated"
            );
        }
        Ok(factors)
    }

    /// Warns about the factors that are on exactly the same edges (only their product is
    /// identified).
    fn warn_identical_factors(&self) {
        let mut edges_of_factor: Vec<Vec<usize>> = vec![Vec::new(); self.ids.len()];
        for (i, c) in self.edge_combinations.iter().enumerate() {
            if let &Some(c) = c {
                self.combinations[c]
                    .iter()
                    .for_each(|&j| edges_of_factor[j].push(i));
            }
        }
        let mut groups: HashMap<&[usize], Vec<String>> = HashMap::default();
        for (j, edges) in edges_of_factor.iter().enumerate() {
            groups
                .entry(edges.as_slice())
                .or_default()
                .push(self.name(j));
        }
        let mut groups: Vec<_> = groups.into_values().filter(|g| g.len() > 1).collect();
        groups.sort();
        for group in groups {
            warn!(
                "The factors {} are on the same edges: only their product is identified",
                group.join(", ")
            );
        }
    }

    /// Returns the capacity per lane of each combination, given the value of each factor.
    fn combination_capacities(&self, values: &[f64]) -> Vec<FlowPerLane> {
        debug_assert_eq!(values.len(), self.ids.len());
        let capacity = f64::from(self.capacity);
        self.combinations
            .iter()
            .map(|c| {
                FlowPerLane::new_unchecked(capacity * c.iter().map(|&j| values[j]).product::<f64>())
            })
            .collect()
    }

    /// Returns the capacity per lane of each edge (`None` if the edge is not calibrated), given
    /// the value of each factor.
    fn edge_capacities(&self, values: &[f64]) -> impl Iterator<Item = Option<FlowPerLane>> + '_ {
        let capacities = self.combination_capacities(values);
        self.edge_combinations
            .iter()
            .map(move |c| c.map(|c| capacities[c]))
    }

    /// Returns the combination index of the given edge (`None` if the edge is not calibrated).
    fn combination_of(&self, edge: EdgeIndex) -> Option<usize> {
        self.edge_combinations[edge.index()]
    }

    /// Returns the bottleneck flows of the edges (ordered by `EdgeIndex`), given the value of each
    /// factor (the edges that are not calibrated keep their input flow).
    fn bottleneck_flows(&self, edges: &[&RoadEdge], values: &[f64]) -> BottleneckFlows {
        BottleneckFlows::from_capacities(edges, self.edge_capacities(values))
    }

    /// Returns the name of the given factor, for the logs.
    fn name(&self, factor: usize) -> String {
        format!("`{}`", self.ids[factor])
    }

    /// Logs the range of the capacities per lane of the calibrated edges, given the value of each
    /// factor, with the given description of the values.
    fn log_capacity_range(&self, description: &str, values: &[f64]) {
        let (min, max) = self
            .combination_capacities(values)
            .iter()
            .fold((f64::INFINITY, 0.0f64), |(min, max), &c| {
                (min.min(f64::from(c)), max.max(f64::from(c)))
            });
        info!(
            "{description} capacities of the calibrated edges: from {:.0} to {:.0} PCE/h per lane",
            3600. * min,
            3600. * max,
        );
    }

    /// Logs the number of edges, the initial value and the bounds of each factor, the number of
    /// combinations and the range of the initial capacities.
    fn log_summary(&self) {
        let mut nb_edges = vec![0; self.ids.len()];
        let mut nb_uncalibrated_edges = 0;
        for &c in self.edge_combinations.iter() {
            if let Some(c) = c {
                self.combinations[c].iter().for_each(|&j| nb_edges[j] += 1);
            } else {
                nb_uncalibrated_edges += 1;
            }
        }
        info!(
            "Capacity of {} PCE/s per lane ({:.0} PCE/h per lane) times the factors of the edges",
            f64::from(self.capacity),
            3600. * f64::from(self.capacity),
        );
        for (j, n) in nb_edges.into_iter().enumerate() {
            let bound = |name: &str, value: Option<f64>| {
                value.map_or_else(String::new, |v| format!(", {name} {v}"))
            };
            info!(
                "Factor {}: {n} edges, initial value {}{}{}",
                self.name(j),
                self.initial[j],
                bound("minimum", self.min[j]),
                bound("maximum", self.max[j]),
            );
        }
        info!("{} combinations of factors", self.combinations.len());
        self.log_capacity_range("Initial", &self.initial);
        if nb_uncalibrated_edges > 0 {
            info!(
                "{nb_uncalibrated_edges} edges without a capacity factor keep their input \
                bottleneck flow"
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

    /// Creates an edge with the given id, speed-density function and (per-lane) bottleneck flows.
    fn edge(
        id: i64,
        speed_density_type: &str,
        bottleneck_flow: Option<f64>,
        time_dependent_flows: bool,
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
        )
        .unwrap()
    }

    fn capacity(value: f64) -> FlowPerLane {
        FlowPerLane::try_from(value).unwrap()
    }

    /// Returns the factors of the edges, from `(edge id, factor id)` pairs.
    fn edge_factors(pairs: &[(i64, &str)]) -> Vec<EdgeFactor> {
        pairs
            .iter()
            .map(|&(edge_id, factor)| EdgeFactor {
                edge_id: MetroId::from(edge_id),
                factor: MetroId::from(factor),
            })
            .collect()
    }

    /// Returns the `factors` parameter from `(factor id, initial, min, max)` values.
    fn params(values: &[(&str, f64, Option<f64>, Option<f64>)]) -> HashMap<String, Factor> {
        let num = |v: f64| PositiveNum::try_from(v).unwrap();
        values
            .iter()
            .map(|&(id, initial, min, max)| {
                (
                    id.to_owned(),
                    Factor {
                        initial: num(initial),
                        min: min.map(num),
                        max: max.map(num),
                    },
                )
            })
            .collect()
    }

    #[test]
    fn capacity_factors_test() {
        let e0 = edge(0, "FreeFlow", Some(1.0), false);
        let e1 = edge(1, "FreeFlow", None, false);
        let e2 = edge(2, "FreeFlow", None, true);
        let e3 = edge(3, "FreeFlow", Some(1.0), false);
        let edges = [&e0, &e1, &e2, &e3];
        let rows = edge_factors(&[(0, "b"), (2, "a"), (3, "b"), (2, "c"), (0, "a")]);
        let new = |params: &HashMap<String, Factor>, rows: &[EdgeFactor]| {
            CapacityFactors::new(&edges, capacity(0.5), params, rows)
        };
        // Factors in order of first appearance, default value 1; edges without a factor are not
        // calibrated; edges with the same factors share a combination (whatever the order).
        let factors = new(&HashMap::default(), &rows).unwrap();
        assert_eq!(factors.capacity, capacity(0.5));
        assert_eq!(
            factors.ids,
            vec![MetroId::from("b"), MetroId::from("a"), MetroId::from("c")]
        );
        assert_eq!(factors.initial, vec![1.; 3]);
        assert_eq!(factors.min, vec![None; 3]);
        assert_eq!(factors.max, vec![None; 3]);
        assert_eq!(factors.combinations, vec![vec![0, 1], vec![1, 2], vec![0]]);
        assert_eq!(
            factors.edge_combinations,
            vec![Some(0), None, Some(1), Some(2)]
        );
        // Same combination for edge 3 as for edge 0.
        let rows_ba = edge_factors(&[(0, "b"), (0, "a"), (2, "c"), (3, "a"), (3, "b")]);
        let factors = new(&HashMap::default(), &rows_ba).unwrap();
        assert_eq!(factors.combinations, vec![vec![0, 1], vec![2]]);
        assert_eq!(
            factors.edge_combinations,
            vec![Some(0), None, Some(1), Some(0)]
        );

        // Initial values and bounds from the parameters.
        let factors = new(
            &params(&[("a", 0.5, Some(0.1), None), ("c", 0.8, None, Some(1.0))]),
            &rows,
        )
        .unwrap();
        assert_eq!(factors.initial, vec![1., 0.5, 0.8]);
        assert_eq!(factors.min, vec![None, Some(0.1), None]);
        assert_eq!(factors.max, vec![None, None, Some(1.0)]);
        // The initial values must be within the bounds.
        let msg = new(
            &params(&[("a", 0.5, Some(0.6), None), ("b", 0.6, None, Some(0.5))]),
            &rows,
        )
        .unwrap_err()
        .to_string();
        assert!(
            msg.ends_with("2 factors is not between their minimum and maximum: `b`, `a`"),
            "{msg}"
        );
        // A factor of the parameters must be the factor of some edge.
        let msg = new(&params(&[("d", 0.5, None, None)]), &rows)
            .unwrap_err()
            .to_string();
        assert!(msg.ends_with("not the factor of any edge: d"), "{msg}");
        // The edges must exist, a factor is given once per edge and there is at least one factor.
        let msg = new(&HashMap::default(), &edge_factors(&[(0, "a"), (9, "a")]))
            .unwrap_err()
            .to_string();
        assert!(msg.ends_with("not part of the road network: 9"), "{msg}");
        let msg = new(&HashMap::default(), &edge_factors(&[(0, "a"), (0, "a")]))
            .unwrap_err()
            .to_string();
        assert!(
            msg.ends_with("several times for the same edge: (0, a)"),
            "{msg}"
        );
        assert!(new(&HashMap::default(), &[]).is_err());

        // Time-dependent flows are not allowed on the edges without a factor.
        let msg = new(&HashMap::default(), &edge_factors(&[(0, "a")]))
            .unwrap_err()
            .to_string();
        assert!(msg.contains("1 edges have one: 2"), "{msg}");

        // All the edges must have a `FreeFlow` speed-density function.
        let e1 = edge(1, "Bottleneck", None, false);
        let edges = [&e0, &e1];
        let msg = CapacityFactors::new(
            &edges,
            capacity(0.5),
            &HashMap::default(),
            &edge_factors(&[(0, "a")]),
        )
        .unwrap_err()
        .to_string();
        assert!(msg.contains("1 edges have another function: 1"), "{msg}");
    }

    #[test]
    fn edge_capacities_test() {
        // Capacity 0.5 times the product of the factors; the edges without a factor are not
        // calibrated.
        let e0 = edge(0, "FreeFlow", Some(1.0), false);
        let e1 = edge(1, "FreeFlow", Some(1.0), false);
        let e2 = edge(2, "FreeFlow", None, false);
        let edges = [&e0, &e1, &e2];
        let factors = CapacityFactors::new(
            &edges,
            capacity(0.5),
            &HashMap::default(),
            &edge_factors(&[(0, "a"), (2, "a"), (2, "b")]),
        )
        .unwrap();
        let capacities: Vec<_> = factors.edge_capacities(&[0.8, 0.5]).collect();
        assert_eq!(
            capacities,
            vec![Some(capacity(0.4)), None, Some(capacity(0.2))]
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
            serde_json::from_str(&format!(r#"{{"capacity": 0.5, {json}}}"#)).unwrap()
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
    fn stable_factors_test() {
        let history = [[1.0, 2.0], [1.2, 2.0], [1.0, 2.2], [1.0, 2.2]];
        let history: Vec<&[f64]> = history.iter().map(|f| f.as_slice()).collect();
        // Mean of each factor.
        assert_eq!(mean_factors(&history[1..]), vec![3.2 / 3., 6.4 / 3.]);
        // Windows of 2 days: (1.1, 2.0), then (1.0, 2.2), a change of 10%.
        assert!(stable_factors(&history, 2, Some(0.1 + 1e-9)));
        assert!(!stable_factors(&history, 2, Some(0.09)));
        // Without tolerance or with less than two windows of days: not stable.
        assert!(!stable_factors(&history, 2, None));
        assert!(!stable_factors(&history[1..], 2, Some(1.)));
        // Windows of 1 day: the last two days are equal.
        assert!(stable_factors(&history, 1, Some(1e-12)));
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
        assert_eq!(max_relative_change(&[0.5, 0.2], &[0.5, 0.2]), 0.);
        let change = max_relative_change(&[0.5, 0.2], &[0.45, 0.21]);
        assert!((change - 0.1).abs() < 1e-12, "{change}");
    }

    #[test]
    fn check_bottleneck_model_test() {
        let e0 = edge(0, "FreeFlow", Some(1.0), false);
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
