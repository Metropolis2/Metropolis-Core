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

//! Surrogate model of the capacity calibration: predicts the queueing delays of the target routes
//! for any capacities, holding fixed the arrival curves recorded during a simulated day.
//!
//! The entry bottleneck of an edge is the discrete FIFO bottleneck of the within-day model: a
//! vehicle crosses it when it arrives or when the bottleneck re-opens, and the bottleneck then
//! closes for the PCE of the vehicle divided by its flow. For a given flow, the surrogate computes
//! the waiting time of each recorded vehicle and averages them into a waiting-time function, as the
//! within-day model records it (see [RecordingGrid]). A target route (probe) reaching the
//! bottleneck at a given time waits the value of this function at that time, as the target delays
//! are computed from the recorded functions (the waiting time of the probe is the mean waiting time
//! of the vehicles arrived around it). It does not add any traffic.
//!
//! With spillback, a vehicle can also wait for space on the edge, until a vehicle leaves it (or
//! until it is forced to enter). Such a vehicle is released when the bottleneck is already open, so
//! it enters at the latest of its arrival time, the re-opening of the bottleneck and its release
//! time. The release times are recorded with the arrival curves and held fixed: at the capacities of
//! the simulated day, the surrogate reproduces the recorded waiting times exactly, and a change of
//! capacity is propagated through the queue behind a vehicle held by space. The effect of the
//! capacities on the release times (a larger capacity further on frees space earlier) is not
//! modeled: the next simulated days include it.
use std::collections::VecDeque;

use num_traits::ConstZero;
use petgraph::graph::EdgeIndex;
use rayon::prelude::*;
use ttf::TTFNum;

use super::CapacityFactors;
use crate::network::road_network::arrival_curve::{ArrivalCurve, ArrivalCurves};
use crate::network::road_network::vehicle::Vehicle;
use crate::network::road_network::RoadEdge;
use crate::units::*;

/// Breakpoints of the waiting-time functions recorded by the within-day model, one per recording
/// interval from the start of the period.
///
/// The waiting time of a vehicle is shared between the two breakpoints around its arrival time,
/// with weights linear in the distance to them, and the value at a breakpoint is the weighted mean
/// of the waiting times (zero if no vehicle arrived around it). The waiting times of the vehicles
/// arrived after the end of the period are not recorded. The function is then made FIFO, and it is
/// evaluated by linear interpolation (the value at the last breakpoint after it).
#[derive(Clone, Copy, Debug)]
pub(crate) struct RecordingGrid {
    /// Time of the first breakpoint (start of the period, in seconds).
    start: f64,
    /// Time between two breakpoints (in seconds).
    interval: f64,
    /// Number of breakpoints.
    nb_points: usize,
    /// End of the period (in seconds).
    end: f64,
}

impl RecordingGrid {
    /// Creates a [RecordingGrid] for the given period and recording interval.
    pub(crate) fn new(period: Interval, interval: PositiveSeconds) -> Self {
        let start = f64::from(period.start());
        let end = f64::from(period.end());
        let interval = f64::from(interval);
        // Same number of breakpoints as in `WaitXYFBuilder::new`.
        let nb_points = ((end - start) / interval) as usize + 1;
        Self {
            start,
            interval,
            nb_points,
            end,
        }
    }

    /// Returns the index of the last breakpoint before or at the given time (the first breakpoint
    /// for a time before the start) and the share of the next breakpoint in the linear
    /// interpolation at that time.
    fn locate(&self, time: NonNegativeSeconds) -> (usize, f64) {
        let x = ((f64::from(time) - self.start) / self.interval).max(0.);
        let i = x as usize;
        (i, x - i as f64)
    }
}

/// Total flow of a bottleneck of the surrogate model.
#[derive(Clone, Copy, Debug)]
enum Capacity {
    /// Calibrated edge: the total flow is the capacity of its combination of factors times the
    /// number of lanes.
    Calibrated { combination: usize, lanes: Lanes },
    /// Edge that is not calibrated, with a constant input flow (`None` if the flow is infinite, the
    /// vehicles then only wait for space, with spillback).
    Fixed(Option<Flow>),
}

/// Entry bottleneck of an edge of the target routes, with its recorded arrival curve.
#[derive(Clone, Debug)]
struct Bottleneck {
    curve: ArrivalCurve,
    capacity: Capacity,
    /// Waiting-time function, for the current flow.
    waiting_times: WaitingTimes,
}

impl Bottleneck {
    /// Creates a new [Bottleneck] (the waiting times of a [Capacity::Fixed] bottleneck are
    /// computed once, here).
    fn new(curve: ArrivalCurve, capacity: Capacity, grid: &RecordingGrid) -> Self {
        let mut bottleneck = Self {
            curve,
            capacity,
            waiting_times: WaitingTimes::default(),
        };
        if let Capacity::Fixed(flow) = capacity {
            compute_waiting_times(&bottleneck.curve, flow, grid, &mut bottleneck.waiting_times);
        }
        bottleneck
    }

    /// Returns the total flow of the bottleneck, given the capacity of each combination.
    fn flow(&self, capacities: &[FlowPerLane]) -> Option<Flow> {
        match self.capacity {
            // Same operation as in `BottleneckFlows::from_capacities`.
            Capacity::Calibrated { combination, lanes } => Some(capacities[combination] * lanes),
            Capacity::Fixed(flow) => flow,
        }
    }

    /// Updates the waiting times of a [Capacity::Calibrated] bottleneck for the given capacity of
    /// each combination.
    fn update(&mut self, capacities: &[FlowPerLane], grid: &RecordingGrid) {
        if matches!(self.capacity, Capacity::Calibrated { .. }) {
            let flow = self.flow(capacities);
            compute_waiting_times(&self.curve, flow, grid, &mut self.waiting_times);
        }
    }
}

/// Waiting-time function of a bottleneck, at the breakpoints of the [RecordingGrid].
///
/// Only the breakpoints from the one before the first arrival to the last non-zero one are stored
/// (the function is zero at the others).
#[derive(Clone, Debug, Default)]
struct WaitingTimes {
    /// Index of the first stored breakpoint.
    first_point: usize,
    /// Waiting time at the stored breakpoints (in seconds).
    values: Vec<f64>,
    /// Derivative of the waiting time at the stored breakpoints with respect to the flow of the
    /// bottleneck (in seconds per PCE/s).
    flow_derivatives: Vec<f64>,
}

impl WaitingTimes {
    /// Returns the waiting time and its derivative with respect to the flow at the breakpoint of
    /// the given index.
    fn at(&self, point: usize) -> (f64, f64) {
        point
            .checked_sub(self.first_point)
            .and_then(|i| Some((*self.values.get(i)?, self.flow_derivatives[i])))
            .unwrap_or((0., 0.))
    }
}

/// Computes the waiting-time function of a bottleneck with the given flow (`None` if infinite), from
/// its arrival curve.
///
/// A vehicle arriving at `t_k` waits `w_k = max(0, w_{k-1} + p_{k-1} / s - (t_k - t_{k-1}), r_k - t_k)`,
/// where `p_{k-1}` is the PCE of the previous vehicle, `s` the flow and `r_k` the release time of the
/// vehicle if it waited for space (spillback). In a busy period starting at vehicle `b` (the last
/// vehicle that did not wait or that was held by space), which entered at `e_b` (`t_b` or `r_b`),
/// `w_k = e_b + sum_{b <= j < k} p_j / s - t_k`, so `dw_k / ds = -(w_k + t_k - e_b) / s` (zero for
/// the vehicle `b` itself).
fn compute_waiting_times(
    curve: &ArrivalCurve,
    flow: Option<Flow>,
    grid: &RecordingGrid,
    waiting_times: &mut WaitingTimes,
) {
    let WaitingTimes {
        first_point,
        values,
        flow_derivatives,
    } = waiting_times;
    values.clear();
    flow_derivatives.clear();
    let times = curve.times();
    let pce = curve.pce();
    // The waiting times of the vehicles arrived after the end of the period are not recorded.
    let nb_arrivals = times.partition_point(|&t| f64::from(t) <= grid.end);
    if nb_arrivals == 0 {
        *first_point = 0;
        return;
    }
    *first_point = grid.locate(times[0]).0;
    let last_point = (grid.locate(times[nb_arrivals - 1]).0 + 1).min(grid.nb_points - 1);
    let nb_values = last_point + 1 - *first_point;
    values.resize(nb_values, 0.);
    flow_derivatives.resize(nb_values, 0.);
    let mut weights = vec![0.; nb_values];
    let s = flow.map_or(f64::INFINITY, f64::from);
    let releases = curve.releases();
    let mut next_release = 0;
    let mut wait = 0.;
    let mut busy_start = f64::from(times[0]);
    for k in 0..nb_arrivals {
        let t = f64::from(times[k]);
        if k > 0 {
            let gap = t - f64::from(times[k - 1]);
            wait = (wait + f64::from(pce[k - 1]) / s - gap).max(0.);
            if wait == 0. {
                busy_start = t;
            }
        }
        if releases.get(next_release).is_some_and(|&(i, _)| i == k) {
            let release = f64::from(releases[next_release].1);
            next_release += 1;
            if release - t > wait {
                // The vehicle is held by space until its release.
                wait = release - t;
                busy_start = release;
            }
        }
        let derivative = -(wait + t - busy_start) / s;
        let (point, share) = grid.locate(times[k]);
        for (point, weight) in [(point, 1. - share), (point + 1, share)] {
            if point < grid.nb_points {
                let i = point - *first_point;
                weights[i] += weight;
                values[i] += weight * wait;
                flow_derivatives[i] += weight * derivative;
            }
        }
    }
    for i in 0..nb_values {
        if weights[i] > 0. {
            values[i] /= weights[i];
            flow_derivatives[i] /= weights[i];
        }
    }
    // Same as `TTF::ensure_fifo`: the waiting time decreases by less than the interval between
    // two breakpoints (minus a margin), also after the last stored breakpoint.
    let min_value = |previous: f64| previous - grid.interval + <f64 as TTFNum>::MARGIN;
    for i in 1..nb_values {
        if values[i] < min_value(values[i - 1]) {
            values[i] = min_value(values[i - 1]);
            flow_derivatives[i] = flow_derivatives[i - 1];
        }
    }
    while *first_point + values.len() < grid.nb_points {
        let last = values.len() - 1;
        let value = min_value(values[last]);
        if value <= 0. {
            break;
        }
        values.push(value);
        flow_derivatives.push(flow_derivatives[last]);
    }
    values.shrink_to_fit();
    flow_derivatives.shrink_to_fit();
}

/// Crossing of a bottleneck by a probe.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Entry {
    /// Time at which the probe crosses the bottleneck.
    time: NonNegativeSeconds,
    /// Derivative of the crossing time with respect to the time at which the probe reaches the
    /// bottleneck.
    time_derivative: f64,
    /// Derivative of the crossing time with respect to the flow of the bottleneck (in seconds per
    /// PCE/s).
    flow_derivative: f64,
}

/// Returns the [Entry] of a probe reaching a bottleneck at the given time, given its waiting-time
/// function: the probe waits the value of the function at that time.
fn entry(waiting_times: &WaitingTimes, grid: &RecordingGrid, time: NonNegativeSeconds) -> Entry {
    let (point, share) = grid.locate(time);
    let (wait, slope, flow_derivative) = if point + 1 >= grid.nb_points {
        // After the last breakpoint, the function is constant.
        let (wait, flow_derivative) = waiting_times.at(grid.nb_points - 1);
        (wait, 0., flow_derivative)
    } else {
        let (wait0, flow_derivative0) = waiting_times.at(point);
        let (wait1, flow_derivative1) = waiting_times.at(point + 1);
        (
            (1. - share) * wait0 + share * wait1,
            (wait1 - wait0) / grid.interval,
            (1. - share) * flow_derivative0 + share * flow_derivative1,
        )
    };
    Entry {
        time: time + NonNegativeSeconds::new_unchecked(wait),
        time_derivative: 1. + slope,
        flow_derivative,
    }
}

/// Edge of the path of a probe.
#[derive(Clone, Debug)]
struct ProbeEdge {
    /// Free-flow travel time of the edge, for the vehicle type of the calibration.
    free_flow_tt: NonNegativeSeconds,
    /// Index of the entry bottleneck of the edge in the surrogate model (`None` if the edge has no
    /// arrival curve, i.e., its flow is infinite and spillback is disabled).
    bottleneck: Option<usize>,
}

/// Target route walked through the surrogate model.
#[derive(Clone, Debug)]
struct Probe {
    /// Time at which the probe reaches the first edge of its path.
    departure_time: NonNegativeSeconds,
    path: Vec<ProbeEdge>,
}

impl Probe {
    /// Returns the total queueing delay of the probe along its path.
    ///
    /// A delay at a bottleneck shifts the time at which the probe reaches all the next ones.
    ///
    /// If `gradient` is given (with one value per factor, initially zero), it receives the
    /// derivative of the delay with respect to each factor, given the [Evaluation] of the factors.
    fn delay(
        &self,
        bottlenecks: &[Bottleneck],
        grid: &RecordingGrid,
        mut gradient: Option<(&mut [f64], &Evaluation<'_>)>,
    ) -> NonNegativeSeconds {
        let mut time = self.departure_time;
        let mut delay = NonNegativeSeconds::ZERO;
        for edge in self.path.iter() {
            if let Some(i) = edge.bottleneck {
                let bottleneck = &bottlenecks[i];
                let entry = entry(&bottleneck.waiting_times, grid, time);
                if let Some((gradient, evaluation)) = gradient.as_mut() {
                    // The derivatives of the arrival time at the bottleneck are carried to the
                    // crossing time, plus the effect of the flow of the bottleneck.
                    if entry.time_derivative != 1. {
                        gradient
                            .iter_mut()
                            .for_each(|g| *g *= entry.time_derivative);
                    }
                    if let Capacity::Calibrated { combination, lanes } = bottleneck.capacity {
                        // The flow is `C·Πₖ fₖ·lanes`: its derivative with respect to a factor
                        // `fⱼ` of the combination is the flow divided by `fⱼ`.
                        let flow = f64::from(evaluation.capacities[combination]) * f64::from(lanes);
                        for &j in evaluation.combinations[combination].iter() {
                            gradient[j] += entry.flow_derivative * flow / evaluation.values[j];
                        }
                    }
                }
                delay += entry.time.sub_unchecked(time);
                time = entry.time;
            }
            time += edge.free_flow_tt;
        }
        delay
    }
}

/// Factors at which the surrogate model is evaluated, with the resulting capacities.
struct Evaluation<'a> {
    /// Value of each factor.
    values: &'a [f64],
    /// Capacity per lane of each combination of factors.
    capacities: Vec<FlowPerLane>,
    /// Factor indices of each combination.
    combinations: &'a [Vec<usize>],
}

/// Surrogate model predicting the queueing delays of the target routes for any capacities, from
/// the arrival curves recorded during a simulated day.
#[derive(Clone, Debug)]
pub(crate) struct Surrogate {
    bottlenecks: Vec<Bottleneck>,
    probes: Vec<Probe>,
    grid: RecordingGrid,
    /// Capacity factors (the capacities of the combinations are computed from them).
    factors: CapacityFactors,
}

impl Surrogate {
    /// Creates the [Surrogate] from the arrival curves (indexed by `EdgeIndex`), the edges of the
    /// road network (ordered by `EdgeIndex`), the capacity factors, the vehicle type of the
    /// calibration, the target routes (departure time and path) and the breakpoints of the
    /// recorded waiting-time functions.
    pub(crate) fn new(
        curves: ArrivalCurves,
        edges: &[&RoadEdge],
        factors: &CapacityFactors,
        vehicle: &Vehicle,
        routes: impl IntoIterator<Item = (NonNegativeSeconds, Vec<EdgeIndex>)>,
        grid: RecordingGrid,
    ) -> Self {
        debug_assert!(!factors.ids.is_empty());
        let mut bottleneck_of = vec![None; edges.len()];
        let mut bottlenecks = Vec::new();
        for (i, curve) in curves.into_iter().enumerate() {
            let Some(curve) = curve else {
                continue;
            };
            let edge = edges[i];
            let capacity = match factors.combination_of(EdgeIndex::new(i)) {
                Some(combination) => Capacity::Calibrated {
                    combination,
                    lanes: edge.lanes(),
                },
                None => Capacity::Fixed(edge.constant_bottleneck_flow()),
            };
            bottleneck_of[i] = Some(bottlenecks.len());
            bottlenecks.push(Bottleneck::new(curve, capacity, &grid));
        }
        let probes = routes
            .into_iter()
            .map(|(departure_time, path)| Probe {
                departure_time,
                path: path
                    .into_iter()
                    .map(|e| ProbeEdge {
                        free_flow_tt: edges[e.index()].get_free_flow_travel_time(vehicle),
                        bottleneck: bottleneck_of[e.index()],
                    })
                    .collect(),
            })
            .collect();
        Self {
            bottlenecks,
            probes,
            grid,
            factors: factors.clone(),
        }
    }

    /// Returns the number of factors.
    fn nb_factors(&self) -> usize {
        self.factors.ids.len()
    }

    /// Returns the predicted queueing delay of each target route (in the order of the routes),
    /// given the value of each factor.
    pub(crate) fn predict(&mut self, values: &[f64]) -> Vec<NonNegativeSeconds> {
        self.update(values);
        let bottlenecks = &self.bottlenecks;
        let grid = &self.grid;
        self.probes
            .par_iter()
            .map(|p| p.delay(bottlenecks, grid, None))
            .collect()
    }

    /// Returns the predicted queueing delay of each target route (in the order of the routes) and
    /// the Jacobian matrix of the delays with respect to the factors (row-major, one row per
    /// target route and one column per factor, in seconds), given the value of each factor.
    pub(crate) fn predict_with_jacobian(
        &mut self,
        values: &[f64],
    ) -> (Vec<NonNegativeSeconds>, Vec<f64>) {
        let evaluation = Evaluation {
            values,
            capacities: self.update(values),
            combinations: &self.factors.combinations,
        };
        let bottlenecks = &self.bottlenecks;
        let grid = &self.grid;
        let nb_factors = self.factors.ids.len();
        let mut jacobian = vec![0.; self.probes.len() * nb_factors];
        let delays = self
            .probes
            .par_iter()
            .zip(jacobian.par_chunks_mut(nb_factors))
            .map(|(p, gradient)| p.delay(bottlenecks, grid, Some((gradient, &evaluation))))
            .collect();
        (delays, jacobian)
    }

    /// Returns, for each factor, whether some target route crosses one of its edges (otherwise,
    /// the predicted delays do not depend on it).
    pub(crate) fn crossed_factors(&self) -> Vec<bool> {
        let mut crossed = vec![false; self.nb_factors()];
        for edge in self.probes.iter().flat_map(|p| p.path.iter()) {
            if let Some(i) = edge.bottleneck {
                if let Capacity::Calibrated { combination, .. } = self.bottlenecks[i].capacity {
                    self.factors.combinations[combination]
                        .iter()
                        .for_each(|&j| crossed[j] = true);
                }
            }
        }
        crossed
    }

    /// Updates the waiting times of the calibrated bottlenecks for the given value of each
    /// factor, and returns the capacity per lane of each combination.
    fn update(&mut self, values: &[f64]) -> Vec<FlowPerLane> {
        debug_assert_eq!(values.len(), self.nb_factors());
        let capacities = self.factors.combination_capacities(values);
        let grid = &self.grid;
        self.bottlenecks
            .par_iter_mut()
            .for_each(|b| b.update(&capacities, grid));
        capacities
    }
}

/// Surrogate model of the last simulated days: predicts the mean of the delays predicted by the
/// surrogate models of the days.
///
/// The days may have been simulated with different capacities: the surrogate model of each day
/// evaluates the queues of its arrival curves at any capacities.
#[derive(Clone, Debug)]
pub(crate) struct MeanSurrogate {
    /// Surrogate model of each day, from the oldest to the newest (at least one).
    days: VecDeque<Surrogate>,
}

impl MeanSurrogate {
    /// Creates the [MeanSurrogate] from the surrogate model of a first day.
    pub(crate) fn new(day: Surrogate) -> Self {
        Self {
            days: VecDeque::from([day]),
        }
    }

    /// Adds the surrogate model of a new day, then drops the oldest days so that at most
    /// `max_days` days (at least one) are kept.
    pub(crate) fn push(&mut self, day: Surrogate, max_days: usize) {
        self.days.push_back(day);
        while self.days.len() > max_days.max(1) {
            self.days.pop_front();
        }
    }

    /// Returns the number of days.
    pub(crate) fn len(&self) -> usize {
        self.days.len()
    }

    /// Returns the predicted queueing delay of each target route on each day (from the oldest to
    /// the newest), given the value of each factor.
    pub(crate) fn predict_days(&mut self, values: &[f64]) -> Vec<Vec<NonNegativeSeconds>> {
        self.days
            .iter_mut()
            .map(|day| day.predict(values))
            .collect()
    }

    /// Returns the mean predicted queueing delay of each target route (in the order of the routes)
    /// and the mean Jacobian matrix of the delays with respect to the factors (see
    /// [Surrogate::predict_with_jacobian]), given the value of each factor.
    pub(crate) fn predict_with_jacobian(
        &mut self,
        values: &[f64],
    ) -> (Vec<NonNegativeSeconds>, Vec<f64>) {
        let (delays, jacobians): (Vec<Vec<f64>>, Vec<Vec<f64>>) = self
            .days
            .iter_mut()
            .map(|day| {
                let (delays, jacobian) = day.predict_with_jacobian(values);
                (delays.into_iter().map(f64::from).collect(), jacobian)
            })
            .unzip();
        let delays = mean(delays.into_iter())
            .into_iter()
            .map(NonNegativeSeconds::new_unchecked)
            .collect();
        (delays, mean(jacobians.into_iter()))
    }

    /// Returns, for each factor, whether some target route crosses one of its edges on some day
    /// (otherwise, the predicted delays do not depend on it).
    pub(crate) fn crossed_factors(&self) -> Vec<bool> {
        self.days
            .iter()
            .map(Surrogate::crossed_factors)
            .reduce(|a, b| a.iter().zip(b).map(|(&a, b)| a || b).collect())
            .expect("There is at least one day")
    }
}

/// Returns the element-wise mean of vectors of the same length.
fn mean(vectors: impl Iterator<Item = Vec<f64>>) -> Vec<f64> {
    let mut sums: Vec<f64> = Vec::new();
    let mut nb_vectors = 0;
    for vector in vectors {
        if nb_vectors == 0 {
            sums = vector;
        } else {
            sums.iter_mut().zip(vector).for_each(|(s, x)| *s += x);
        }
        nb_vectors += 1;
    }
    sums.iter_mut().for_each(|s| *s /= nb_vectors as f64);
    sums
}

#[cfg(test)]
mod tests {
    use num_traits::ConstOne;
    use ttf::PwlTTF;

    use super::*;
    use crate::calibration::optimizer::optimize_factors;
    use crate::calibration::parameters::OptimizerParameters;
    use crate::hash::HashSet;
    use crate::network::road_network::vehicle::SpeedFunction;
    use crate::network::road_network::SpeedDensityFunction;

    fn s(t: f64) -> NonNegativeSeconds {
        NonNegativeSeconds::new_unchecked(t)
    }

    fn curve(arrivals: &[(f64, f64)]) -> ArrivalCurve {
        let mut curve = ArrivalCurve::default();
        for &(time, pce) in arrivals {
            curve.push(s(time), PCE::new_unchecked(pce));
        }
        curve
    }

    /// Returns a deterministic sequence of pseudo-random numbers in [0, 1).
    fn pseudo_random(n: usize) -> Vec<f64> {
        let mut x: u64 = 13;
        (0..n)
            .map(|_| {
                x = x
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                (x >> 11) as f64 / (1u64 << 53) as f64
            })
            .collect()
    }

    /// Recording grid with breakpoints every `interval` seconds over `[0, end]`.
    fn grid(end: f64, interval: f64) -> RecordingGrid {
        RecordingGrid::new(
            Interval::new_unchecked(0., end),
            PositiveSeconds::new_unchecked(interval),
        )
    }

    fn assert_close(actual: f64, expected: f64) {
        assert!(
            (actual - expected).abs() <= 1e-9 * expected.abs().max(1.),
            "{actual} != {expected}"
        );
    }

    #[test]
    fn waiting_times_test() {
        // Breakpoints at 0, 10, 20 and 30; flow 0.5, so a vehicle closes the bottleneck for 2 s.
        let grid = grid(30., 10.);
        assert_eq!(grid.nb_points, 4);
        let curve = curve(&[
            (0., 1.),
            (1., 1.),
            (2., 1.),
            (10., 1.),
            (20., 1.),
            (35., 1.),
        ]);
        let mut waiting_times = WaitingTimes::default();
        compute_waiting_times(
            &curve,
            Some(Flow::new_unchecked(0.5)),
            &grid,
            &mut waiting_times,
        );
        // Waiting times 0, 1, 2, 0 and 0 (the vehicle at 35 is after the end of the period). The
        // busy period started at 0, so the derivatives are -(1 + 1) / 0.5 = -4 and
        // -(2 + 2) / 0.5 = -8. Weights at 0: 1, 0.9 and 0.8; at 10: 0.1, 0.2 and 1; at 20: 1.
        assert_eq!(waiting_times.first_point, 0);
        assert_eq!(waiting_times.values.len(), 4);
        let expected = [
            (2.5 / 2.7, -10. / 2.7),
            (0.5 / 1.3, -2. / 1.3),
            (0., 0.),
            (0., 0.),
        ];
        for (point, (value, derivative)) in expected.into_iter().enumerate() {
            let (actual_value, actual_derivative) = waiting_times.at(point);
            assert_close(actual_value, value);
            assert_close(actual_derivative, derivative);
        }
        assert_eq!(waiting_times.at(4), (0., 0.));
        // Two vehicles arriving at the same time: the second one waits 1 / 0.5 = 2, with
        // derivative -(2 + 0) / 0.5 = -4.
        let simultaneous = self::curve(&[(0., 1.), (0., 1.)]);
        let mut simultaneous_times = WaitingTimes::default();
        compute_waiting_times(
            &simultaneous,
            Some(Flow::new_unchecked(0.5)),
            &grid,
            &mut simultaneous_times,
        );
        assert_eq!(simultaneous_times.at(0), (1., -2.));
        // A probe at 5 waits the mean of the waiting times at 0 and 10.
        let entry = |t: f64| entry(&waiting_times, &grid, s(t));
        let probe = entry(5.);
        let (v0, d0) = expected[0];
        let (v1, d1) = expected[1];
        assert_close(f64::from(probe.time), 5. + (v0 + v1) / 2.);
        assert_close(probe.time_derivative, 1. + (v1 - v0) / 10.);
        assert_close(probe.flow_derivative, (d0 + d1) / 2.);
        let not_queued = |time: f64| Entry {
            time: s(time),
            time_derivative: 1.,
            flow_derivative: 0.,
        };
        assert_eq!(entry(25.), not_queued(25.));
        // After the last breakpoint.
        assert_eq!(entry(40.), not_queued(40.));

        // FIFO: flow 0.1 (10 s per vehicle), waiting times 0, 9, 18 and 27, with derivatives
        // -(9 + 1) / 0.1 = -100, -200 and -300. Weights at 0: 1, 0.9, 0.8 and 0.7; at 10: 0.1, 0.2
        // and 0.3. The waiting time at 10 (21 s) decreases by 10 s minus the margin at each next
        // breakpoint, while it is positive.
        let grid = self::grid(50., 10.);
        let curve = self::curve(&[(0., 1.), (1., 1.), (2., 1.), (3., 1.)]);
        compute_waiting_times(
            &curve,
            Some(Flow::new_unchecked(0.1)),
            &grid,
            &mut waiting_times,
        );
        assert_eq!(waiting_times.values.len(), 4);
        let margin = <f64 as TTFNum>::MARGIN;
        let derivative = (0.1 * -100. + 0.2 * -200. + 0.3 * -300.) / 0.6;
        let expected = [
            ((0.9 * 9. + 0.8 * 18. + 0.7 * 27.) / 3.4, None),
            (21., Some(derivative)),
            (11. + margin, Some(derivative)),
            (1. + 2. * margin, Some(derivative)),
            (0., Some(0.)),
        ];
        for (point, (value, derivative)) in expected.into_iter().enumerate() {
            let (actual_value, actual_derivative) = waiting_times.at(point);
            assert_close(actual_value, value);
            if let Some(derivative) = derivative {
                assert_close(actual_derivative, derivative);
            }
        }

        // Spillback: the vehicle arrived at 0 is held by space until 5, so it waits 5 with
        // derivative 0 and the busy period starts at 5. The next two vehicles wait 7 and 9, with
        // derivatives -(7 + 0 - 5) / 0.5 = -4 and -8. The vehicle at 10 is released at 10.5, before
        // the bottleneck re-opens: it waits 5 + 3 * 2 - 10 = 1, with derivative -3 / 0.5^2 = -12.
        let grid = self::grid(30., 10.);
        let mut curve = self::curve(&[(0., 1.), (0., 1.), (0., 1.), (10., 1.)]);
        curve.push_release(0, s(5.));
        curve.push_release(3, s(10.5));
        compute_waiting_times(
            &curve,
            Some(Flow::new_unchecked(0.5)),
            &grid,
            &mut waiting_times,
        );
        assert_eq!(waiting_times.values.len(), 3);
        let expected = [(7., -4.), (1., -12.), (0., 0.), (0., 0.)];
        for (point, (value, derivative)) in expected.into_iter().enumerate() {
            let (actual_value, actual_derivative) = waiting_times.at(point);
            assert_close(actual_value, value);
            assert_close(actual_derivative, derivative);
        }
    }

    /// Returns the waiting-time function recorded by the within-day model (`WaitXYFBuilder`, then
    /// `TTF::ensure_fifo`), from the arrival time and waiting time of each vehicle (in order).
    fn recorded_function(records: &[(f64, f64)], end: f64, interval: f64) -> PwlTTF<f64> {
        let mut points = Vec::new();
        let mut threshold = interval;
        let mut prev = (0., 0.);
        let mut next = (0., 0.);
        let mut finish_intervals =
            |time: f64, threshold: &mut f64, prev: &mut (f64, f64), next: &mut (f64, f64)| {
                while time > *threshold {
                    points.push(if prev.1 == 0. { 0. } else { prev.0 / prev.1 });
                    *prev = *next;
                    *next = (0., 0.);
                    *threshold += interval;
                }
            };
        for &(time, wait) in records.iter().filter(|&&(t, _)| t <= end) {
            finish_intervals(time, &mut threshold, &mut prev, &mut next);
            let alpha = (threshold - time) / interval;
            prev.0 += wait * alpha;
            prev.1 += alpha;
            next.0 += wait * (1. - alpha);
            next.1 += 1. - alpha;
        }
        finish_intervals(end + 2. * interval, &mut threshold, &mut prev, &mut next);
        let mut function = PwlTTF::from_values(points, 0., interval);
        function.ensure_fifo();
        function
    }

    #[test]
    fn entry_brute_force_test() {
        // Vehicles with various PCE, some arriving at the same time, then three vehicles after the
        // end of the period. With spillback, one vehicle in ten is released up to 40 s after its
        // arrival (binding or not).
        let draws = pseudo_random(3 * 300);
        let mut arrivals = Vec::with_capacity(303);
        let mut releases = Vec::new();
        let mut time = 5.0;
        for (i, d) in draws.chunks(3).enumerate() {
            arrivals.push((time, [0.5, 1., 2.][(d[1] * 3.) as usize]));
            if d[2] < 0.1 {
                releases.push((i, time + 400. * d[2]));
            }
            if d[0] >= 0.1 {
                time += 3. * d[0];
            }
        }
        arrivals.extend([(650., 1.), (700., 1.), (720., 1.)]);
        assert!(arrivals.windows(2).any(|w| w[0].0 == w[1].0));
        let (end, interval) = (600., 30.);
        let grid = grid(end, interval);
        let mut probes: Vec<f64> = (0..=50).map(|i| 15. * i as f64).collect();
        probes.extend(arrivals.iter().map(|&(t, _)| t));
        let mut waiting_times = WaitingTimes::default();
        for spillback in [false, true] {
            let mut curve = curve(&arrivals);
            let mut release_of = vec![0.; arrivals.len()];
            if spillback {
                for &(i, release) in releases.iter() {
                    curve.push_release(i, s(release));
                    release_of[i] = release;
                }
            }
            for flow in [Some(0.3), Some(0.7), Some(1.5), None] {
                // Vehicle-by-vehicle FIFO bottleneck, closed for `pce / flow` after each crossing,
                // which a vehicle crosses at the earliest at its release.
                let mut open_time = 0.0f64;
                let records: Vec<_> = arrivals
                    .iter()
                    .zip(release_of.iter())
                    .map(|(&(t, pce), &release)| {
                        let crossing = t.max(open_time).max(release);
                        open_time = crossing + flow.map_or(0., |f| pce / f);
                        (t, crossing - t)
                    })
                    .collect();
                let function = recorded_function(&records, end, interval);
                let flow = flow.map(Flow::new_unchecked);
                compute_waiting_times(&curve, flow, &grid, &mut waiting_times);
                if flow == Some(Flow::new_unchecked(0.3)) {
                    // The queue does not clear before the end of the period.
                    assert!(waiting_times.at(grid.nb_points - 1).0 > 0.);
                }
                if spillback && flow.is_none() {
                    // The vehicles only wait for space.
                    assert!(waiting_times.values.iter().any(|&w| w > 0.));
                }
                for &t in probes.iter() {
                    let expected = t + function.eval(t);
                    let predicted = f64::from(entry(&waiting_times, &grid, s(t)).time);
                    assert!(
                        (predicted - expected).abs() <= 1e-9 * expected.max(1.),
                        "Spillback {spillback}, flow {flow:?}, probe at {t}: \
                        {predicted} != {expected}"
                    );
                }
            }
        }
    }

    fn edge(id: i64, length: f64, lanes: f64, flow: Option<f64>) -> RoadEdge {
        RoadEdge::new(
            id,
            MetersPerSecond::new_unchecked(1.),
            NonNegativeMeters::new_unchecked(length),
            Lanes::new_unchecked(lanes),
            SpeedDensityFunction::FreeFlow,
            flow.map(FlowPerLane::new_unchecked),
            NonNegativeSeconds::ZERO,
            true,
        )
    }

    #[test]
    fn predict_test() {
        // Edge 0: calibrated, 2 lanes, free-flow travel time 10.
        // Edge 1: not calibrated, total flow 0.5, free-flow travel time 5.
        // Edge 2: not calibrated, infinite flow (no curve), free-flow travel time 3.
        let e0 = edge(0, 10., 2., None);
        let e1 = edge(1, 5., 2., Some(0.25));
        let e2 = edge(2, 3., 1., None);
        let edges = [&e0, &e1, &e2];
        // Capacity 1, so that the factor is the capacity of edge 0.
        let factors = test_factors(1, &[Some(&[0]), None, None]);
        // Arrivals at breakpoints only (every 10 s), so each waiting time has a single weight.
        // Edge 1: waiting times 0 at 20 and 6 * 2 - 10 = 2 at 30.
        let curves: ArrivalCurves = vec![
            Some(curve(&[(0., 12.), (10., 1.), (20., 1.)])),
            Some(curve(&[(20., 6.), (30., 1.)])),
            None,
        ]
        .into_iter()
        .collect();
        let vehicle = Vehicle::new(
            1,
            NonNegativeMeters::ZERO,
            PCE::ONE,
            SpeedFunction::Base,
            HashSet::default(),
            HashSet::default(),
        );
        let path = |ids: &[usize]| ids.iter().map(|&i| EdgeIndex::new(i)).collect();
        let routes = vec![
            (s(5.), path(&[0, 1, 2])),
            (s(30.), path(&[1, 2])),
            (s(0.), path(&[2])),
        ];
        let mut surrogate =
            Surrogate::new(curves, &edges, &factors, &vehicle, routes, grid(100., 10.));
        let capacity = |c: f64| [c];
        let assert_delays = |delays: Vec<NonNegativeSeconds>, expected: [f64; 3]| {
            for (d, e) in delays.into_iter().zip(expected) {
                assert_close(f64::from(d), e);
            }
        };
        // Flow 0.5 on edge 0: waiting times 0 at 0, 24 - 10 = 14 at 10 and 14 + 2 - 10 = 6 at 20.
        // The probe waits 7 at 5 and reaches edge 1 at 22, where it waits 0.2 * 2 = 0.4.
        assert_delays(surrogate.predict(&capacity(0.25)), [7.4, 2., 0.]);
        // Jacobian: at edge 0, the derivative of the waiting time at 10 is -(14 + 10) / 0.5 = -48,
        // so the probe at 5 gets -24, i.e., -48 per unit of capacity (2 lanes); at edge 1, the
        // slope of the waiting time is 0.2, so dE/dt = 1.2.
        let (delays, jacobian) = surrogate.predict_with_jacobian(&capacity(0.25));
        assert_delays(delays, [7.4, 2., 0.]);
        assert_close(jacobian[0], -57.6);
        assert_eq!(&jacobian[1..], &[0., 0.]);
        // Flow 0.25 on edge 0: waiting time 48 - 10 = 38 at 10. The probe waits 19 at 5 and
        // reaches edge 1 at 34, where it waits 0.6 * 2 = 1.2.
        assert_delays(surrogate.predict(&capacity(0.125)), [20.2, 2., 0.]);
        // Flow 1 on edge 0: waiting time 12 - 10 = 2 at 10. The probe waits 1 at 5 and reaches
        // edge 1 at 16, before its first arrival.
        assert_delays(surrogate.predict(&capacity(0.5)), [1., 2., 0.]);
    }

    /// Returns [CapacityFactors] with a capacity of 1 PCE/s per lane, `nb_factors` factors
    /// (initial value 1, no bounds) and the given factors of each edge (`None` if the edge is not
    /// calibrated).
    fn test_factors(nb_factors: usize, edge_factors: &[Option<&[usize]>]) -> CapacityFactors {
        let mut combinations: Vec<Vec<usize>> = Vec::new();
        let edge_combinations = edge_factors
            .iter()
            .map(|factors| {
                factors.map(|factors| {
                    combinations
                        .iter()
                        .position(|c| c == factors)
                        .unwrap_or_else(|| {
                            combinations.push(factors.to_vec());
                            combinations.len() - 1
                        })
                })
            })
            .collect();
        CapacityFactors {
            capacity: FlowPerLane::new_unchecked(1.),
            ids: (0..nb_factors)
                .map(|j| MetroId::from(format!("f{j}").as_str()))
                .collect(),
            initial: vec![1.; nb_factors],
            min: vec![None; nb_factors],
            max: vec![None; nb_factors],
            combinations,
            edge_combinations,
        }
    }

    /// Returns a surrogate model with pseudo-random arrival curves (about 0.5 PCE/s at each edge)
    /// at 3 edges (edge 0: 1 lane; edge 1: 2 lanes; edge 2: not calibrated) and 60 probes with
    /// paths through the 3 edges, given the number of factors and the factors of edges 0 and 1
    /// (with a capacity of 1 PCE/s per lane).
    /// With spillback, one vehicle in 20 is released 60 s after its arrival and the edge 2 has an
    /// infinite flow (its vehicles only wait for space).
    fn random_surrogate(
        nb_factors: usize,
        edge_factors: [&[usize]; 2],
        spillback: bool,
    ) -> Surrogate {
        let e0 = edge(0, 20., 1., None);
        let e1 = edge(1, 20., 2., None);
        let e2 = edge(2, 20., 1., if spillback { None } else { Some(0.5) });
        let edges = [&e0, &e1, &e2];
        let factors = test_factors(
            nb_factors,
            &[Some(edge_factors[0]), Some(edge_factors[1]), None],
        );
        // Random arrivals of about 0.5 PCE/s at each edge.
        let draws = pseudo_random(3 * 2 * 1000 + 2 * 60);
        let (curve_draws, probe_draws) = draws.split_at(3 * 2 * 1000);
        let curves: ArrivalCurves = curve_draws
            .chunks(2 * 1000)
            .map(|d| {
                let mut time = 0.;
                let arrivals: Vec<_> = d
                    .chunks(2)
                    .map(|d| {
                        time += 4. * d[0];
                        (time, [0.5, 1., 2.][(d[1] * 3.) as usize])
                    })
                    .collect();
                let mut curve = curve(&arrivals);
                if spillback {
                    for (i, &(t, _)) in arrivals.iter().enumerate().step_by(20) {
                        curve.push_release(i, s(t + 60.));
                    }
                }
                Some(curve)
            })
            .collect();
        let vehicle = Vehicle::new(
            1,
            NonNegativeMeters::ZERO,
            PCE::ONE,
            SpeedFunction::Base,
            HashSet::default(),
            HashSet::default(),
        );
        let paths = [[0, 1, 2], [1, 0, 2], [2, 0, 1], [2, 1, 0]];
        let routes: Vec<_> = probe_draws
            .chunks(2)
            .map(|d| {
                let path = paths[(d[1] * 4.) as usize]
                    .iter()
                    .map(|&i| EdgeIndex::new(i))
                    .collect();
                (s(1800. * d[0]), path)
            })
            .collect();
        Surrogate::new(curves, &edges, &factors, &vehicle, routes, grid(3600., 60.))
    }

    #[test]
    fn jacobian_test() {
        for spillback in [false, true] {
            // One factor per edge: the factors are the capacities.
            jacobian_check(
                random_surrogate(2, [&[0], &[1]], spillback),
                &[[0.5, 0.25], [0.4, 0.3], [0.6, 0.2]],
            );
            // A factor shared by the two edges and a factor of edge 1 only (capacity of edge 1:
            // 0.25, 0.3 and 0.24).
            jacobian_check(
                random_surrogate(2, [&[0], &[0, 1]], spillback),
                &[[0.5, 0.5], [0.4, 0.75], [0.6, 0.4]],
            );
        }
    }

    /// Checks the Jacobian of the surrogate (with 2 factors) against finite differences, at the
    /// given values of the factors.
    fn jacobian_check(mut surrogate: Surrogate, values: &[[f64; 2]]) {
        let delays = |surrogate: &mut Surrogate, values: &[f64]| -> Vec<f64> {
            surrogate
                .predict(values)
                .into_iter()
                .map(f64::from)
                .collect()
        };
        for &values in values {
            let (predicted, jacobian) = surrogate.predict_with_jacobian(&values);
            let predicted: Vec<f64> = predicted.into_iter().map(f64::from).collect();
            assert_eq!(predicted, delays(&mut surrogate, &values));
            let mut nb_checked = 0;
            let mut nb_non_zero = 0;
            for j in 0..2 {
                let h = 1e-6 * values[j];
                let mut shifted = values;
                shifted[j] += h;
                let up = delays(&mut surrogate, &shifted);
                shifted[j] -= 2. * h;
                let down = delays(&mut surrogate, &shifted);
                for n in 0..predicted.len() {
                    let forward = (up[n] - predicted[n]) / h;
                    let backward = (predicted[n] - down[n]) / h;
                    if (forward - backward).abs() > 1e-3 * forward.abs().max(1.) {
                        // Kink between the two sides.
                        continue;
                    }
                    nb_checked += 1;
                    let central = (forward + backward) / 2.;
                    let analytic = jacobian[2 * n + j];
                    if analytic != 0. {
                        nb_non_zero += 1;
                    }
                    assert!(
                        (analytic - central).abs() <= 1e-4 * central.abs() + 1e-3,
                        "Factors {values:?}, route {n}, factor {j}: {analytic} != {central}"
                    );
                }
            }
            assert!(nb_checked >= 2 * predicted.len() * 9 / 10);
            assert!(nb_non_zero >= predicted.len() / 2);
        }
    }

    #[test]
    fn recover_factors_test() {
        // The target delays are the predicted delays at some factors, which the optimization must
        // recover from other initial factors, with one factor per edge or with a shared factor.
        for (edge_factors, truth, start) in [
            ([&[0][..], &[1][..]], [0.4, 0.3], [0.44, 0.27]),
            ([&[0][..], &[0, 1][..]], [0.4, 0.75], [0.44, 0.65]),
        ] {
            let mut day = random_surrogate(2, edge_factors, false);
            let target_delays = day.predict(&truth);
            let mut surrogate = MeanSurrogate::new(day);
            let mut factors = test_factors(2, &[Some(edge_factors[0]), Some(edge_factors[1])]);
            factors.initial = start.to_vec();
            let optimized = optimize_factors(
                &mut surrogate,
                &target_delays,
                &start,
                0.2,
                &OptimizerParameters::default(),
                &factors,
            );
            for (&f, expected) in optimized.iter().zip(truth) {
                assert!((f / expected - 1.).abs() < 1e-3, "{f} != {expected}");
            }
        }
        let mut day = random_surrogate(2, [&[0], &[1]], false);
        let target_delays = day.predict(&[0.4, 0.3]);
        let mut surrogate = MeanSurrogate::new(day);
        let mut factors = test_factors(2, &[Some(&[0]), Some(&[1])]);
        factors.initial = vec![0.44, 0.27];
        let mut optimize = |start: &[f64], factors: &CapacityFactors| {
            optimize_factors(
                &mut surrogate,
                &target_delays,
                start,
                0.2,
                &OptimizerParameters::default(),
                factors,
            )
        };
        // With a maximum of 0.28 for factor 1, it stops exactly at that bound, also when the
        // optimization starts from that bound.
        factors.max[1] = Some(0.28);
        let optimized = optimize(&factors.initial, &factors);
        assert_eq!(optimized[1], 0.28);
        let optimized = optimize(&optimized, &factors);
        assert_eq!(optimized[1], 0.28);
        // Same with a minimum of 0.42 for factor 0.
        factors.min[0] = Some(0.42);
        let optimized = optimize(&factors.initial, &factors);
        assert_eq!(optimized[0], 0.42);
        let optimized = optimize(&optimized, &factors);
        assert_eq!(optimized[0], 0.42);
    }

    #[test]
    fn uncrossed_factor_test() {
        // The edges of factor 1 are crossed by no target route: with a penalty, it stays the same
        // (instead of decreasing to the trust-region bound).
        let mut day = random_surrogate(2, [&[0], &[0]], false);
        let start = [0.4, 0.3];
        let target_delays = day.predict(&start);
        let mut surrogate = MeanSurrogate::new(day);
        assert_eq!(surrogate.crossed_factors(), vec![true, false]);
        let mut factors = test_factors(2, &[Some(&[0]), Some(&[0])]);
        factors.initial = start.to_vec();
        let params = OptimizerParameters {
            penalty: 0.01,
            ..Default::default()
        };
        let optimized = optimize_factors(
            &mut surrogate,
            &target_delays,
            &start,
            0.2,
            &params,
            &factors,
        );
        assert_eq!(optimized[1], start[1]);
    }

    #[test]
    fn mean_surrogate_test() {
        let capacities = [0.4, 0.3];
        let to_f64 = |delays: Vec<NonNegativeSeconds>| -> Vec<f64> {
            delays.into_iter().map(f64::from).collect()
        };
        // A single day: the mean surrogate model is the surrogate model of the day.
        let mut day = random_surrogate(2, [&[0], &[1]], false);
        let mut single = MeanSurrogate::new(day.clone());
        assert_eq!(
            single.predict_with_jacobian(&capacities),
            day.predict_with_jacobian(&capacities)
        );
        // Two days (with different factors, so that their predictions differ): the mean of their
        // delays and Jacobian matrices.
        let mut other = random_surrogate(2, [&[1], &[0]], false);
        let (delays_0, jacobian_0) = day.predict_with_jacobian(&capacities);
        let (delays_1, jacobian_1) = other.predict_with_jacobian(&capacities);
        let (delays_0, delays_1) = (to_f64(delays_0), to_f64(delays_1));
        assert_ne!(delays_0, delays_1);
        let mut two = MeanSurrogate::new(day.clone());
        two.push(other.clone(), 2);
        assert_eq!(two.len(), 2);
        let (delays, jacobian) = two.predict_with_jacobian(&capacities);
        let delays = to_f64(delays);
        for (n, &d) in delays.iter().enumerate() {
            assert_close(d, (delays_0[n] + delays_1[n]) / 2.);
        }
        for (i, &d) in jacobian.iter().enumerate() {
            assert_close(d, (jacobian_0[i] + jacobian_1[i]) / 2.);
        }
        // The predictions of each day, from the oldest to the newest.
        let days: Vec<_> = two
            .predict_days(&capacities)
            .into_iter()
            .map(to_f64)
            .collect();
        assert_eq!(days, vec![delays_0, delays_1.clone()]);
        // Beyond `max_days`, the oldest days are dropped.
        two.push(other.clone(), 2);
        assert_eq!(two.len(), 2);
        let days: Vec<_> = two
            .predict_days(&capacities)
            .into_iter()
            .map(to_f64)
            .collect();
        assert_eq!(days, vec![delays_1.clone(), delays_1]);
        let mut one = MeanSurrogate::new(day);
        one.push(other, 1);
        assert_eq!(one.len(), 1);
        assert_eq!(one.predict_with_jacobian(&capacities).1, jacobian_1);
        // A factor is crossed if it is crossed on some day.
        let mut two = MeanSurrogate::new(random_surrogate(2, [&[0], &[0]], false));
        two.push(random_surrogate(2, [&[1], &[1]], false), 2);
        assert_eq!(two.crossed_factors(), vec![true, true]);
    }
}
