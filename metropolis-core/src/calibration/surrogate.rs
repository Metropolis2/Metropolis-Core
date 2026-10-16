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
//! The entry bottleneck of an edge is a fluid FIFO queue, served at the flow of the bottleneck.
//! The recorded arrival curves are made piecewise linear: the PCE of the vehicles arrived at a time
//! of the curve is spread uniformly over the interval since the previous time of the curve (the
//! PCE of the first time is spread over an infinite interval, so the queue is empty at the first
//! time). A target route (probe) reaching a bottleneck at a given time crosses it when the queue
//! at that time has been served, but it does not add any traffic.
use num_traits::ConstZero;
use petgraph::graph::EdgeIndex;
use rayon::prelude::*;

use super::EdgeCategories;
use crate::network::road_network::arrival_curve::{ArrivalCurve, ArrivalCurves};
use crate::network::road_network::vehicle::Vehicle;
use crate::network::road_network::RoadEdge;
use crate::units::*;

/// Total flow of a bottleneck of the surrogate model.
#[derive(Clone, Copy, Debug)]
enum Capacity {
    /// Calibrated edge: the total flow is the capacity of the category times the number of lanes.
    Calibrated { category: usize, lanes: Lanes },
    /// Edge that is not calibrated, with a constant (finite) input flow.
    Fixed(Flow),
}

/// Entry bottleneck of an edge of the target routes, with its recorded arrival curve.
#[derive(Clone, Debug)]
struct Bottleneck {
    curve: ArrivalCurve,
    capacity: Capacity,
    /// Queue (in PCE) at each time of the arrival curve, for the current flow.
    queues: Vec<PCE>,
}

impl Bottleneck {
    /// Creates a new [Bottleneck] (the queues of a [Capacity::Fixed] bottleneck are computed once,
    /// here).
    fn new(curve: ArrivalCurve, capacity: Capacity) -> Self {
        let mut bottleneck = Self {
            curve,
            capacity,
            queues: Vec::new(),
        };
        if let Capacity::Fixed(flow) = capacity {
            compute_queues(&bottleneck.curve, flow, &mut bottleneck.queues);
        }
        bottleneck
    }

    /// Returns the total flow of the bottleneck, given the capacity of each category.
    fn flow(&self, capacities: &[FlowPerLane]) -> Flow {
        match self.capacity {
            // Same operation as in `BottleneckFlows::from_capacities`.
            Capacity::Calibrated { category, lanes } => capacities[category] * lanes,
            Capacity::Fixed(flow) => flow,
        }
    }

    /// Updates the queues of a [Capacity::Calibrated] bottleneck for the given capacity of each
    /// category.
    fn update(&mut self, capacities: &[FlowPerLane]) {
        if matches!(self.capacity, Capacity::Calibrated { .. }) {
            let flow = self.flow(capacities);
            compute_queues(&self.curve, flow, &mut self.queues);
        }
    }

    /// Returns the time at which a probe reaching the bottleneck at the given time crosses it,
    /// given the capacity of each category.
    fn entry_time(
        &self,
        time: NonNegativeSeconds,
        capacities: &[FlowPerLane],
    ) -> NonNegativeSeconds {
        entry_time(&self.curve, &self.queues, self.flow(capacities), time)
    }
}

/// Returns the queue at the end of an interval, given the queue at its start, the PCE arrived and
/// the PCE that the bottleneck can serve during the interval, when the arrival rate is constant
/// over the interval.
fn queue_after(queue: PCE, inflow: PCE, outflow: PCE) -> PCE {
    let total = queue + inflow;
    if total > outflow {
        total.sub_unchecked(outflow)
    } else {
        PCE::ZERO
    }
}

/// Computes the queue of a bottleneck with the given flow at each time of the arrival curve.
fn compute_queues(curve: &ArrivalCurve, flow: Flow, queues: &mut Vec<PCE>) {
    queues.clear();
    queues.reserve(curve.len());
    let times = curve.times();
    let pce = curve.pce();
    let mut queue = PCE::ZERO;
    for k in 0..curve.len() {
        if k > 0 {
            let outflow = flow * times[k].sub_unchecked(times[k - 1]);
            queue = queue_after(queue, pce[k], outflow);
        }
        queues.push(queue);
    }
}

/// Returns the time at which a probe reaching a bottleneck at the given time crosses it, given the
/// arrival curve, the queues and the flow of the bottleneck.
fn entry_time(
    curve: &ArrivalCurve,
    queues: &[PCE],
    flow: Flow,
    time: NonNegativeSeconds,
) -> NonNegativeSeconds {
    let times = curve.times();
    // Number of times of the curve before or at the probe.
    let k = times.partition_point(|&t| t <= time);
    if k == 0 {
        return time;
    }
    let elapsed = time.sub_unchecked(times[k - 1]);
    let inflow = if k < times.len() {
        // The interval is not empty as `times[k - 1] <= time < times[k]`.
        let rate = curve.pce()[k] / times[k].sub_unchecked(times[k - 1]);
        rate * elapsed
    } else {
        // No arrival after the last time of the curve.
        PCE::ZERO
    };
    let queue = queue_after(queues[k - 1], inflow, flow * elapsed);
    time + queue / flow
}

/// Edge of the path of a probe.
#[derive(Clone, Debug)]
struct ProbeEdge {
    /// Free-flow travel time of the edge, for the vehicle type of the calibration.
    free_flow_tt: NonNegativeSeconds,
    /// Index of the entry bottleneck of the edge in the surrogate model (`None` if the edge has no
    /// arrival curve, i.e., its flow is infinite).
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
    fn delay(&self, bottlenecks: &[Bottleneck], capacities: &[FlowPerLane]) -> NonNegativeSeconds {
        let mut time = self.departure_time;
        let mut delay = NonNegativeSeconds::ZERO;
        for edge in self.path.iter() {
            if let Some(i) = edge.bottleneck {
                let entry_time = bottlenecks[i].entry_time(time, capacities);
                delay += entry_time.sub_unchecked(time);
                time = entry_time;
            }
            time += edge.free_flow_tt;
        }
        delay
    }
}

/// Surrogate model predicting the queueing delays of the target routes for any capacities, from
/// the arrival curves recorded during a simulated day.
#[derive(Clone, Debug)]
pub(crate) struct Surrogate {
    bottlenecks: Vec<Bottleneck>,
    probes: Vec<Probe>,
}

impl Surrogate {
    /// Creates the [Surrogate] from the arrival curves (indexed by `EdgeIndex`), the edges of the
    /// road network (ordered by `EdgeIndex`), the edge categories, the vehicle type of the
    /// calibration and the target routes (departure time and path).
    pub(crate) fn new(
        curves: ArrivalCurves,
        edges: &[&RoadEdge],
        categories: &EdgeCategories,
        vehicle: &Vehicle,
        routes: impl IntoIterator<Item = (NonNegativeSeconds, Vec<EdgeIndex>)>,
    ) -> Self {
        let mut bottleneck_of = vec![None; edges.len()];
        let mut bottlenecks = Vec::new();
        for (i, curve) in curves.into_iter().enumerate() {
            let Some(curve) = curve else {
                continue;
            };
            let edge = edges[i];
            let capacity = match categories.category_of(EdgeIndex::new(i)) {
                Some(category) => Capacity::Calibrated {
                    category,
                    lanes: edge.lanes(),
                },
                None => Capacity::Fixed(
                    edge.constant_bottleneck_flow()
                        .expect("Arrival curves are only recorded at edges with a finite flow"),
                ),
            };
            bottleneck_of[i] = Some(bottlenecks.len());
            bottlenecks.push(Bottleneck::new(curve, capacity));
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
        }
    }

    /// Returns the predicted queueing delay of each target route (in the order of the routes),
    /// given the capacity of each category.
    pub(crate) fn predict(&mut self, capacities: &[FlowPerLane]) -> Vec<NonNegativeSeconds> {
        self.bottlenecks
            .par_iter_mut()
            .for_each(|b| b.update(capacities));
        let bottlenecks = &self.bottlenecks;
        self.probes
            .par_iter()
            .map(|p| p.delay(bottlenecks, capacities))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use num_traits::ConstOne;

    use super::*;
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

    #[test]
    fn entry_time_test() {
        let curve = curve(&[(0., 1.), (1., 1.), (2., 1.), (10., 1.)]);
        let flow = Flow::new_unchecked(0.5);
        let mut queues = Vec::new();
        compute_queues(&curve, flow, &mut queues);
        let pce = PCE::new_unchecked;
        assert_eq!(queues, vec![pce(0.), pce(0.5), pce(1.), pce(0.)]);
        let entry = |t: f64| f64::from(entry_time(&curve, &queues, flow, s(t)));
        // The queue is empty at the first time of the curve.
        assert_eq!(entry(0.), 0.);
        // Queue 0.5 at 1, plus 0.5 arrived, minus 0.25 served.
        assert_eq!(entry(1.5), 3.);
        assert_eq!(entry(2.), 4.);
        // Queue 1 at 2, plus 0.25 arrived, minus 1 served.
        assert_eq!(entry(4.), 4.5);
        // The queue is empty.
        assert_eq!(entry(5.), 5.);
        // After the last time of the curve.
        assert_eq!(entry(11.), 11.);
        // The entry time is continuous.
        assert!((entry(2. - 1e-9) - 4.).abs() < 1e-6);
        assert!((entry(2. + 1e-9) - 4.).abs() < 1e-6);

        // The vehicles arrived at the same time are spread over the interval since the previous
        // time of the curve.
        let curve = self::curve(&[(0., 1.), (2., 1.), (2., 3.)]);
        let flow = Flow::new_unchecked(1.);
        compute_queues(&curve, flow, &mut queues);
        assert_eq!(queues, vec![pce(0.), pce(2.)]);
        assert_eq!(entry_time(&curve, &queues, flow, s(1.)), s(2.));
        assert_eq!(entry_time(&curve, &queues, flow, s(2.)), s(4.));
        assert_eq!(entry_time(&curve, &queues, flow, s(3.)), s(4.));
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

    #[test]
    fn entry_time_brute_force_test() {
        // Vehicles with various PCE, some arriving at the same time.
        let draws = pseudo_random(2 * 500);
        let mut arrivals = Vec::with_capacity(500);
        let mut time = 5.0;
        for d in draws.chunks(2) {
            if d[0] >= 0.1 {
                time += 3. * d[0];
            }
            let pce = [0.5, 1., 2.][(d[1] * 3.) as usize];
            arrivals.push((time, pce));
        }
        let curve = curve(&arrivals);
        assert!(curve.len() < arrivals.len());
        let times: Vec<f64> = curve.times().iter().map(|&t| f64::from(t)).collect();
        let cumulative_pce: Vec<f64> = curve
            .pce()
            .iter()
            .scan(0., |total, &p| {
                *total += f64::from(p);
                Some(*total)
            })
            .collect();
        let last = *times.last().unwrap();
        // Piecewise-linear arrival curve.
        let arrival_curve = |t: f64| {
            let k = times.partition_point(|&s| s <= t);
            if k == times.len() {
                cumulative_pce[k - 1]
            } else {
                let rate = (cumulative_pce[k] - cumulative_pce[k - 1]) / (times[k] - times[k - 1]);
                cumulative_pce[k - 1] + rate * (t - times[k - 1])
            }
        };
        let mut probes = vec![0., last + 1., last + 100.];
        probes.extend(times.iter());
        probes.extend(times.windows(2).map(|w| (w[0] + w[1]) / 2.));
        let mut queues = Vec::new();
        for flow in [0.3, 0.7, 1.5] {
            compute_queues(&curve, Flow::new_unchecked(flow), &mut queues);
            for &t in probes.iter() {
                // Queue from the departure curve D(t) = min_{u <= t} A(u) + s (t - u), where the
                // minimum is reached at a time of the curve or at t (the queue is empty at the
                // first time).
                let queue = times
                    .iter()
                    .zip(cumulative_pce.iter())
                    .take_while(|&(&s, _)| s <= t)
                    .map(|(&s, &a)| arrival_curve(t) - a - flow * (t - s))
                    .fold(0.0f64, f64::max);
                let expected = t + queue / flow;
                let predicted =
                    f64::from(entry_time(&curve, &queues, Flow::new_unchecked(flow), s(t)));
                assert!(
                    (predicted - expected).abs() < 1e-9,
                    "Flow {flow}, probe at {t}: {predicted} != {expected}"
                );
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
        let categories = EdgeCategories {
            ids: vec![Some(MetroId::from("a"))],
            initial_capacities: vec![FlowPerLane::new_unchecked(0.25)],
            edge_categories: vec![Some(0), None, None],
        };
        // Queues at edge 1: 0, 1, 2 and 2 at times 10, 12, 16 and 20.
        let curves: ArrivalCurves = vec![
            Some(curve(&[(0., 1.), (1., 1.), (2., 1.)])),
            Some(curve(&[(10., 1.), (12., 2.), (16., 3.), (20., 2.)])),
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
            // The probe reaches edge 0 at the last time of its curve.
            (s(2.), path(&[0, 1, 2])),
            // The probe arrives after the queue of edge 1 has cleared.
            (s(30.), path(&[1, 2])),
            (s(0.), path(&[2])),
        ];
        let mut surrogate = Surrogate::new(curves, &edges, &categories, &vehicle, routes);
        let capacity = |c: f64| FlowPerLane::new_unchecked(c);
        // Flow 0.5 on edge 0: queue 1, the probe enters edge 0 at 4 (delay 2). It reaches edge 1
        // at 14 (queue 1 at 12, plus 1.5 arrived, minus 1 served) and enters it at 17 (delay 3).
        assert_eq!(
            surrogate.predict(&[capacity(0.25)]),
            vec![s(5.), s(0.), s(0.)]
        );
        // Flow 0.25 on edge 0: queue 1.5, the probe enters edge 0 at 8 (delay 6). It reaches
        // edge 1 at 18 (queue 2 at 16, plus 1 arrived, minus 1 served) and enters it at 22 (delay
        // 4).
        assert_eq!(
            surrogate.predict(&[capacity(0.125)]),
            vec![s(10.), s(0.), s(0.)]
        );
        // Flow 1 on edge 0: no queue on edge 0, the probe reaches edge 1 at 12 (queue 1) and
        // enters it at 14 (delay 2).
        assert_eq!(
            surrogate.predict(&[capacity(0.5)]),
            vec![s(2.), s(0.), s(0.)]
        );
    }
}
