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
//! The entry bottleneck of an edge is a FIFO queue with the same rule as in the within-day model:
//! a vehicle crosses the bottleneck when it reaches it or, if the bottleneck is closed, when it
//! re-opens; the bottleneck then closes for `pce / flow` seconds. A target route (probe) waits
//! behind the vehicles that reached the bottleneck strictly before it, but it does not add any
//! traffic.
use num_traits::ConstZero;
use petgraph::graph::EdgeIndex;
use rayon::prelude::*;

use super::EdgeCategories;
use crate::network::road_network::arrival_curve::{ArrivalCurve, ArrivalCurves};
use crate::network::road_network::vehicle::Vehicle;
use crate::network::road_network::RoadEdge;
use crate::units::*;

/// Tolerance, in seconds, when comparing the time at which a probe reaches a bottleneck with the
/// arrival times of the curve: the vehicles arriving at the same time as the probe (within the
/// tolerance) are not ahead of it.
const TIE_TOLERANCE: f64 = 1e-6;

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
    /// Time at which the bottleneck re-opens after the vehicles arrived up to each arrival time of
    /// the curve, for the current flow.
    release_times: Vec<NonNegativeSeconds>,
}

impl Bottleneck {
    /// Creates a new [Bottleneck] (the release times of a [Capacity::Fixed] bottleneck are
    /// computed once, here).
    fn new(curve: ArrivalCurve, capacity: Capacity) -> Self {
        let mut bottleneck = Self {
            curve,
            capacity,
            release_times: Vec::new(),
        };
        if let Capacity::Fixed(flow) = capacity {
            compute_release_times(&bottleneck.curve, flow, &mut bottleneck.release_times);
        }
        bottleneck
    }

    /// Updates the release times of a [Capacity::Calibrated] bottleneck for the given capacity of
    /// each category.
    fn update(&mut self, capacities: &[FlowPerLane]) {
        if let Capacity::Calibrated { category, lanes } = self.capacity {
            // Same operation as in `BottleneckFlows::from_capacities`.
            let flow = capacities[category] * lanes;
            compute_release_times(&self.curve, flow, &mut self.release_times);
        }
    }

    /// Returns the time at which a probe reaching the bottleneck at the given time crosses it.
    fn entry_time(&self, time: NonNegativeSeconds) -> NonNegativeSeconds {
        entry_time(&self.curve, &self.release_times, time)
    }
}

/// Computes, for each arrival time of the curve, the time at which a bottleneck with the given
/// flow re-opens after letting pass all the vehicles arrived up to that time.
///
/// The vehicles arrived at the same time cross the bottleneck when it re-opens after the previous
/// vehicles (or when they arrive if it is open), then it closes for their total service time.
fn compute_release_times(
    curve: &ArrivalCurve,
    flow: Flow,
    release_times: &mut Vec<NonNegativeSeconds>,
) {
    release_times.clear();
    release_times.reserve(curve.len());
    let mut previous_pce = PCE::ZERO;
    let mut release_time = NonNegativeSeconds::ZERO;
    for (&time, &pce) in curve.times().iter().zip(curve.cumulative_pce()) {
        // Same operation as in the within-day model (`Bottleneck::get_closing_time`).
        release_time = time.max(release_time) + pce.sub_unchecked(previous_pce) / flow;
        release_times.push(release_time);
        previous_pce = pce;
    }
}

/// Returns the time at which a probe reaching a bottleneck at the given time crosses it, given the
/// arrival curve and the release times of the bottleneck.
fn entry_time(
    curve: &ArrivalCurve,
    release_times: &[NonNegativeSeconds],
    time: NonNegativeSeconds,
) -> NonNegativeSeconds {
    let threshold = f64::from(time) - TIE_TOLERANCE;
    // Number of arrival times strictly before the probe.
    let nb_ahead = curve.times().partition_point(|&t| f64::from(t) < threshold);
    if nb_ahead == 0 {
        time
    } else {
        time.max(release_times[nb_ahead - 1])
    }
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
    fn delay(&self, bottlenecks: &[Bottleneck]) -> NonNegativeSeconds {
        let mut time = self.departure_time;
        let mut delay = NonNegativeSeconds::ZERO;
        for edge in self.path.iter() {
            if let Some(i) = edge.bottleneck {
                let entry_time = bottlenecks[i].entry_time(time);
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
            .map(|p| p.delay(bottlenecks))
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
        let mut release_times = Vec::new();
        compute_release_times(&curve, Flow::new_unchecked(0.5), &mut release_times);
        assert_eq!(release_times, vec![s(2.), s(4.), s(6.), s(12.)]);
        let entry = |t: f64| entry_time(&curve, &release_times, s(t));
        // Before the first arrival: no queue.
        assert_eq!(entry(0.), s(0.));
        // Behind the vehicles arrived at 0 and 1.
        assert_eq!(entry(1.5), s(4.));
        assert_eq!(entry(5.), s(6.));
        // The queue is empty.
        assert_eq!(entry(7.), s(7.));
        assert_eq!(entry(11.), s(12.));
        // Same time as the vehicle arrived at 1 (up to rounding): it is not ahead of the probe,
        // which crosses the bottleneck at the same time as that vehicle in the simulation.
        assert_eq!(entry(1.), s(2.));
        assert_eq!(entry(1. + 1e-9), s(2.));
        assert_eq!(entry(1. - 1e-9), s(2.));

        // Simultaneous arrivals are served as a group.
        let curve = self::curve(&[(0., 1.), (0., 2.), (1., 0.5)]);
        compute_release_times(&curve, Flow::new_unchecked(1.), &mut release_times);
        assert_eq!(release_times, vec![s(3.), s(3.5)]);
        assert_eq!(entry_time(&curve, &release_times, s(1.)), s(3.));
        assert_eq!(entry_time(&curve, &release_times, s(2.)), s(3.5));
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
        let mut time = 0.0;
        for d in draws.chunks(2) {
            if d[0] >= 0.1 {
                time += 3. * d[0];
            }
            let pce = [0.5, 1., 2.][(d[1] * 3.) as usize];
            arrivals.push((time, pce));
        }
        let curve = curve(&arrivals);
        assert!(curve.len() < arrivals.len());
        let mut release_times = Vec::new();
        for flow in [0.3, 0.7, 1.5] {
            compute_release_times(&curve, Flow::new_unchecked(flow), &mut release_times);
            // Simulation of the queue, vehicle by vehicle, with the rule of the within-day model.
            let mut reopening_time: f64 = 0.;
            for (i, &(arrival, pce)) in arrivals.iter().enumerate() {
                let entry = arrival.max(reopening_time);
                reopening_time = entry + pce / flow;
                if i == 0 || arrivals[i - 1].0 != arrival {
                    // The probe is the first vehicle of its group.
                    let predicted = f64::from(entry_time(&curve, &release_times, s(arrival)));
                    assert!(
                        (predicted - entry).abs() < 1e-9,
                        "Flow {flow}, vehicle {i}: {predicted} != {entry}"
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
        let categories = EdgeCategories {
            ids: vec![Some(MetroId::from("a"))],
            initial_capacities: vec![FlowPerLane::new_unchecked(0.25)],
            edge_categories: vec![Some(0), None, None],
        };
        let curves: ArrivalCurves = vec![
            Some(curve(&[(0., 1.), (1., 1.), (2., 1.)])),
            Some(curve(&[(12., 1.), (13., 1.)])),
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
            // The probe is the third vehicle arriving at edge 0.
            (s(2.), path(&[0, 1, 2])),
            // The probe arrives after the queue of edge 1 has cleared.
            (s(20.), path(&[1, 2])),
            (s(0.), path(&[2])),
        ];
        let mut surrogate = Surrogate::new(curves, &edges, &categories, &vehicle, routes);
        let capacity = |c: f64| FlowPerLane::new_unchecked(c);
        // Flow 0.5 on edge 0: the probe enters edge 0 at 4 (delay 2), reaches edge 1 at 14 and
        // enters it at 16 (delay 2).
        assert_eq!(
            surrogate.predict(&[capacity(0.25)]),
            vec![s(4.), s(0.), s(0.)]
        );
        // Flow 0.25 on edge 0: the probe enters edge 0 at 8 (delay 6) and reaches edge 1 at 18,
        // after its queue.
        assert_eq!(
            surrogate.predict(&[capacity(0.125)]),
            vec![s(6.), s(0.), s(0.)]
        );
        // Flow 1 on edge 0: no delay on edge 0, the probe reaches edge 1 at 12, at the same time
        // as the first vehicle there.
        assert_eq!(
            surrogate.predict(&[capacity(0.5)]),
            vec![s(0.), s(0.), s(0.)]
        );
    }
}
