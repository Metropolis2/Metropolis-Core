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
pub mod parameters;
mod surrogate;

use std::time::{Duration, Instant};

use anyhow::{anyhow, bail, Context, Result};
use log::{info, warn};
use petgraph::graph::EdgeIndex;

use self::parameters::{Capacities, CategoryCapacity, IdValue, OptimizerParameters};
use self::surrogate::Surrogate;
use crate::hash::{HashMap, HashSet};
use crate::mode::trip::DepartureTimeModel;
use crate::mode::Mode;
use crate::network::road_network::arrival_curve::ArrivalCurves;
use crate::network::road_network::vehicle::Vehicle;
use crate::network::road_network::{BottleneckFlows, OriginalEdgeId, RoadEdge, RoadNetworkState};
use crate::network::NetworkState;
use crate::population::Agent;
use crate::simulation::{check_ids_exist, format_ids};
use crate::units::*;

/// Runs the road-capacity calibration.
pub fn run() -> Result<()> {
    crate::simulation::init_thread_pool();
    crate::simulation::check_validity()?;
    let params = crate::parameters::capacity_calibration()
        .expect("The capacity-calibration parameters are not set");
    check_population(crate::population::agents())?;
    let edges: Vec<_> = crate::network::road_network::iter_edges().collect();
    let categories = EdgeCategories::new(&edges, &params.capacities)?;
    check_optimizer_parameters(&params.optimizer)?;
    check_bottleneck_model(
        &edges,
        crate::network::road_network::parameters::constrain_inflow(),
    )?;
    let vehicle = calibration_vehicle(
        crate::network::road_network::vehicles(),
        params.vehicle_type.as_ref(),
    )?;
    let path = crate::parameters::input_files()
        .target_routes
        .as_ref()
        .expect("The target-routes file is not set");
    let target_routes = crate::io::read_target_routes(path)?;
    check_target_routes(&target_routes)?;
    info!(
        "Capacity calibration with {} target routes and vehicle type `{}`",
        target_routes.len(),
        vehicle.id
    );
    categories.log_summary();
    let curves = simulate_day(
        &edges,
        &categories,
        &categories.initial_capacities,
        &target_routes,
    )?;
    let mut surrogate = Surrogate::new(
        curves,
        &edges,
        &categories,
        vehicle,
        target_routes.iter().map(|r| {
            let path = r
                .path
                .iter()
                .map(|&e| crate::network::road_network::edge_index_of(e))
                .collect();
            (r.departure_time, path)
        }),
    );
    let start = Instant::now();
    let predicted_delays = surrogate.predict(&categories.initial_capacities);
    let target_delays: Vec<_> = target_routes.iter().map(|r| r.target_delay).collect();
    log_fit(&target_delays, &predicted_delays, start.elapsed());
    let start = Instant::now();
    let (predicted_delays, jacobian) =
        surrogate.predict_with_jacobian(&categories.initial_capacities);
    log_sensitivity(
        &categories,
        &target_delays,
        &predicted_delays,
        &jacobian,
        start.elapsed(),
    );
    optimizer::optimize_capacities(
        &mut surrogate,
        &target_delays,
        &categories.initial_capacities,
        &params.optimizer,
        &categories,
    );
    bail!(
        "The capacity-calibration loop (simulation with the optimized capacities) is not \
        implemented yet"
    )
}

/// Checks the parameters of the optimization of the capacities.
fn check_optimizer_parameters(optimizer: &OptimizerParameters) -> Result<()> {
    if optimizer.trust_region <= 0. || optimizer.trust_region >= 1. {
        bail!("The parameter `optimizer.trust_region` must be between 0 and 1");
    }
    if optimizer.step_tolerance <= 0. {
        bail!("The parameter `optimizer.step_tolerance` must be positive");
    }
    if optimizer.max_iterations == 0 {
        bail!("The parameter `optimizer.max_iterations` must be positive");
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

/// Logs the fit of the predicted delays of the target routes (at the initial capacities) to their
/// target delays, and the time taken by the surrogate model to predict them.
fn log_fit(
    target_delays: &[NonNegativeSeconds],
    predicted_delays: &[NonNegativeSeconds],
    duration: Duration,
) {
    debug_assert_eq!(target_delays.len(), predicted_delays.len());
    if target_delays.is_empty() {
        return;
    }
    let n = target_delays.len() as f64;
    let errors: Vec<f64> = predicted_delays
        .iter()
        .zip(target_delays)
        .map(|(&p, &t)| f64::from(p) - f64::from(t))
        .collect();
    let rmse = (errors.iter().map(|e| e * e).sum::<f64>() / n).sqrt();
    let mean_error = errors.iter().sum::<f64>() / n;
    let max_error = errors.iter().fold(0.0f64, |m, e| m.max(e.abs()));
    let mean_target = target_delays.iter().map(|&d| f64::from(d)).sum::<f64>() / n;
    info!(
        "Surrogate model at the initial capacities: RMSE of the delays {rmse:.3} s, mean error \
        (predicted - target) {mean_error:.3} s, maximum absolute error {max_error:.3} s, mean \
        target delay {mean_target:.3} s (evaluated in {:.1} ms)",
        duration.as_secs_f64() * 1e3,
    );
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
    let n = target_delays.len() as f64;
    let residuals: Vec<f64> = predicted_delays
        .iter()
        .zip(target_delays)
        .map(|(&p, &t)| f64::from(p) - f64::from(t))
        .collect();
    let rmse = |shifts: &mut dyn Iterator<Item = f64>| {
        (residuals
            .iter()
            .zip(shifts)
            .map(|(r, d)| (r + d).powi(2))
            .sum::<f64>()
            / n)
            .sqrt()
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

/// Simulates one day with the given capacities (by category): runs the pre-day model with the
/// initial network conditions, then the within-day model, recording the arrival curves at the
/// entry of the edges of the target routes.
fn simulate_day(
    edges: &[&RoadEdge],
    categories: &EdgeCategories,
    capacities: &[FlowPerLane],
    target_routes: &[TargetRoute],
) -> Result<ArrivalCurves> {
    let (preprocess_data, weights, mut node_orders) = crate::simulation::prepare()?;
    info!("Computing skims");
    let skims =
        crate::network::compute_skims(&weights, &preprocess_data.network, &mut node_orders)?;
    info!("Running demand model");
    let mut agent_results = crate::simulation::run_pre_day_model(
        &weights,
        &skims,
        &preprocess_data,
        None,
        crate::parameters::init_iteration_counter(),
    )?;
    let target_route_edges: HashSet<_> = target_routes
        .iter()
        .flat_map(|r| r.path.iter())
        .map(|&id| crate::network::road_network::edge_index_of(id))
        .collect();
    let mut rn_state = RoadNetworkState::init(&categories.bottleneck_flows(edges, capacities));
    rn_state.record_arrivals(target_route_edges.iter().copied());
    info!("Running supply model");
    let mut state = crate::simulation::run_within_day_model(
        &mut agent_results,
        &skims,
        &preprocess_data,
        NetworkState::new(Some(rn_state)),
    )?;
    let curves = state
        .get_mut_road_network()
        .expect("The road-network state is set")
        .take_arrival_curves();
    curves.log_summary();
    let nb_infinite = target_route_edges
        .iter()
        .filter(|&&e| curves.get(e).is_none())
        .count();
    if nb_infinite > 0 {
        info!(
            "{nb_infinite} edges of the target routes have an infinite bottleneck flow (no \
            arrival curve is recorded)"
        );
    }
    Ok(curves)
}

/// A route with an observed queueing delay, that the calibrated capacities must reproduce.
#[derive(Clone, Debug)]
pub(crate) struct TargetRoute {
    /// Id of the route.
    pub(crate) id: MetroId,
    /// Departure time from the first edge of the path.
    pub(crate) departure_time: NonNegativeSeconds,
    /// Observed delay of the route: its travel time minus its free-flow travel time.
    pub(crate) target_delay: NonNegativeSeconds,
    /// Edges of the route, in order.
    pub(crate) path: Vec<OriginalEdgeId>,
}

impl TargetRoute {
    /// Creates a new TargetRoute from deserialized values.
    pub(crate) fn from_values(
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
            (r#"{"trust_region": 0.0}"#, "trust_region"),
            (r#"{"trust_region": 1.0}"#, "trust_region"),
            (r#"{"step_tolerance": 0.0}"#, "step_tolerance"),
            (r#"{"max_iterations": 0}"#, "max_iterations"),
        ] {
            let msg = check_optimizer_parameters(&serde_json::from_str(optimizer).unwrap())
                .unwrap_err()
                .to_string();
            assert!(msg.contains(&format!("`optimizer.{name}`")), "{msg}");
        }
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
