//! Everything related to road modes of transportation.
use super::{ModeCallback, ModeResults, PreDayChoices};
use crate::agent::AgentIndex;
use crate::event::{Event, EventQueue};
use crate::mode::PreDayChoiceAllocation;
use crate::network::road_network::skim::{EAAllocation, RoadNetworkSkim, RoadNetworkSkims};
use crate::network::road_network::state::BottleneckStatus;
use crate::network::road_network::vehicle::VehicleIndex;
use crate::network::road_network::RoadNetwork;
use crate::network::{Network, NetworkSkim, NetworkState};
use crate::schedule_utility::ScheduleUtility;
use crate::schema::NodeIndexDef;
use crate::simulation::results::AgentResult;
use crate::travel_utility::TravelUtility;
use crate::units::{Distribution, Interval, Length, NoUnit, Time, Utility};

use anyhow::{anyhow, Result};
use choice::ContinuousChoiceModel;
use hashbrown::HashSet;
use num_traits::{Float, Zero};
use petgraph::graph::{EdgeIndex, NodeIndex};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::{PwlTTF, PwlXYF, TTFNum, TTF};

/// Model used to compute the chosen departure time.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "values")]
pub enum DepartureTimeModel<T> {
    /// The departure time is always equal to the given value.
    Constant(Time<T>),
    /// The departure time is chosen according to a continuous choice model.
    ContinuousChoice {
        /// Interval in which the departure time is chosen.
        period: Interval<T>,
        /// Continuous choice model.
        choice_model: ContinuousChoiceModel<NoUnit<T>>,
    },
}

/// Representation of the mode of transportation for a vehicle that travels on the road network.
///
/// A road mode of transportation has the following attributes:
/// - An origin and a destination, represented as [NodeIndex] of the road network graph.
/// - A vehicle, represented as a [VehicleIndex] for the [RoadNetwork].
/// - A departure-time period `[t0, t1]` that represents the earliest and latest possible departure
///   times.
/// - A [ContinuousChoiceModel] that represents the departure-time choice model of the agent for
///   this mode.
/// - A [TravelUtility] object that represents the way the travel utility of the agent is
///   computed for this mode.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Road Mode")]
#[schemars(description = "Mode of transportation for a vehicle that travels on the road network.")]
#[schemars(example = "crate::schema::example_road_mode")]
pub struct RoadMode<T> {
    #[schemars(with = "NodeIndexDef")]
    /// Id of the origin node on the road network graph.
    origin: NodeIndex,
    #[schemars(with = "NodeIndexDef")]
    /// Id of the destination node on the road network graph.
    destination: NodeIndex,
    /// Id of the vehicle.
    vehicle: VehicleIndex,
    /// Model used for the departure-time choice.
    departure_time_model: DepartureTimeModel<T>,
    /// Travel-utility model describing how travel utility is computed.
    #[serde(default)]
    utility_model: TravelUtility<T>,
}

impl<T> RoadMode<T> {
    /// Creates a new RoadMode.
    pub fn new(
        origin: NodeIndex,
        destination: NodeIndex,
        vehicle: VehicleIndex,
        departure_time_model: DepartureTimeModel<T>,
        utility_model: TravelUtility<T>,
    ) -> Self {
        RoadMode {
            origin,
            destination,
            vehicle,
            departure_time_model,
            utility_model,
        }
    }

    /// Return the [VehicleIndex] of the [RoadMode].
    pub fn vehicle_index(&self) -> VehicleIndex {
        self.vehicle
    }

    /// Return the origin of the [RoadMode].
    pub fn origin(&self) -> NodeIndex {
        self.origin
    }

    /// Return the destination of the [RoadMode].
    pub fn destination(&self) -> NodeIndex {
        self.destination
    }
}

impl<T: TTFNum> RoadMode<T> {
    /// Return the travel utility for this mode, given the total travel time.
    pub fn get_travel_utility(&self, tt: Time<T>) -> Utility<T> {
        self.utility_model.get_travel_utility(tt)
    }

    /// Return the total utility of a trip given the departure time, arrival time and travel time.
    ///
    /// The total utility is the sum of the travel utility and the schedule utility.
    pub fn get_utility(
        &self,
        schedule_utility: &ScheduleUtility<T>,
        departure_time: Time<T>,
        arrival_time: Time<T>,
        travel_time: Time<T>,
    ) -> Utility<T> {
        schedule_utility.get_utility(departure_time, arrival_time)
            + self.get_travel_utility(travel_time)
    }

    /// Return the total utility of a trip for this mode, given the [RoadResults], the
    /// [ScheduleUtility] and the departure and arrival times.
    pub fn get_utility_from_results(
        &self,
        results: &RoadResults<T>,
        schedule_utility: &ScheduleUtility<T>,
        departure_time: Time<T>,
        arrival_time: Time<T>,
    ) -> Utility<T> {
        self.get_utility(
            schedule_utility,
            departure_time,
            arrival_time,
            results.total_travel_time(),
        )
    }

    /// Return the pre-day choice for this mode.
    ///
    /// Given the expected [RoadNetworkSkims] and the [ScheduleUtility], this returns a tuple with
    /// the expected utility from the departure-time choice model and a [ModeCallback] function.
    ///
    /// The departure time and route chosen are only computed when the callback function is called.
    pub fn make_pre_day_choice<'a: 'b, 'b>(
        &'a self,
        rn_skims: &'b RoadNetworkSkims<T>,
        schedule_utility: &ScheduleUtility<T>,
    ) -> Result<(Utility<T>, ModeCallback<'b, T>)> {
        let skims = rn_skims[self.vehicle]
            .as_ref()
            .ok_or_else(|| anyhow!("No skims were computed for the vehicle of the agent"))?;
        if let Some(ttf) = skims.profile_query(self.origin, self.destination)? {
            match &self.departure_time_model {
                &DepartureTimeModel::Constant(dt) => {
                    let tt = ttf.eval(dt);
                    let utility = self.get_utility(schedule_utility, dt, dt + tt, tt);
                    let callback =
                        move |alloc: &mut PreDayChoiceAllocation<T>| -> Result<PreDayChoices<T>> {
                            let (arrival_time, route) = get_arrival_time_and_route(
                                self.origin,
                                self.destination,
                                dt,
                                skims,
                                alloc,
                            )?;
                            if cfg!(debug_assertions) {
                                check_route(dt, arrival_time, &route, ttf);
                            }
                            Ok(PreDayChoices::Road(RoadChoices::new(
                                dt,
                                arrival_time,
                                route,
                                self.destination,
                                self.vehicle,
                            )))
                        };
                    Ok((utility, Box::new(callback)))
                }
                DepartureTimeModel::ContinuousChoice {
                    period,
                    choice_model,
                } => {
                    // Create a `PwlXYF` that yields the utility for each departure time breakpoint in the
                    // TTF and for each departure time breakpoint from the schedule utility model.
                    let new_breakpoints = schedule_utility.get_breakpoints(ttf);
                    let breakpoints = match ttf {
                        TTF::Constant(c) => {
                            let mut breakpoints = Vec::with_capacity(2 + new_breakpoints.len());
                            breakpoints.push((period.start(), *c));
                            breakpoints.extend(
                                new_breakpoints
                                    .into_iter()
                                    .skip_while(|&(dt, _)| dt <= period.start())
                                    .take_while(|&(dt, _)| dt <= period.end()),
                            );
                            breakpoints.push((period.end(), *c));
                            breakpoints
                        }
                        TTF::Piecewise(pwl_ttf) => {
                            add_breakpoints_to_pwl_ttf(pwl_ttf, new_breakpoints)
                        }
                    };
                    let utilities = PwlXYF::from_iterator(
                        breakpoints.into_iter().map(|(dt, tt)| {
                            (dt, self.get_utility(schedule_utility, dt, dt + tt, tt))
                        }),
                        [period.start(), period.end()],
                    );
                    let (time_callback, expected_utility) = choice_model.get_choice(utilities)?;
                    let callback =
                        move |alloc: &mut PreDayChoiceAllocation<T>| -> Result<PreDayChoices<T>> {
                            let dt = time_callback();
                            let (arrival_time, route) = get_arrival_time_and_route(
                                self.origin,
                                self.destination,
                                dt,
                                skims,
                                alloc,
                            )?;
                            if cfg!(debug_assertions) {
                                check_route(dt, arrival_time, &route, ttf);
                            }
                            Ok(PreDayChoices::Road(RoadChoices::new(
                                dt,
                                arrival_time,
                                route,
                                self.destination,
                                self.vehicle,
                            )))
                        };
                    Ok((expected_utility, Box::new(callback)))
                }
            }
        } else {
            // No route from origin to destination.
            Err(anyhow!(
                "No route on road network from origin {:?} to destination {:?}",
                self.origin,
                self.destination,
            ))
        }
    }
}

/// Run an earliest arrival query on the [RoadNetworkSkim] to get the arrival time and route, for a
/// given origin, destination and departure time.
///
/// Return an error if the destination cannot be reached with the given departure time from origin.
fn get_arrival_time_and_route<T: TTFNum>(
    origin: NodeIndex,
    destination: NodeIndex,
    departure_time: Time<T>,
    skims: &RoadNetworkSkim<T>,
    alloc: &mut PreDayChoiceAllocation<T>,
) -> Result<(Time<T>, Vec<EdgeIndex>)> {
    if let Some((arrival_time, route)) = skims.earliest_arrival_query(
        origin,
        destination,
        departure_time,
        &mut alloc.road_alloc.ea_alloc,
    )? {
        Ok((arrival_time, route))
    } else {
        Err(anyhow!(
            "No route from {:?} to {:?} at departure time {:?}",
            origin,
            destination,
            departure_time,
        ))
    }
}

/// Run checks to ensure that the computed route and arrival time are valid.
fn check_route<T: TTFNum>(
    departure_time: Time<T>,
    arrival_time: Time<T>,
    route: &[EdgeIndex],
    ttf: &TTF<Time<T>>,
) {
    // Check that there is no loop in the route.
    let n = route.iter().collect::<HashSet<_>>().len();
    assert_eq!(n, route.len(), "Invalid route: {:?}", route);
    // Check that the predicted arrival time is coherent with the TTF.
    let tt = ttf.eval(departure_time);
    assert!(
        arrival_time - (departure_time + tt) < Time::large_margin(),
        "Invalid arrival time: {:?} != {:?} + {:?} = {:?}",
        arrival_time,
        departure_time,
        tt,
        departure_time + tt
    );
}

/// Add new breakpoints `(td, ta)` to a [PwlTTF].
fn add_breakpoints_to_pwl_ttf<T: TTFNum>(
    pwl_ttf: &PwlTTF<Time<T>>,
    new_breakpoints: Vec<(Time<T>, Time<T>)>,
) -> Vec<(Time<T>, Time<T>)> {
    let mut breakpoints = Vec::with_capacity(pwl_ttf.len() + new_breakpoints.len() + 1);
    let &[first, last] = pwl_ttf.period();
    if new_breakpoints.is_empty() {
        for point in pwl_ttf.iter() {
            breakpoints.push((point.x, point.y));
        }
    } else {
        let mut ttf_iter = pwl_ttf.iter().peekable();
        for (dt, tt) in new_breakpoints.into_iter() {
            while let Some(point) = ttf_iter.peek() {
                if point.x.approx_eq(&dt) {
                    ttf_iter.next();
                    continue;
                }
                if point.x > dt {
                    break;
                }
                breakpoints.push((point.x, point.y));
                ttf_iter.next();
            }
            if dt < first {
                continue;
            }
            if dt > last {
                break;
            }
            breakpoints.push((dt, tt));
        }
    }
    debug_assert!(!breakpoints.is_empty());
    if breakpoints.last().unwrap().0.approx_ne(&last) {
        // Add a breakpoint for the last period.
        debug_assert!(breakpoints.last().unwrap().0 < last,);
        breakpoints.push((last, pwl_ttf.eval(last)));
    }
    breakpoints
}

/// Struct to store the pre-day choices (departure time, expected arrival time and route) from a
/// [RoadMode].
///
/// The destination and vehicle from the [RoadMode] are stored here for convenience.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct RoadChoices<T> {
    departure_time: Time<T>,
    expected_arrival_time: Time<T>,
    route: Vec<EdgeIndex>,
    #[serde(skip_serializing)]
    #[serde(default)]
    destination: NodeIndex,
    #[serde(skip_serializing)]
    #[serde(default)]
    vehicle: VehicleIndex,
}

impl<T> RoadChoices<T> {
    /// Creates a new RoadChoices.
    pub fn new(
        departure_time: Time<T>,
        expected_arrival_time: Time<T>,
        route: Vec<EdgeIndex>,
        destination: NodeIndex,
        vehicle: VehicleIndex,
    ) -> Self {
        RoadChoices {
            departure_time,
            expected_arrival_time,
            route,
            destination,
            vehicle,
        }
    }

    /// Return the route chosen in the pre-day model.
    pub fn get_route(&self) -> &[EdgeIndex] {
        &self.route
    }

    /// Return the number of edges in the chosen route.
    pub fn route_len(&self) -> usize {
        self.route.len()
    }

    /// Return the [EdgeIndex] at the given position in the chosen route (0 is the first edge in
    /// the route).
    pub fn get_edge_by_position(&self, position: usize) -> EdgeIndex {
        self.route[position]
    }
}

impl<T: Copy> RoadChoices<T> {
    /// Return the departure time chosen in the pre-day model.
    pub fn get_departure_time(&self) -> Time<T> {
        self.departure_time
    }
}

impl<T: TTFNum + 'static> RoadChoices<T> {
    /// Return a [VehicleEvent] of type [VehicleEventType::LeavesOrigin] that represent the
    /// departure of the agent from his / her origin.
    pub fn get_event(&self, agent: AgentIndex) -> Option<Box<dyn Event<T>>> {
        Some(Box::new(VehicleEvent::new(agent, self.departure_time)))
    }
}

impl<T: TTFNum> RoadChoices<T> {
    /// Return an empty [RoadResults].
    pub fn init_mode_results(&self) -> RoadResults<T> {
        RoadResults::with_capacity(self.route_len())
    }

    /// Return the expected travel time at the departure time chosen in the pre-day model.
    pub fn get_expected_travel_time(&self) -> Time<T> {
        self.expected_arrival_time - self.departure_time
    }
}

/// Struct used to store the results from a [RoadMode] in the within-day model.
#[derive(Debug, Default, Clone, Deserialize, Serialize)]
pub struct RoadResults<T> {
    /// The route taken by the vehicle, as a Vec of [EdgeIndex].
    route: Vec<EdgeIndex>,
    /// The timings at which the vehicle entered each edge.
    road_breakpoints: Vec<Time<T>>,
    /// The timings at which the vehicle reached the bottleneck of each edge.
    bottleneck_breakpoints: Vec<Time<T>>,
    /// The timings at which the vehicle exited the bottleneck of each edge.
    pending_breakpoints: Vec<Time<T>>,
    /// Total time spent traveling on an edge.
    road_time: Time<T>,
    /// Total time spent waiting at the bottleneck of an edge.
    bottleneck_time: Time<T>,
    /// Total time spent pending for the next edge to get free.
    pending_time: Time<T>,
}

impl<T: TTFNum> RoadResults<T> {
    /// Creates an empty RoadResults.
    pub fn new() -> Self {
        Default::default()
    }

    /// Create a new [RoadResults] with the given capacity (in number of edges taken).
    pub fn with_capacity(capacity: usize) -> Self {
        RoadResults {
            route: Vec::with_capacity(capacity),
            road_breakpoints: Vec::with_capacity(capacity),
            bottleneck_breakpoints: Vec::with_capacity(capacity),
            pending_breakpoints: Vec::with_capacity(capacity),
            ..Default::default()
        }
    }

    /// Record the entry of the vehicle on the given edge at the given time.
    fn enters_edge(&mut self, edge: EdgeIndex, at_time: Time<T>) {
        self.route.push(edge);
        self.road_breakpoints.push(at_time);
        if let Some(last_time) = self.pending_breakpoints.last() {
            self.pending_time = self.pending_time + at_time - *last_time;
        }
    }

    /// Record the entry of the vehicle at the bottleneck of the given edge at the given time.
    fn enters_bottleneck(&mut self, at_time: Time<T>) {
        self.bottleneck_breakpoints.push(at_time);
        if let Some(last_time) = self.road_breakpoints.last() {
            self.road_time = self.road_time + at_time - *last_time;
        }
    }

    /// Record the exit of the vehicle from the bottleneck of the given edge at the given time.
    fn exits_bottleneck(&mut self, at_time: Time<T>) {
        self.pending_breakpoints.push(at_time);
        if let Some(last_time) = self.bottleneck_breakpoints.last() {
            self.bottleneck_time = self.bottleneck_time + at_time - *last_time;
        }
    }

    /// Return the total travel time of the vehicle (sum of road time, bottleneck time and pending
    /// time).
    pub fn total_travel_time(&self) -> Time<T> {
        self.road_time + self.bottleneck_time + self.pending_time
    }

    /// Return the number of edges taken by the vehicle.
    pub fn edge_count(&self) -> usize {
        self.route.len()
    }

    /// Compute the route free-flow travel time of the vehicle.
    ///
    /// The route free-flow travel time is the travel time of the vehicle *on the same route*
    /// assuming that there is no congestion.
    pub fn route_free_flow_travel_time(
        &self,
        road_network: &RoadNetwork<T>,
        vehicle_index: VehicleIndex,
    ) -> Time<T> {
        let mut tt = Time::zero();
        let vehicle = &road_network[vehicle_index];
        for &edge_id in self.route.iter() {
            tt = tt
                + road_network
                    .get_graph()
                    .edge_weight(edge_id)
                    .expect("The route is incompatible with the road network.")
                    .get_free_flow_travel_time(vehicle);
        }
        tt
    }

    /// Return the length of the route taken by the vehicle.
    pub fn route_length(&self, road_network: &RoadNetwork<T>) -> Length<T> {
        let mut length = Length::zero();
        for &edge_id in self.route.iter() {
            length = length
                + road_network
                    .get_graph()
                    .edge_weight(edge_id)
                    .expect("The route is incompatible with the road network.")
                    .length();
        }
        length
    }
}

/// Struct to store aggregate results specific to road modes of transportation.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AggregateRoadResults<T> {
    /// Number of trips taken with a [RoadMode].
    pub count: usize,
    /// The relative difference between average actual travel time and average free-flow travel
    /// time.
    pub congestion: Distribution<T>,
    /// Distribution of departure times.
    pub departure_times: Distribution<Time<T>>,
    /// Distribution of arrival times.
    pub arrival_times: Distribution<Time<T>>,
    /// Distribution of road times.
    pub road_times: Distribution<Time<T>>,
    /// Distribution of bottleneck times.
    pub bottleneck_times: Distribution<Time<T>>,
    /// Distribution of pending times.
    pub pending_times: Distribution<Time<T>>,
    /// Distribution of total travel times times.
    pub travel_times: Distribution<Time<T>>,
    /// Distribution of route free-flow travel times times.
    pub route_free_flow_travel_times: Distribution<Time<T>>,
    /// Distribution of route length.
    pub lengths: Distribution<Length<T>>,
    /// Distribution of number of edges taken.
    pub edge_counts: Distribution<T>,
    /// Distribution of total utility.
    pub utilities: Distribution<Utility<T>>,
    /// Distribution of relative difference between expected travel time and actual travel time.
    pub exp_travel_time_diff: Distribution<T>,
    /// Distribution of departure time shift compared to previous iteration (except for the first
    /// iteration, excluding agents who chose a different mode in the previous iteration).
    pub dep_time_shift: Option<Distribution<Time<T>>>,
}

/// Shorthand for a Vec to store tuples with, for each agent, the [RoadMode], the [AgentResult] and
/// (optionally) the [AgentResult] from previous iteration.
pub type RoadAgentResults<'a, T> = Vec<(
    &'a RoadMode<T>,
    &'a AgentResult<T>,
    Option<&'a AgentResult<T>>,
)>;

impl<T: TTFNum + 'static> AggregateRoadResults<T> {
    /// Compute [AggregateRoadResults] from the results of an iteration.
    pub fn from_agent_results(
        results: RoadAgentResults<'_, T>,
        road_network: &RoadNetwork<T>,
    ) -> Self {
        fn get_distribution<U, V: TTFNum, F: Fn(&RoadMode<U>, &RoadResults<U>) -> V>(
            results: &RoadAgentResults<'_, U>,
            func: F,
        ) -> Distribution<V> {
            Distribution::from_iterator(results.iter().map(|(m, r, _)| {
                if let ModeResults::Road(road_results) = r.mode_results() {
                    func(m, road_results)
                } else {
                    panic!("Invalid within-day results");
                }
            }))
            .unwrap()
        }
        let msg = "Invalid within-day results";
        assert!(!results.is_empty(), "{msg}");
        let departure_times = Distribution::from_iterator(
            results
                .iter()
                .map(|(_, r, _)| r.departure_time().expect(msg)),
        )
        .unwrap();
        let arrival_times = Distribution::from_iterator(
            results.iter().map(|(_, r, _)| r.arrival_time().expect(msg)),
        )
        .unwrap();
        let road_times = get_distribution(&results, |_, r| r.road_time);
        let bottleneck_times = get_distribution(&results, |_, r| r.bottleneck_time);
        let pending_times = get_distribution(&results, |_, r| r.pending_time);
        let travel_times = get_distribution(&results, |_, r| r.total_travel_time());
        let route_free_flow_travel_times = get_distribution(&results, |m, r| {
            r.route_free_flow_travel_time(road_network, m.vehicle)
        });
        let lengths = get_distribution(&results, |_, r| r.route_length(road_network));
        let edge_counts = get_distribution(&results, |_, r| T::from_usize(r.edge_count()).unwrap());
        let utilities =
            Distribution::from_iterator(results.iter().map(|(_, r, _)| r.utility().expect(msg)))
                .unwrap();
        let exp_travel_time_diff = Distribution::from_iterator(results.iter().map(|(_, r, _)| {
            if let (PreDayChoices::Road(road_choices), ModeResults::Road(road_results)) =
                (r.pre_day_results().get_choices(), r.mode_results())
            {
                let exp_tt = road_choices.get_expected_travel_time();
                let tt = road_results.total_travel_time();
                if exp_tt > Time::zero() {
                    (exp_tt - tt).abs().0 / exp_tt.0
                } else {
                    T::zero()
                }
            } else {
                panic!("{msg}");
            }
        }))
        .unwrap();
        let dep_time_shift =
            Distribution::from_iterator(results.iter().filter_map(|(_, r, prev_r_opt)| {
                prev_r_opt.as_ref().map(|prev_r| {
                    (r.departure_time().unwrap() - prev_r.departure_time().unwrap()).abs()
                })
            }));
        let congestion = get_distribution(&results, |m, r| {
            let tt = r.total_travel_time();
            let fftt = r.route_free_flow_travel_time(road_network, m.vehicle);
            (tt.0 - fftt.0) / fftt.0
        });
        AggregateRoadResults {
            count: results.len(),
            congestion,
            departure_times,
            arrival_times,
            road_times,
            bottleneck_times,
            pending_times,
            travel_times,
            route_free_flow_travel_times,
            lengths,
            edge_counts,
            utilities,
            exp_travel_time_diff,
            dep_time_shift,
        }
    }
}

/// Types of [VehicleEvent].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VehicleEventType {
    /// The vehicle leaves its origin.
    LeavesOrigin,
    /// The vehicle enters the next edge.
    EntersEdge,
    /// The vehicle enters the bottleneck of its current edge.
    EntersBottleneck,
    /// The vehicle exits the bottleneck of its current edge.
    ExitsBottleneck,
    /// The vehicle reaches its destination.
    ReachesDestination,
}

/// Struct that describes the vehicle events that happen in the within-day model.
///
/// The struct is updated and re-inserted in the event queue when the event is executed.
#[derive(Clone, Debug, PartialEq)]
pub struct VehicleEvent<T> {
    /// The index of the associated agent.
    agent: AgentIndex,
    /// The time of the event.
    at_time: Time<T>,
    /// Index of the current edge of the vehicle in the planned route.
    position: usize,
    /// Edge where the vehicle currently is.
    current_edge: Option<EdgeIndex>,
    /// Type of event.
    event_type: VehicleEventType,
}

impl<T> VehicleEvent<T> {
    /// Create a new [VehicleEvent] for a given agent that leaves his / her origin at the given
    /// time.
    pub fn new(agent: AgentIndex, at_time: Time<T>) -> Self {
        VehicleEvent {
            agent,
            at_time,
            position: 0,
            current_edge: None,
            event_type: VehicleEventType::LeavesOrigin,
        }
    }

    /// Change the time of the event.
    pub fn set_time(&mut self, at_time: Time<T>) {
        self.at_time = at_time;
    }

    /// Return the [EdgeIndex] at the current position in the chosen route.
    fn get_edge_at_current_position(&self, choices: &RoadChoices<T>) -> Option<EdgeIndex> {
        let route = choices.get_route();
        route.get(self.position).copied()
    }
}

impl<T: TTFNum> VehicleEvent<T> {
    /// Record this event in the given [AgentResult].
    fn record_event(&self, result: &mut AgentResult<T>) {
        if self.event_type == VehicleEventType::LeavesOrigin {
            result.set_departure_time(self.at_time);
        } else if self.event_type == VehicleEventType::ReachesDestination {
            result.set_arrival_time(self.at_time);
        }
        if let ModeResults::Road(road_results) = result.mut_mode_results() {
            match self.event_type {
                VehicleEventType::EntersEdge => {
                    road_results.enters_edge(self.current_edge.unwrap(), self.at_time);
                }
                VehicleEventType::EntersBottleneck => {
                    road_results.enters_bottleneck(self.at_time);
                }
                VehicleEventType::ExitsBottleneck => {
                    road_results.exits_bottleneck(self.at_time);
                }
                _ => {}
            }
        } else {
            panic!("Got a road event for an agent with no RoadResults.");
        }
    }
}

impl<T: TTFNum + 'static> Event<T> for VehicleEvent<T> {
    fn execute<'a: 'b, 'b>(
        mut self: Box<Self>,
        network: &'a Network<T>,
        exp_skims: &NetworkSkim<T>,
        state: &mut NetworkState<'b, T>,
        result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<T>,
    ) {
        let road_network = network
            .get_road_network()
            .expect("Got a vehicle event but there is no road network.");
        let road_network_state = state
            .get_mut_road_network()
            .expect("Got a vehicle event but there is no road network state.");
        let agent_result = result.expect("Got a vehicle event with no agent.");
        self.record_event(agent_result);
        let choices =
            if let PreDayChoices::Road(choices) = agent_result.pre_day_results().get_choices() {
                choices
            } else {
                panic!("Got a vehicle event for an agent with no RoadChoices.");
            };
        match self.event_type {
            VehicleEventType::LeavesOrigin => {
                debug_assert_eq!(self.position, 0);
                // Set the current edge to the first edge of the route.
                self.current_edge = Some(
                    self.get_edge_at_current_position(choices)
                        .expect("Cannot start route."),
                );
                self.event_type = VehicleEventType::EntersEdge;
                // We can execute the next event directly because the time is the same.
                self.execute(network, exp_skims, state, Some(agent_result), events);
            }
            VehicleEventType::EntersEdge => {
                let vehicle_index = choices.vehicle;
                let vehicle = &road_network[vehicle_index];
                let travel_time = road_network_state[self.current_edge.unwrap()]
                    .enters_edge(vehicle, self.at_time);
                self.event_type = VehicleEventType::EntersBottleneck;
                if travel_time == Time::zero() {
                    // We can execute the next event directly because the time is the same.
                    self.execute(network, exp_skims, state, Some(agent_result), events);
                } else {
                    self.at_time = self.at_time + travel_time;
                    events.push(self);
                }
            }
            VehicleEventType::EntersBottleneck => {
                let vehicle_index = choices.vehicle;
                let vehicle = &road_network[vehicle_index];
                self.event_type = VehicleEventType::ExitsBottleneck;
                match road_network_state[self.current_edge.unwrap()]
                    .enters_bottleneck(vehicle, self)
                {
                    BottleneckStatus::Open(mut vehicle_event) => {
                        // The bottleneck is open, the vehicle immediately exits it.
                        vehicle_event.event_type = VehicleEventType::ExitsBottleneck;
                        // We can execute the next event directly because the time is the same.
                        vehicle_event.execute(
                            network,
                            exp_skims,
                            state,
                            Some(agent_result),
                            events,
                        );
                    }
                    BottleneckStatus::Closed(Some(bottleneck_event)) => {
                        // The bottleneck is closed and we need to push the BottleneckEvent to the
                        // event queue.
                        events.push(Box::new(bottleneck_event));
                    }
                    BottleneckStatus::Closed(None) => {
                        // The bottleneck is closed, the vehicle has been pushed to the bottleneck
                        // queue and a bottleneck event is already in the event queue.
                    }
                }
            }
            VehicleEventType::ExitsBottleneck => {
                self.position += 1;
                let current_edge = self.get_edge_at_current_position(choices);
                if current_edge.is_none() {
                    // The vehicle has reached its destination.
                    debug_assert!(
                        road_network
                            .get_endpoints(self.current_edge.unwrap())
                            .expect("Current edge is invalid.")
                            .1
                            == choices.destination
                    );
                    self.event_type = VehicleEventType::ReachesDestination;
                    // We can execute the next event directly because the time is the same.
                    self.execute(network, exp_skims, state, Some(agent_result), events);
                    return;
                }
                self.current_edge = current_edge;
                self.event_type = VehicleEventType::EntersEdge;
                // We can execute the next event directly because the time is the same.
                // TODO: This might no longer be true when spillback will be implemented.
                self.execute(network, exp_skims, state, Some(agent_result), events);
            }
            VehicleEventType::ReachesDestination => (),
        }
    }

    fn get_time(&self) -> Time<T> {
        self.at_time
    }

    fn get_agent_index(&self) -> Option<AgentIndex> {
        Some(self.agent)
    }
}

/// Memory allocation used when executing the [ModeCallback] function for a [RoadMode].
#[derive(Clone, Debug, Default)]
pub struct RoadChoiceAllocation<T: TTFNum> {
    /// Allocation for the earliest-arrival query.
    pub ea_alloc: EAAllocation<T>,
}
