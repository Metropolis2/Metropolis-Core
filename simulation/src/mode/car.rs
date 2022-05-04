use super::{ModeCallback, ModeResults, PreDayChoices};
use crate::agent::AgentIndex;
use crate::event::{Event, EventQueue};
use crate::mode::PreDayChoiceAllocation;
use crate::mode_utility::TravelUtility;
use crate::network::road_network::skim::EAAllocation;
use crate::network::road_network::vehicle::VehicleIndex;
use crate::network::road_network::{NodePair, RoadNetwork};
use crate::network::{NetworkSkim, NetworkState};
use crate::schedule_utility::ScheduleUtility;
use crate::simulation::AgentResult;
use crate::units::{Distribution, Length, Time, Utility};

use anyhow::{anyhow, Result};
use choice::ContinuousChoiceModel;
use num_traits::{Float, Zero};
use petgraph::graph::{EdgeIndex, NodeIndex};
use serde_derive::{Deserialize, Serialize};
use std::fmt;
use ttf::{PwlTTF, TTFNum, TTF};

pub trait RoadVehicleMode: fmt::Debug {
    fn vehicle_index(&self) -> VehicleIndex;
    fn origin(&self) -> NodeIndex;
    fn destination(&self) -> NodeIndex;
    fn node_pair(&self) -> NodePair {
        (self.origin(), self.destination())
    }
}

/// Representation of the car alternative available to an agent.
///
/// A car alternative has the following attributes:
/// - An origin and a destination represented as [NodeIndex] of the road network graph.
/// - A [ContinuousChoiceModel] object that represents the departure-time choice model of the agent
///   for this alternative.
/// - A [TravelUtility] object that represents the way the travel utility of the agent is
///   computed for this alternative.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct CarAlternative<T> {
    origin: NodeIndex,
    destination: NodeIndex,
    vehicle: VehicleIndex,
    departure_time_period: [Time<T>; 2],
    departure_time_model: ContinuousChoiceModel<T>,
    utility_model: TravelUtility<T>,
}

impl<T> CarAlternative<T> {
    pub fn new(
        origin: NodeIndex,
        destination: NodeIndex,
        vehicle: VehicleIndex,
        departure_time_period: [Time<T>; 2],
        departure_time_model: ContinuousChoiceModel<T>,
        utility_model: TravelUtility<T>,
    ) -> Self {
        CarAlternative {
            origin,
            destination,
            vehicle,
            departure_time_period,
            departure_time_model,
            utility_model,
        }
    }
}

impl<T: TTFNum> CarAlternative<T> {
    pub fn get_travel_utility(&self, results: &CarResults<T>) -> Utility<T> {
        self.utility_model
            .get_travel_utility(results.total_travel_time())
    }

    pub fn get_utility(
        &self,
        results: &CarResults<T>,
        schedule_utility: &ScheduleUtility<T>,
        departure_time: Time<T>,
        arrival_time: Time<T>,
    ) -> Utility<T> {
        schedule_utility.get_utility(departure_time, arrival_time)
            + self.get_travel_utility(results)
    }

    pub fn make_pre_day_choice<'a: 'b, 'b>(
        &'a self,
        exp_skims: &'b NetworkSkim<T>,
        schedule_utility: &ScheduleUtility<T>,
    ) -> Result<(Utility<T>, ModeCallback<'b, T>)> {
        let my_skims = &exp_skims.get_road_network().ok_or_else(|| {
            anyhow!(
                "Cannot make pre-day choice for car when there is no skims for the road network"
            )
        })?[self.vehicle];
        if let Some(ttf) = my_skims.profile_query(self.origin, self.destination)? {
            let new_breakpoints = schedule_utility.get_breakpoints(ttf);
            let breakpoints = match ttf {
                TTF::Constant(c) => {
                    let mut breakpoints = Vec::with_capacity(2 + new_breakpoints.len());
                    breakpoints.push((self.departure_time_period[0], *c));
                    breakpoints.extend(new_breakpoints.into_iter());
                    breakpoints.push((self.departure_time_period[1], *c));
                    breakpoints
                }
                TTF::Piecewise(pwl_ttf) => {
                    let mut breakpoints =
                        Vec::with_capacity(pwl_ttf.len() + new_breakpoints.len() + 1);
                    let mut ttf_iter = pwl_ttf.iter().peekable();
                    let &[first, last] = pwl_ttf.period();
                    for (dt, tt) in new_breakpoints.into_iter() {
                        if dt < first {
                            continue;
                        }
                        if dt > last {
                            break;
                        }
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
                        breakpoints.push((dt, tt));
                    }
                    if breakpoints.last().unwrap().1.approx_ne(&last) {
                        // Add a breakpoint for the last period.
                        debug_assert!(breakpoints.last().unwrap().1 < last);
                        breakpoints.push((last, pwl_ttf.eval(last)));
                    }
                    breakpoints
                }
            };
            let utilities = PwlTTF::from_iterator(
                breakpoints.into_iter().map(|(dt, tt)| {
                    (
                        dt.0,
                        self.utility_model.get_travel_utility(tt).0
                            + schedule_utility.get_utility(dt, dt + tt).0,
                    )
                }),
                [
                    self.departure_time_period[0].0,
                    self.departure_time_period[1].0,
                ],
            );
            let (time_callback, expected_utility) =
                self.departure_time_model.get_choice(utilities)?;
            let mode_callback =
                move |alloc: &mut PreDayChoiceAllocation<T>| -> Result<PreDayChoices<T>> {
                    let departure_time = Time(time_callback());
                    if let Some((arrival_time, route)) = my_skims.earliest_arrival_query(
                        self.origin,
                        self.destination,
                        departure_time,
                        &mut alloc.car_alloc.ea_alloc,
                    )? {
                        debug_assert!(arrival_time.approx_eq(&ttf.eval(departure_time)));
                        Ok(PreDayChoices::Car(CarChoices::new(
                            departure_time,
                            arrival_time,
                            route,
                            self.destination,
                            self.vehicle,
                        )))
                    } else {
                        panic!(
                            concat!(
                                "No route from {:?} to {:?} at departure time {:?},",
                                "even though the profile query returned something"
                            ),
                            self.origin, self.destination, departure_time,
                        );
                    }
                };
            Ok((Utility(expected_utility), Box::new(mode_callback)))
        } else {
            // No route from origin to destination.
            Err(anyhow!(
                "No route by car from origin {:?} to destination {:?}",
                self.origin,
                self.destination,
            ))
        }
    }
}

impl<T: fmt::Debug> RoadVehicleMode for CarAlternative<T> {
    fn vehicle_index(&self) -> VehicleIndex {
        self.vehicle
    }

    fn origin(&self) -> NodeIndex {
        self.origin
    }

    fn destination(&self) -> NodeIndex {
        self.destination
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct CarChoices<T> {
    departure_time: Time<T>,
    expected_arrival_time: Time<T>,
    route: Vec<EdgeIndex>,
    #[serde(skip_serializing)]
    destination: NodeIndex,
    #[serde(skip_serializing)]
    vehicle: VehicleIndex,
}

impl<T> CarChoices<T> {
    pub fn new(
        departure_time: Time<T>,
        expected_arrival_time: Time<T>,
        route: Vec<EdgeIndex>,
        destination: NodeIndex,
        vehicle: VehicleIndex,
    ) -> Self {
        CarChoices {
            departure_time,
            expected_arrival_time,
            route,
            destination,
            vehicle,
        }
    }

    pub fn get_route(&self) -> &[EdgeIndex] {
        &self.route
    }

    pub fn route_len(&self) -> usize {
        self.route.len()
    }

    pub fn get_edge_by_position(&self, position: usize) -> EdgeIndex {
        self.route[position]
    }

    pub fn vehicle_index(&self) -> VehicleIndex {
        self.vehicle
    }

    pub fn get_destination(&self) -> NodeIndex {
        self.destination
    }
}

impl<T: Copy> CarChoices<T> {
    pub fn get_departure_time(&self) -> Time<T> {
        self.departure_time
    }
}

impl<T: TTFNum + 'static> CarChoices<T> {
    pub fn get_event(&self, agent: AgentIndex) -> Option<Box<dyn Event<T>>> {
        Some(Box::new(VehicleEvent::new(
            agent,
            self.departure_time,
            None,
            VehicleEventType::LeavesOrigin,
        )))
    }
}

impl<T: TTFNum> CarChoices<T> {
    pub fn init_mode_results(&self) -> ModeResults<T> {
        ModeResults::Car(CarResults::with_capacity(self.route_len()))
    }

    pub fn get_expected_travel_time(&self) -> Time<T> {
        self.expected_arrival_time - self.departure_time
    }
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct CarResults<T> {
    route: Vec<EdgeIndex>,
    road_breakpoints: Vec<Time<T>>,
    bottleneck_breakpoints: Vec<Time<T>>,
    pending_breakpoints: Vec<Time<T>>,
    road_time: Time<T>,
    bottleneck_time: Time<T>,
    pending_time: Time<T>,
}

impl<T: TTFNum> CarResults<T> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        CarResults {
            route: Vec::with_capacity(capacity),
            road_breakpoints: Vec::with_capacity(capacity),
            bottleneck_breakpoints: Vec::with_capacity(capacity),
            pending_breakpoints: Vec::with_capacity(capacity),
            ..Default::default()
        }
    }

    fn enters_edge(&mut self, edge: EdgeIndex, at_time: Time<T>) {
        self.route.push(edge);
        self.road_breakpoints.push(at_time);
        if let Some(last_time) = self.pending_breakpoints.last() {
            self.pending_time = self.pending_time + at_time - *last_time;
        }
    }

    fn enters_bottleneck(&mut self, at_time: Time<T>) {
        self.bottleneck_breakpoints.push(at_time);
        if let Some(last_time) = self.road_breakpoints.last() {
            self.road_time = self.road_time + at_time - *last_time;
        }
    }

    fn exits_edge(&mut self, at_time: Time<T>) {
        self.pending_breakpoints.push(at_time);
        if let Some(last_time) = self.bottleneck_breakpoints.last() {
            self.bottleneck_time = self.bottleneck_time + at_time - *last_time;
        }
    }

    pub fn total_travel_time(&self) -> Time<T> {
        self.road_time + self.bottleneck_time + self.pending_time
    }

    pub fn edge_count(&self) -> usize {
        self.route.len()
    }

    pub fn free_flow_travel_time(
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

    pub fn trip_length(&self, road_network: &RoadNetwork<T>) -> Length<T> {
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

#[derive(Debug, Clone, Serialize)]
pub struct AggregateCarResults<T> {
    count: usize,
    congestion: T,
    departure_times: Distribution<Time<T>>,
    arrival_times: Distribution<Time<T>>,
    road_times: Distribution<Time<T>>,
    bottleneck_times: Distribution<Time<T>>,
    pending_times: Distribution<Time<T>>,
    travel_times: Distribution<Time<T>>,
    free_flow_travel_times: Distribution<Time<T>>,
    lengths: Distribution<Length<T>>,
    edge_counts: Distribution<T>,
    utilities: Distribution<Utility<T>>,
    exp_travel_time_diff: Distribution<Time<T>>,
}

impl<T: TTFNum + 'static> AggregateCarResults<T> {
    pub fn from_agent_results<'a>(
        results: Vec<(&'a CarAlternative<T>, &'a AgentResult<T>)>,
        road_network: &RoadNetwork<T>,
    ) -> Self {
        assert!(!results.is_empty(), "Invalid within-day results");
        let departure_times = Distribution::from_iterator(
            results
                .iter()
                .map(|(_, r)| r.departure_time().expect("Invalid within-day result")),
        )
        .unwrap();
        let arrival_times = Distribution::from_iterator(
            results
                .iter()
                .map(|(_, r)| r.arrival_time().expect("Invalid within-day result")),
        )
        .unwrap();
        let road_times = Distribution::from_iterator(results.iter().map(|(_, r)| {
            if let ModeResults::Car(car_results) = r.mode_results() {
                car_results.road_time
            } else {
                panic!("Invalid within-day result");
            }
        }))
        .unwrap();
        let bottleneck_times = Distribution::from_iterator(results.iter().map(|(_, r)| {
            if let ModeResults::Car(car_results) = r.mode_results() {
                car_results.bottleneck_time
            } else {
                panic!("Invalid within-day result");
            }
        }))
        .unwrap();
        let pending_times = Distribution::from_iterator(results.iter().map(|(_, r)| {
            if let ModeResults::Car(car_results) = r.mode_results() {
                car_results.pending_time
            } else {
                panic!("Invalid within-day result");
            }
        }))
        .unwrap();
        let travel_times = Distribution::from_iterator(results.iter().map(|(_, r)| {
            if let ModeResults::Car(car_results) = r.mode_results() {
                car_results.total_travel_time()
            } else {
                panic!("Invalid within-day result");
            }
        }))
        .unwrap();
        let free_flow_travel_times =
            Distribution::from_iterator(results.iter().map(|(car_mode, r)| {
                if let ModeResults::Car(car_results) = r.mode_results() {
                    car_results.free_flow_travel_time(road_network, car_mode.vehicle_index())
                } else {
                    panic!("Invalid within-day result");
                }
            }))
            .unwrap();
        let lengths = Distribution::from_iterator(results.iter().map(|(_, r)| {
            if let ModeResults::Car(car_results) = r.mode_results() {
                car_results.trip_length(road_network)
            } else {
                panic!("Invalid within-day result");
            }
        }))
        .unwrap();
        let edge_counts = Distribution::from_iterator(results.iter().map(|(_, r)| {
            if let ModeResults::Car(car_results) = r.mode_results() {
                T::from_usize(car_results.edge_count()).unwrap()
            } else {
                panic!("Invalid within-day result");
            }
        }))
        .unwrap();
        let utilities = Distribution::from_iterator(
            results
                .iter()
                .map(|(_, r)| r.utility().expect("Invalid within-day result")),
        )
        .unwrap();
        let exp_travel_time_diff = Distribution::from_iterator(results.iter().map(|(_, r)| {
            if let (PreDayChoices::Car(car_choices), ModeResults::Car(car_results)) =
                (r.pre_day_results().get_choices(), r.mode_results())
            {
                let exp_tt = car_choices.get_expected_travel_time();
                let tt = car_results.total_travel_time();
                if exp_tt > Time::zero() {
                    (exp_tt - tt).abs() / exp_tt
                } else {
                    Time::zero()
                }
            } else {
                panic!("Invalid within-day result");
            }
        }))
        .unwrap();
        let congestion = (travel_times.mean().0 - free_flow_travel_times.mean().0)
            / free_flow_travel_times.mean().0;
        AggregateCarResults {
            count: results.len(),
            congestion,
            departure_times,
            arrival_times,
            road_times,
            bottleneck_times,
            pending_times,
            travel_times,
            free_flow_travel_times,
            lengths,
            edge_counts,
            utilities,
            exp_travel_time_diff,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VehicleEventType {
    LeavesOrigin,
    EntersEdge,
    EntersBottleneck,
    ExitsEdge,
    ReachesDestination,
}

#[derive(Debug)]
pub struct VehicleEvent<T> {
    agent: AgentIndex,
    at_time: Time<T>,
    // edge is None only when the trip has not started yet.
    edge: Option<EdgeIndex>,
    event_type: VehicleEventType,
}

impl<T> VehicleEvent<T> {
    pub fn new(
        agent: AgentIndex,
        at_time: Time<T>,
        edge: Option<EdgeIndex>,
        event_type: VehicleEventType,
    ) -> Self {
        VehicleEvent {
            agent,
            at_time,
            edge,
            event_type,
        }
    }

    pub fn set_time(&mut self, at_time: Time<T>) {
        self.at_time = at_time;
    }

    fn get_next_edge(&self, choices: &CarChoices<T>) -> Option<EdgeIndex> {
        let route = choices.get_route();
        if let Some(current_edge) = self.edge {
            if let Some(i) = route.iter().position(|&e| e == current_edge) {
                if i + 1 < route.len() {
                    Some(route[i + 1])
                } else {
                    None
                }
            } else {
                panic!("Agent is on a edge that is not on the planned route.");
            }
        } else {
            Some(route[0])
        }
    }
}

impl<T: TTFNum> VehicleEvent<T> {
    fn record_event(&self, result: &mut AgentResult<T>) {
        if self.event_type == VehicleEventType::LeavesOrigin {
            result.set_departure_time(self.at_time);
        } else if self.event_type == VehicleEventType::ReachesDestination {
            result.set_arrival_time(self.at_time);
        }
        if let ModeResults::Car(car_results) = result.mut_mode_results() {
            match self.event_type {
                VehicleEventType::EntersEdge => {
                    car_results.enters_edge(self.edge.unwrap(), self.at_time);
                }
                VehicleEventType::EntersBottleneck => {
                    car_results.enters_bottleneck(self.at_time);
                }
                VehicleEventType::ExitsEdge => {
                    car_results.exits_edge(self.at_time);
                }
                _ => {}
            }
        } else {
            panic!("Got a road event for an agent with no car result.");
        }
    }
}

impl<T: TTFNum + 'static> Event<T> for VehicleEvent<T> {
    fn execute(
        mut self: Box<Self>,
        _exp_skims: &NetworkSkim<T>,
        state: &mut NetworkState<T>,
        result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<T>,
    ) {
        let road_network_state = state
            .get_mut_road_network()
            .expect("Got a vehicle event but there is no road network state.");
        let agent_result = result.expect("Got a vehicle event with no agent.");
        self.record_event(agent_result);
        let choices =
            if let PreDayChoices::Car(choices) = agent_result.pre_day_results().get_choices() {
                choices
            } else {
                panic!("Got a vehicle event for an agent with no car choices.");
            };
        match self.event_type {
            VehicleEventType::LeavesOrigin => {
                self.edge = Some(self.get_next_edge(choices).expect("Cannot start route."));
                self.event_type = VehicleEventType::EntersEdge;
                events.push(self);
            }
            VehicleEventType::EntersEdge => {
                let vehicle_index = choices.vehicle_index();
                let vehicle = road_network_state.get_vehicle(vehicle_index);
                if let Some(travel_time) =
                    road_network_state[self.edge.unwrap()].enters_edge(vehicle, self.at_time)
                {
                    self.at_time = self.at_time + travel_time;
                    self.event_type = VehicleEventType::EntersBottleneck;
                    events.push(self);
                }
            }
            VehicleEventType::EntersBottleneck => {
                let vehicle_index = choices.vehicle_index();
                let vehicle = road_network_state.get_vehicle(vehicle_index);
                self.event_type = VehicleEventType::ExitsEdge;
                if let Some(bottleneck_event) = road_network_state[self.edge.unwrap()]
                    .enters_bottleneck(vehicle, self.at_time, self)
                {
                    events.push(bottleneck_event);
                }
            }
            VehicleEventType::ExitsEdge => {
                if road_network_state
                    .get_target(self.edge.unwrap())
                    .expect("Current edge is invalid.")
                    == choices.get_destination()
                {
                    // The vehicle has reached its destination.
                    self.event_type = VehicleEventType::ReachesDestination;
                    events.push(self);
                    return;
                }
                self.edge = Some(
                    self.get_next_edge(choices)
                        .expect("Cannot reach destination."),
                );
                self.event_type = VehicleEventType::EntersEdge;
                events.push(self);
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

#[derive(Clone, Debug, Default)]
pub struct CarChoiceAllocation<T: TTFNum> {
    ea_alloc: EAAllocation<T>,
}
