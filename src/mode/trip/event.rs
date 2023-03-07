// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to road events.
use anyhow::{anyhow, Result};
use hashbrown::HashSet;
use num_traits::{Float, Zero};
use petgraph::graph::{EdgeIndex, NodeIndex};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::TTFNum;

use super::results::RoadLegResults;
use super::TravelingMode;
use crate::agent::AgentIndex;
use crate::event::{Event, EventQueue};
use crate::mode::trip::LegType;
use crate::network::road_network::skim::{EAAllocation, RoadNetworkSkim};
use crate::network::road_network::state::BottleneckStatus;
use crate::network::{Network, NetworkSkim, NetworkState};
use crate::simulation::results::AgentResult;
use crate::simulation::PreprocessingData;
use crate::units::Time;

/// Types of [VehicleEvent].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VehicleEventType {
    /// A virtual leg is starting.
    BeginsVirtualLeg,
    /// The vehicle leaves its origin.
    LeavesOrigin,
    /// The vehicle enters the in-bottleneck of the next edge.
    EntersInBottleneck,
    /// The vehicle enters the running part of its current edge.
    EntersRoadSegment,
    /// The vehicle enters the out-bottleneck of its current edge.
    EntersOutBottleneck,
    /// The vehicle exits its current edge (but it might still be pending).
    ExitsEdge,
    /// The vehicle reaches its destination.
    ReachesDestination,
}

/// Timings for the event of an edge being taken by a vehicle.
#[derive(Debug, Default, Clone, PartialEq, Serialize)]
#[serde(into = "TransparentRoadEvent<T>")]
#[serde(bound(serialize = "T: Clone + Serialize"))]
pub struct RoadEvent<T> {
    /// Id of the edge taken.
    pub edge: EdgeIndex,
    /// Time at which the vehicle enters the edge (i.e., it enters the in-bottleneck).
    pub edge_entry: Time<T>,
}

#[derive(Debug, Default, Clone, Deserialize, Serialize, JsonSchema)]
#[serde(bound(serialize = "T: Clone + Serialize"))]
#[schemars(title = "RoadEvent")]
#[schemars(
    description = "Array `[e, t]`, where `e` is the index of the edge taken and `t` is the entry time of the vehicle on this edges"
)]
pub(crate) struct TransparentRoadEvent<T>(usize, Time<T>);

impl<T> From<RoadEvent<T>> for TransparentRoadEvent<T> {
    fn from(v: RoadEvent<T>) -> Self {
        Self(v.edge.index(), v.edge_entry)
    }
}

/// Timings for the event of an edge being taken by a vehicle.
#[derive(Debug, Default, Clone)]
pub struct TemporaryRoadEvent<T> {
    /// Id of the edge taken.
    edge: EdgeIndex,
    /// Time at which the vehicle enters the edge (i.e., it enters the in-bottleneck).
    edge_entry: Option<Time<T>>,
    /// Time at which the vehicle enters the road segment of the edge (i.e., it exits the
    /// in-bottleneck).
    segment_entry: Option<Time<T>>,
    /// Time at which the vehicle enters the out-bottleneck of the edge (i.e., it exits the road
    /// segment).
    out_bottleneck_entry: Option<Time<T>>,
    /// Time at which the vehicle exits the out-bottleneck of the edge (note that the vehicle might
    /// still be pending on the edge).
    edge_exit: Option<Time<T>>,
}

impl<T> TemporaryRoadEvent<T> {
    fn new(edge: EdgeIndex) -> Self {
        Self {
            edge,
            edge_entry: None,
            segment_entry: None,
            out_bottleneck_entry: None,
            edge_exit: None,
        }
    }
}

impl<T> From<TemporaryRoadEvent<T>> for RoadEvent<T> {
    fn from(v: TemporaryRoadEvent<T>) -> Self {
        Self {
            edge: v.edge,
            edge_entry: v.edge_entry.unwrap(),
        }
    }
}

/// Struct that describes the vehicle events that happen in the within-day model.
///
/// The struct is updated and re-inserted in the event queue when the event is executed.
#[derive(Clone, Debug)]
pub struct VehicleEvent<'a, T> {
    /// The index of the associated agent.
    agent: AgentIndex,
    /// The description of the trip.
    trip: &'a TravelingMode<T>,
    /// The time of the event.
    at_time: Time<T>,
    /// Index of the current leg for the agent's trip.
    leg_position: usize,
    /// Index of the current edge in the current leg's route.
    edge_position: usize,
    /// Current route being followed.
    route: Vec<EdgeIndex>,
    /// Current [TemporaryRoadEvent].
    current_event: Option<TemporaryRoadEvent<T>>,
    /// Type of event.
    event_type: VehicleEventType,
}

impl<T> VehicleEvent<'_, T> {
    /// Changes the time of the event.
    pub fn set_time(&mut self, at_time: Time<T>) {
        self.at_time = at_time;
    }

    fn set_edge_entry(&mut self, time: Time<T>) {
        self.current_event.as_mut().unwrap().edge_entry = Some(time);
    }

    fn set_segment_entry(&mut self, time: Time<T>) {
        self.current_event.as_mut().unwrap().segment_entry = Some(time);
    }

    fn set_out_bottleneck_entry(&mut self, time: Time<T>) {
        self.current_event.as_mut().unwrap().out_bottleneck_entry = Some(time);
    }

    fn set_edge_exit(&mut self, time: Time<T>) {
        self.current_event.as_mut().unwrap().edge_exit = Some(time);
    }

    /// Modifies the VehicleEvent in place in preparation for the next leg.
    ///
    /// Returns `false` if there is no next leg.
    fn as_next_leg(&mut self) -> bool {
        self.leg_position += 1;
        match self.trip.legs.get(self.leg_position).map(|l| &l.class) {
            Some(LegType::Road(_)) => {
                // Next leg is a road leg.
                self.event_type = VehicleEventType::LeavesOrigin;
                true
            }
            Some(LegType::Virtual(_)) => {
                // Next leg is virtual.
                self.event_type = VehicleEventType::BeginsVirtualLeg;
                true
            }
            None => {
                // The trip is finished.
                false
            }
        }
    }

    /// Index of the edge the vehicle was previously on (if any).
    pub fn previous_edge(&self) -> Option<EdgeIndex> {
        if self.edge_position > 0 {
            Some(self.route[self.edge_position - 1])
        } else {
            None
        }
    }

    /// Index of the edge the vehicle is currently on.
    pub fn current_edge(&self) -> EdgeIndex {
        self.route[self.edge_position]
    }
}

impl<'a, T: TTFNum> VehicleEvent<'a, T> {
    /// Creates a new [VehicleEvent] for a given agent that leaves his / her origin at the given
    /// time.
    fn new(
        agent: AgentIndex,
        trip: &'a TravelingMode<T>,
        departure_time: Time<T>,
        first_event: VehicleEventType,
    ) -> Self {
        VehicleEvent {
            agent,
            trip,
            at_time: departure_time + trip.origin_delay,
            leg_position: 0,
            edge_position: 0,
            route: Vec::new(),
            current_event: None,
            event_type: first_event,
        }
    }

    /// Creates a new [VehicleEvent] for a given agent that leaves his / her origin at the given
    /// time, where the first leg of the trip is a road leg.
    ///
    /// The event's execution time is the departure time from origin, plus the origin delay time.
    pub fn new_road(
        agent: AgentIndex,
        trip: &'a TravelingMode<T>,
        departure_time: Time<T>,
    ) -> Self {
        VehicleEvent::new(agent, trip, departure_time, VehicleEventType::LeavesOrigin)
    }

    /// Creates a new [VehicleEvent] for a given agent that leaves his / her origin at the given
    /// time, where the first leg of the trip is a virtual leg.
    ///
    /// The event's execution time is the departure time from origin, plus the origin delay time.
    pub fn new_virtual(
        agent: AgentIndex,
        trip: &'a TravelingMode<T>,
        departure_time: Time<T>,
    ) -> Self {
        VehicleEvent::new(
            agent,
            trip,
            departure_time,
            VehicleEventType::BeginsVirtualLeg,
        )
    }

    /// Records the edge just taken by the vehicle.
    fn record_edge(&mut self, result: &mut RoadLegResults<T>) {
        let road_event = std::mem::take(&mut self.current_event).unwrap();
        result.in_bottleneck_time +=
            road_event.segment_entry.unwrap() - road_event.edge_entry.unwrap();
        result.road_time +=
            road_event.out_bottleneck_entry.unwrap() - road_event.segment_entry.unwrap();
        result.out_bottleneck_time +=
            road_event.edge_exit.unwrap() - road_event.out_bottleneck_entry.unwrap();
        result.route.push(road_event.into());
    }

    pub fn execute<'b: 'a>(
        self,
        network: &'b Network<T>,
        skims: &NetworkSkim<T>,
        state: &mut NetworkState<'a, T>,
        preprocess_data: &PreprocessingData<T>,
        mut result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<'a, T>,
    ) -> Result<()> {
        // Unwrap the network, skims, state and preprocess data into network variables.
        let road_network = network
            .get_road_network()
            .expect("Got a vehicle event but there is no road network.");
        let road_network_skims = skims
            .get_road_network()
            .expect("Got a vehicle event but there is no road network skims.");
        let road_network_state = state
            .get_mut_road_network()
            .expect("Got a vehicle event but there is no road network state.");
        let road_network_preprocess_data = preprocess_data
            .network
            .get_road_network()
            .expect("Got a vehicle event but there is no road network preprocess data.");

        let trip_results = result
            .as_mut()
            .expect("Got a vehicle event with no agent.")
            .mode_results
            .as_trip_mut()
            .expect("Got a vehicle event without trip results.");
        let leg = self
            .trip
            .legs
            .get(self.leg_position)
            .expect("Invalid trip: Incompatible number of legs.");
        let leg_results = trip_results
            .legs
            .get_mut(self.leg_position)
            .expect("Invalid leg results: Incompatible number of legs.");
        debug_assert!(self.leg_position < self.trip.legs.len());

        match self.event_type {
            VehicleEventType::BeginsVirtualLeg => {
                // Set the departure time of the leg.
                debug_assert!(leg_results.departure_time.is_nan());
                leg_results.departure_time = self.at_time;
                let ttf = leg.class.as_virtual().expect("Not a virtual leg");
                // Compute and store the travel time of the leg.
                let travel_time = ttf.eval(self.at_time);
                leg_results.save_results(travel_time, leg);
                // Increase the event time according to the travel time and leg stopping time.
                self.at_time += travel_time + leg.stopping_time;
                if self.as_next_leg() {
                    // Next execution of the event is for the next leg.
                    if leg.stopping_time.is_zero() {
                        // We can execute the next event directly because the time is the same.
                        self.execute(network, skims, state, preprocess_data, result, events)?;
                    } else {
                        events.push(self);
                    }
                } else {
                    // The trip is finished.
                    trip_results.save_results(self.at_time, self.trip);
                }
            }

            VehicleEventType::LeavesOrigin => {
                // Set the departure time of the leg.
                debug_assert!(leg_results.departure_time.is_nan());
                leg_results.departure_time = self.at_time;
                let road_leg = leg.class.as_road().expect("Not a road leg");
                // Compute the route between origin and destination of the current leg.
                let uvehicle = road_network_preprocess_data.unique_vehicles[road_leg.vehicle];
                let vehicle_skims = road_network_skims[uvehicle]
                    .as_ref()
                    .expect("Road network skims are empty.");
                let (exp_arrival_time, route) = get_arrival_time_and_route(
                    road_leg.origin,
                    road_leg.destination,
                    self.at_time,
                    vehicle_skims,
                    &mut Default::default(),
                )?;
                if cfg!(debug_assertions) {
                    check_route(&route);
                }
                self.route = route;
                self.edge_position = 0;
                self.current_event = None;
                // Store in the results the expected arrival time at destination.
                let road_leg_results = leg_results
                    .class
                    .as_road_mut()
                    .expect("Invalid leg results: Incompatible leg type.");
                road_leg_results.exp_arrival_time = exp_arrival_time;
                // Compute and store the route free-flow travel time and length.
                road_leg_results.route_free_flow_travel_time = road_network
                    .route_free_flow_travel_time(self.route.iter().copied(), road_leg.vehicle);
                road_leg_results.length = road_network.route_length(self.route.iter().copied());
                // Store the global free-flow travel time.
                road_leg_results.global_free_flow_travel_time = *road_network_preprocess_data
                    .free_flow_travel_times[uvehicle]
                    .get(&(road_leg.origin, road_leg.destination))
                    .expect("The free flow travel time of the OD pair has not been computed.");
                // Next event in the entry in the first leg of the edge.
                self.event_type = VehicleEventType::EntersInBottleneck;
                // We can execute the next event directly because the time is the same.
                self.execute(network, skims, state, preprocess_data, result, events)?;
            }

            VehicleEventType::EntersInBottleneck => {
                let road_leg = leg.class.as_road().expect("Not a road leg");
                let vehicle = &road_network[road_leg.vehicle];
                let current_edge = self.route[self.edge_position];
                // Set the current edge.
                self.current_event = Some(TemporaryRoadEvent::new(current_edge));
                self.set_edge_entry(self.at_time);
                // Update the event type for the next execution of the event.
                self.event_type = VehicleEventType::EntersRoadSegment;
                // Try to cross the bottleneck.
                match road_network_state[current_edge].enters_in_bottleneck(vehicle, self) {
                    BottleneckStatus::Open(vehicle_event) => {
                        // The bottleneck is open, the vehicle immediately exits it.
                        // We can execute the next event directly because the time is the same.
                        vehicle_event.execute(
                            network,
                            skims,
                            state,
                            preprocess_data,
                            result,
                            events,
                        )?;
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

            VehicleEventType::EntersRoadSegment => {
                let road_leg = leg.class.as_road().expect("Not a road leg");
                let vehicle = &road_network[road_leg.vehicle];
                // Record the event.
                self.set_segment_entry(self.at_time);
                // Compute the road travel time.
                let travel_time = road_network_state.enters_road(&self, vehicle, self.at_time);
                self.event_type = VehicleEventType::EntersOutBottleneck;
                if travel_time == Time::zero() {
                    // We can execute the next event directly because the time is the same.
                    self.execute(network, skims, state, preprocess_data, result, events)?;
                } else {
                    self.at_time += travel_time;
                    events.push(self);
                }
            }

            VehicleEventType::EntersOutBottleneck => {
                let road_leg = leg.class.as_road().expect("Not a road leg");
                let vehicle = &road_network[road_leg.vehicle];
                let current_edge = self.route[self.edge_position];
                // Record the event.
                self.set_out_bottleneck_entry(self.at_time);
                // Update the event type for the next execution of the event.
                self.event_type = VehicleEventType::ExitsEdge;
                // Try to cross the bottleneck.
                match road_network_state[current_edge].enters_out_bottleneck(vehicle, self) {
                    BottleneckStatus::Open(vehicle_event) => {
                        vehicle_event.execute(
                            network,
                            skims,
                            state,
                            preprocess_data,
                            result,
                            events,
                        )?;
                    }
                    BottleneckStatus::Closed(Some(bottleneck_event)) => {
                        events.push(Box::new(bottleneck_event));
                    }
                    BottleneckStatus::Closed(None) => {}
                }
            }

            VehicleEventType::ExitsEdge => {
                let road_leg_results = leg_results
                    .class
                    .as_road_mut()
                    .expect("Invalid leg results: Incompatible leg type.");
                // Record the event.
                self.set_edge_exit(self.at_time);
                self.record_edge(road_leg_results);
                // Switch to the next edge.
                if self.edge_position + 1 < self.route.len() {
                    self.edge_position += 1;
                    self.event_type = VehicleEventType::EntersInBottleneck;
                    // We can execute the next event directly because the time is the same.
                    // TODO: This is no true when there is spillback.
                    self.execute(network, skims, state, preprocess_data, result, events)?;
                } else {
                    // The vehicle has reached its destination.
                    debug_assert!(
                        road_network
                            .get_endpoints(self.route[self.edge_position])
                            .expect("Current edge is invalid.")
                            .1
                            == leg.class.as_road().expect("Not a road leg").destination
                    );
                    self.event_type = VehicleEventType::ReachesDestination;
                    // We can execute the next event directly because the time is the same.
                    self.execute(network, skims, state, preprocess_data, result, events)?;
                }
            }

            VehicleEventType::ReachesDestination => {
                // TODO: Remove from previous edge.
                let road_leg_results = leg_results
                    .class
                    .as_road()
                    .expect("Invalid leg results: Incompatible leg type.");
                // Compute and store the travel time of the leg.
                let travel_time = road_leg_results.road_time
                    + road_leg_results.in_bottleneck_time
                    + road_leg_results.out_bottleneck_time;
                leg_results.save_results(travel_time, leg);
                // Increase the event time according to the leg stopping time.
                self.at_time += leg.stopping_time;
                if self.as_next_leg() {
                    // Next execution of the event is for the next leg.
                    if leg.stopping_time.is_zero() {
                        // We can execute the next event directly because the time is the same.
                        self.execute(network, skims, state, preprocess_data, result, events)?;
                    } else {
                        events.push(self);
                    }
                } else {
                    // The trip is finished.
                    trip_results.save_results(self.at_time, self.trip);
                }
            }
        }
        Ok(())
    }
}

impl<'a, T: TTFNum> Event<'a, T> for VehicleEvent<'a, T> {
    fn execute<'b: 'a>(
        self: Box<Self>,
        network: &'b Network<T>,
        skims: &NetworkSkim<T>,
        state: &mut NetworkState<'a, T>,
        preprocess_data: &PreprocessingData<T>,
        result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<'a, T>,
    ) -> Result<()> {
        self.execute(network, skims, state, preprocess_data, result, events)
    }

    fn get_time(&self) -> Time<T> {
        self.at_time
    }

    fn get_agent_index(&self) -> Option<AgentIndex> {
        Some(self.agent)
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
    alloc: &mut EAAllocation<T>,
) -> Result<(Time<T>, Vec<EdgeIndex>)> {
    if let Some((arrival_time, route)) =
        skims.earliest_arrival_query(origin, destination, departure_time, alloc)?
    {
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

/// Run checks to ensure that the computed route is valid.
fn check_route(route: &[EdgeIndex]) {
    // Check that there is no loop in the route.
    let n = route.iter().collect::<HashSet<_>>().len();
    assert_eq!(n, route.len(), "Invalid route: {route:?}");
}
