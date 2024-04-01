// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to road events.

use anyhow::Result;
use enum_as_inner::EnumAsInner;
use num_traits::Float;
use petgraph::graph::EdgeIndex;
use ttf::TTF;

use super::results::LegResults;
use super::TravelingMode;
use crate::event::{Event, EventAlloc, EventInput, EventQueue};
use crate::mode::trip::LegType;
use crate::mode::ModeIndex;
use crate::network::road_network::vehicle::Vehicle;
use crate::network::road_network::{OriginalEdgeId, RoadNetworkState};
use crate::population::AgentIndex;
use crate::units::Time;

/// Types of [VehicleEvent].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VehicleEventType {
    /// The trip is starting.
    TripStarts,
    /// A virtual leg is starting.
    BeginsVirtualLeg,
    /// A road leg is starting.
    BeginsRoadLeg,
    /// The vehicle has reached the next edge entry.
    ReachesEdgeEntry,
    /// The vehicle can enter the next edge.
    EntersEdge,
    /// The vehicle has reached its current edge's exit.
    ReachesEdgeExit,
    /// The vehicle reaches its destination.
    EndsRoadLeg,
    /// The trip is ending.
    TripEnds,
}

/// Timings for the event of an edge being taken by a vehicle.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct RoadEvent {
    /// Id of the edge taken.
    pub edge: OriginalEdgeId,
    /// Time at which the vehicle enters the edge (i.e., it enters the in-bottleneck).
    pub entry_time: Time,
}

/// Struct that describes the vehicle events that happen in the within-day model.
///
/// The struct is updated and re-inserted in the event queue when the event is executed.
#[derive(Clone, Debug)]
pub(crate) struct VehicleEvent {
    /// The index of the associated agent.
    agent: AgentIndex,
    /// Index of the mode chosen by the agent.
    mode: ModeIndex,
    /// The time of the event.
    at_time: Time,
    /// Last event timing.
    last_timing: Option<Time>,
    /// Index of the current leg for the agent's trip.
    leg_position: usize,
    /// Index of the current edge in the current leg's route.
    edge_position: usize,
    /// Current route being followed.
    route: Vec<EdgeIndex>,
    /// Type of event.
    event_type: VehicleEventType,
    /// [Vehicle] used for the current leg.
    vehicle: Option<&'static Vehicle>,
    /// If `true`, the vehicle is a phatom, i.e., it does not take any room on the edge.
    is_phantom: bool,
    /// If `true`, the vehicle was a phatom for the last edge it took.
    was_phantom: bool,
}

impl VehicleEvent {
    /// Changes the time of the event.
    pub(crate) fn set_time(&mut self, at_time: Time) {
        self.at_time = at_time;
    }

    /// Set the vehicle to be a phantom.
    pub(crate) fn set_phantom(&mut self) {
        self.is_phantom = true;
    }

    /// Index of the edge the vehicle was previously on (if any).
    pub(crate) fn previous_edge(&self) -> Option<EdgeIndex> {
        if self.edge_position > 0 {
            Some(self.route[self.edge_position - 1])
        } else {
            None
        }
    }

    /// Index of the edge the vehicle is currently on.
    fn current_edge(&self) -> EdgeIndex {
        self.route[self.edge_position]
    }

    /// Returns `true` if the vehicle has reached its destination.
    fn has_reached_destination(&self) -> bool {
        self.edge_position >= self.route.len()
    }

    /// Returns the [AgentIndex] associated with the event.
    pub(crate) fn agent_id(&self) -> AgentIndex {
        self.agent
    }

    /// Creates a new [VehicleEvent] for a given agent that leaves his / her origin at the given
    /// time.
    pub(crate) fn new(agent: AgentIndex, mode: ModeIndex, departure_time: Time) -> Self {
        VehicleEvent {
            agent,
            mode,
            at_time: departure_time,
            last_timing: None,
            leg_position: 0,
            edge_position: 0,
            route: Vec::new(),
            event_type: VehicleEventType::TripStarts,
            vehicle: None,
            is_phantom: false,
            was_phantom: false,
        }
    }
}

impl VehicleEvent {
    fn record_event(&self, leg_results: &mut LegResults) {
        match self.event_type {
            VehicleEventType::BeginsVirtualLeg | VehicleEventType::BeginsRoadLeg => {
                // Set the departure time of the leg.
                debug_assert!(leg_results.departure_time.is_nan());
                leg_results.departure_time = self.at_time;
            }
            VehicleEventType::ReachesEdgeEntry => {
                let road_leg_results = leg_results
                    .class
                    .as_road_mut()
                    .expect("Invalid leg results: Incompatible leg type.");
                // Store the time spent at the previous edge exit (if any).
                debug_assert!(self.edge_position > 0 || self.last_timing == Some(self.at_time));
                road_leg_results.out_bottleneck_time += self.at_time - self.last_timing.unwrap();
            }
            VehicleEventType::EntersEdge => {
                let road_leg_results = leg_results
                    .class
                    .as_road_mut()
                    .expect("Invalid leg results: Incompatible leg type.");
                // Store the time spent at edge entry.
                road_leg_results.in_bottleneck_time += self.at_time - self.last_timing.unwrap();
                // Record the entry time for the current edge.
                road_leg_results.route.push(RoadEvent {
                    edge: crate::network::road_network::original_edge_id_of(self.current_edge()),
                    entry_time: self.at_time,
                });
            }
            VehicleEventType::ReachesEdgeExit => {
                let road_leg_results = leg_results
                    .class
                    .as_road_mut()
                    .expect("Invalid leg results: Incompatible leg type.");
                // Store the time spent on the edge.
                road_leg_results.road_time += self.at_time - self.last_timing.unwrap();
            }
            VehicleEventType::EndsRoadLeg => {
                let road_leg_results = leg_results
                    .class
                    .as_road_mut()
                    .expect("Invalid leg results: Incompatible leg type.");
                // Store the time spent on the last edge exit.
                road_leg_results.out_bottleneck_time += self.at_time - self.last_timing.unwrap();
            }
            _ => {
                // Nothing to record.
            }
        }
    }

    /// Consumes the event and returns a [VehicleEvent] for the next step of the trip.
    fn into_next_step(mut self, travel_time: Option<Time>, trip: &TravelingMode) -> Self {
        self.last_timing = Some(self.at_time);
        self.was_phantom = self.is_phantom;
        self.is_phantom = false;
        match self.event_type {
            VehicleEventType::TripStarts => {
                // Increase the event time according to the delay at origin.
                self.at_time += trip.origin_delay;
                self.into_next_leg(trip, true)
            }
            VehicleEventType::BeginsVirtualLeg => {
                // Increase the event time according to the travel time and leg stopping time.
                self.at_time += travel_time.unwrap();
                self.into_next_leg(trip, false)
            }
            VehicleEventType::BeginsRoadLeg => {
                self.edge_position = 0;
                if self.route.is_empty() {
                    // Empty route (origin = destination), the vehicle immediately reaches the
                    // destination.
                    self.event_type = VehicleEventType::EndsRoadLeg;
                } else {
                    // Next event is the entry in the first leg of the edge.
                    self.event_type = VehicleEventType::ReachesEdgeEntry;
                }
                self
            }
            VehicleEventType::ReachesEdgeEntry => {
                // Next event is to enter the edge.
                self.event_type = VehicleEventType::EntersEdge;
                self
            }
            VehicleEventType::EntersEdge => {
                // Next event is to reach the end of the edge.
                self.event_type = VehicleEventType::ReachesEdgeExit;
                self.at_time += travel_time.unwrap();
                self
            }
            VehicleEventType::ReachesEdgeExit => {
                // Increase the edge index then check if the destination is reached.
                self.edge_position += 1;
                if self.has_reached_destination() {
                    self.event_type = VehicleEventType::EndsRoadLeg;
                } else {
                    self.event_type = VehicleEventType::ReachesEdgeEntry;
                }
                self
            }
            VehicleEventType::EndsRoadLeg => {
                // Increase the event time according to the leg stopping time.
                self.at_time += travel_time.unwrap();
                self.into_next_leg(trip, false)
            }
            VehicleEventType::TripEnds => {
                panic!("The `TripEnds` event does not have a next step");
            }
        }
    }

    /// Consumes the event and returns a [VehicleEvent] for the next leg of the trip.
    fn into_next_leg(mut self, trip: &TravelingMode, first: bool) -> Self {
        if !first {
            self.leg_position += 1;
        }
        match trip.legs.get(self.leg_position).map(|l| &l.class) {
            Some(LegType::Road(_)) => {
                // Next leg is a road leg.
                self.event_type = VehicleEventType::BeginsRoadLeg;
            }
            Some(LegType::Virtual(_)) => {
                // Next leg is virtual.
                self.event_type = VehicleEventType::BeginsVirtualLeg;
            }
            None => {
                // The trip is finished.
                self.event_type = VehicleEventType::TripEnds;
            }
        }
        self
    }

    /// Consumes the event and returns another event with the given route.
    fn with_route(mut self, route: Vec<EdgeIndex>) -> Self {
        self.route = route;
        self
    }

    /// Consumes the event and returns another event with the [Vehicle].
    fn with_vehicle(mut self, vehicle: &'static Vehicle) -> Self {
        self.vehicle = Some(vehicle);
        self
    }

    /// Executes the [VehicleEvent].
    pub(crate) fn execute<'sim: 'event, 'event>(
        self,
        input: &'event mut EventInput<'sim>,
        road_network_state: &'event mut RoadNetworkState,
        alloc: &'event mut EventAlloc,
        events: &'event mut EventQueue,
    ) -> Result<bool> {
        // Unwrap the network, skims and preprocess data into network variables.
        let preprocess_data = input
            .preprocess_data
            .network
            .get_road_network()
            .expect("Got a vehicle event but there is no road network preprocess data.");
        let skims = input
            .skims
            .get_road_network()
            .expect("Got a vehicle event but there is no road network skims.");

        // Load the trip input and the trip results.
        let trip = crate::population::agent_alternative(self.agent.index(), self.mode)
            .as_trip()
            .expect("Got a vehicle event for an agent which did not choose a Trip mode");
        let trip_results = &mut input.agent_results[self.agent]
            .mode_results
            .as_trip_mut()
            .expect("Got a vehicle event without trip results.");

        if self.event_type == VehicleEventType::TripEnds {
            // The trip is finished.
            trip_results.save_results(self.at_time, trip);
            return Ok(true);
        }

        // Load the leg input and the leg results.
        debug_assert!(self.leg_position < trip.legs.len());
        let leg = trip
            .legs
            .get(self.leg_position)
            .expect("Invalid trip: Incompatible number of legs.");
        let leg_results = trip_results
            .legs
            .get_mut(self.leg_position)
            .expect("Invalid leg results: Incompatible number of legs.");

        let current_time = self.at_time;

        self.record_event(leg_results);

        if let Some(next_event) = match self.event_type {
            VehicleEventType::TripStarts => Some(self.into_next_step(None, trip)),
            VehicleEventType::BeginsVirtualLeg => {
                // Compute and store the travel time of the leg.
                let ttf = leg.class.as_virtual().expect("Not a virtual leg");
                let travel_time = ttf.eval(self.at_time);
                // Store the travel time and arrival time.
                leg_results.save_results(travel_time, leg);
                Some(self.into_next_step(Some(travel_time + leg.stopping_time), trip))
            }
            VehicleEventType::BeginsRoadLeg => {
                let road_leg = leg.class.as_road().expect("Not a road leg");
                let road_leg_results = leg_results
                    .class
                    .as_road_mut()
                    .expect("Invalid leg results: Incompatible leg type.");
                let (exp_arrival_time, route) =
                    if let Some(route) = std::mem::take(&mut road_leg_results.expected_route) {
                        let exp_travel_time = road_leg_results.pre_exp_arrival_time
                            - road_leg_results.pre_exp_departure_time;
                        let exp_arrival_time = current_time + exp_travel_time;
                        (exp_arrival_time, route.clone())
                    } else {
                        // Compute the route between origin and destination of the current leg.
                        let uvehicle = preprocess_data.get_unique_vehicle_index(road_leg.vehicle);
                        let vehicle_skims = skims[uvehicle]
                            .as_ref()
                            .expect("Road network skims are empty.");
                        super::get_arrival_time_and_route(
                            road_leg,
                            self.at_time,
                            vehicle_skims,
                            input.progress_bar.clone(),
                            &mut alloc.ea_alloc,
                        )?
                    };
                // Store the expected arrival time at destination in the results.
                road_leg_results.exp_arrival_time = exp_arrival_time;
                // Compute and store the route free-flow travel time and length (if it was not
                // computed already).
                if road_leg_results.route_free_flow_travel_time.is_nan() {
                    road_leg_results.route_free_flow_travel_time =
                        crate::network::road_network::route_free_flow_travel_time(
                            route.iter().copied(),
                            road_leg.vehicle,
                        );
                }
                if road_leg_results.length.is_nan() {
                    road_leg_results.length =
                        crate::network::road_network::route_length(route.iter().copied());
                }
                let vehicle = crate::network::road_network::vehicle_with_id(road_leg.vehicle);
                Some(
                    self.with_route(route)
                        .with_vehicle(vehicle)
                        .into_next_step(None, trip),
                )
            }

            VehicleEventType::ReachesEdgeEntry => {
                // Try to enter the edge.
                road_network_state.try_enter_edge(
                    self.current_edge(),
                    self.at_time,
                    self.vehicle.expect("Vehicle should be set at this point"),
                    self.into_next_step(None, trip),
                    events,
                )
            }

            VehicleEventType::EntersEdge => {
                // Get the road travel time.
                let travel_time = road_network_state.enters_edge(
                    self.current_edge(),
                    self.previous_edge(),
                    self.at_time,
                    self.vehicle.expect("Vehicle should be set at this point"),
                    self.agent,
                    self.is_phantom,
                    self.was_phantom,
                    input,
                    alloc,
                    events,
                )?;
                Some(self.into_next_step(Some(travel_time), trip))
            }

            VehicleEventType::ReachesEdgeExit => {
                // Try to cross the bottleneck.
                road_network_state.try_exit_edge(
                    self.current_edge(),
                    self.at_time,
                    self.vehicle.expect("Vehicle should be set at this point"),
                    self.into_next_step(None, trip),
                    events,
                )
            }

            VehicleEventType::EndsRoadLeg => {
                let road_leg_results = leg_results
                    .class
                    .as_road()
                    .expect("Invalid leg results: Incompatible leg type.");
                // Compute and store the travel time of the leg.
                let travel_time = road_leg_results.road_time
                    + road_leg_results.in_bottleneck_time
                    + road_leg_results.out_bottleneck_time;
                leg_results.save_results(travel_time, leg);
                if let Some(previous_edge) = self.previous_edge() {
                    // Release the vehicle from the last edge taken.
                    road_network_state.release_from_edge(
                        previous_edge,
                        self.at_time,
                        self.vehicle.expect("Vehicle should be set at this point"),
                        self.is_phantom,
                        input,
                        alloc,
                        events,
                    )?;
                }
                Some(self.into_next_step(Some(leg.stopping_time), trip))
            }

            VehicleEventType::TripEnds => {
                unreachable!();
            }
        } {
            if next_event.at_time == current_time {
                // Next event can be executed immediately.
                return next_event.execute(input, road_network_state, alloc, events);
            } else {
                debug_assert!(next_event.at_time > current_time);
                // Push next event to the queue.
                events.push(Box::new(next_event));
            }
        }
        Ok(false)
    }
}

impl Event for VehicleEvent {
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim>,
        road_network_state: &'event mut RoadNetworkState,
        alloc: &'event mut EventAlloc,
        events: &'event mut EventQueue,
    ) -> Result<bool> {
        (*self).execute(input, road_network_state, alloc, events)
    }

    fn get_time(&self) -> Time {
        self.at_time
    }
}
