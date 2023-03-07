// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of [RoadNetworkState].
use std::collections::VecDeque;
use std::marker::PhantomData;

use anyhow::Result;
use enum_as_inner::EnumAsInner;
use num_traits::{Float, Zero};
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use ttf::{PwlXYF, TTFNum, TTF, XYF};

use super::super::{Network, NetworkSkim, NetworkState};
use super::vehicle::Vehicle;
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetwork, RoadNetworkPreprocessingData, RoadNode};
use crate::event::{Event, EventQueue};
use crate::mode::trip::event::VehicleEvent;
use crate::simulation::results::AgentResult;
use crate::simulation::PreprocessingData;
use crate::units::{Flow, Interval, Length, NoUnit, Time};

/// Struct that holds data on the current state of a [RoadNode].
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct RoadNodeState<'a> {
    reference: &'a RoadNode,
    node_index: NodeIndex,
}

impl<'a> RoadNodeState<'a> {
    /// Creates a new RoadNodeState.
    pub const fn new(reference: &'a RoadNode, node_index: NodeIndex) -> Self {
        RoadNodeState {
            reference,
            node_index,
        }
    }
}

/// Struct representing the current state of the running part of a [RoadEdge].
#[derive(Clone, Debug)]
struct RoadSegment<T> {
    /// Total length of the vehicles currently on the segment.
    occupied_length: Length<T>,
    /// History of the length of vehicles on the segment.
    length_history: PwlXYFBuilder<Time<T>, Length<T>, NoUnit<T>>,
}

impl<T: TTFNum> RoadSegment<T> {
    fn new(period: Interval<T>, interval: Time<T>) -> Self {
        let length_history: PwlXYFBuilder<Time<T>, Length<T>, NoUnit<T>> =
            PwlXYFBuilder::new(period.0, interval);
        RoadSegment {
            occupied_length: Length::zero(),
            length_history,
        }
    }

    /// Records the entry of a new vehicle on the segment.
    fn enters(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) {
        let new_length = self.occupied_length + vehicle.get_headway();
        self.set_length(new_length, current_time);
    }

    /// Records the exit of a vehicle from the segment.
    fn exits(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) {
        let new_length = self.occupied_length - vehicle.get_headway();
        self.set_length(new_length, current_time);
    }

    /// Changes the occupied length to the new value.
    ///
    /// Also records the change of value.
    fn set_length(&mut self, length: Length<T>, timing: Time<T>) {
        self.length_history.push(timing, length);
        self.occupied_length = length;
    }

    /// Consumes the [RoadSegment] and returns a [PwlXYF] with the simulated Length.
    fn into_simulated_length_function(self) -> XYF<Time<T>, Length<T>, NoUnit<T>> {
        self.length_history.finish()
    }
}

/// Entry for a [BottleneckQueue].
#[derive(Clone, Debug)]
struct BottleneckEntry<'a, T> {
    /// Next [VehicleEvent] to execute for the vehicle waiting.
    event: VehicleEvent<'a, T>,
    /// Closing time induced by the vehicle waiting.
    closing_time: Time<T>,
    /// Length of the vehicle waiting.
    vehicle_length: Length<T>,
}

/// Type representing a queue of vehicles waiting at a Bottleneck.
type BottleneckQueue<'a, T> = VecDeque<BottleneckEntry<'a, T>>;

/// Enum representing the status of a Bottleneck (open or closed).
///
/// If the bottleneck is open, the enum store the VehicleEvent associated to the vehicle that just
/// entered.
///
/// If the bottleneck is closed, the enum can store a [BottleneckEvent] that triggers the next time
/// it open.
#[derive(Clone, Debug)]
enum BottleneckResult<T> {
    /// The bottleneck is open.
    Open,
    /// The bottleneck is closed.
    ///
    /// If a [BottleneckEvent] is not created yet, it is returned here.
    Closed(Option<BottleneckEvent<T>>),
}

#[derive(Clone, Copy, Debug, EnumAsInner)]
enum BottleneckStatus<T> {
    /// The bottleneck is open.
    Open,
    /// The bottleneck is closed until the given time.
    Closed(Time<T>),
    /// A vehicle, with the given length, wants to cross the bottleneck but there is not enough
    /// room for it to enter the edge.
    Pending(Length<T>),
}

/// Enum representing the position of a bottleneck.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BottleneckPosition {
    /// The bottleneck is at the beginning of the edge.
    In,
    /// The bottleneck is at the end of the edge.
    Out,
}

/// Struct representing the current state of the bottleneck queue of an edge.
#[derive(Clone, Debug)]
struct Bottleneck<'a, T> {
    /// Effective flow of the bottleneck (i.e., bottleneck flow of all the lanes of the edge).
    effective_flow: Flow<T>,
    /// In or out bottleneck.
    position: BottleneckPosition,
    /// Indicates the status of the botleneck (open, closed or pending).
    status: BottleneckStatus<T>,
    /// Queue of vehicles currently waiting at the bottleneck.
    queue: BottleneckQueue<'a, T>,
    /// Waiting time PwlTTF function.
    waiting_time_history: PwlXYFBuilder<Time<T>, Time<T>, Time<T>>,
}

impl<'a, T> Bottleneck<'a, T> {
    /// Return the next [BottleneckEntry] in the [BottleneckQueue] of the Bottleneck.
    fn pop(&mut self) -> Option<BottleneckEntry<'a, T>> {
        self.queue.pop_front()
    }
    /// Return a reference to the next [BottleneckEntry] in the [BottleneckQueue] of the Bottleneck,
    /// without removing it from the queue.
    fn peek(&self) -> Option<&BottleneckEntry<'a, T>> {
        self.queue.front()
    }
}

impl<T: TTFNum> Bottleneck<'_, T> {
    fn new(
        effective_flow: Flow<T>,
        position: BottleneckPosition,
        period: Interval<T>,
        interval: Time<T>,
    ) -> Self {
        let waiting_time_history = PwlXYFBuilder::new(period.0, interval);
        Bottleneck {
            effective_flow,
            position,
            status: BottleneckStatus::Open,
            queue: Default::default(),
            waiting_time_history,
        }
    }

    /// Returns the closing time of the bottleneck given the vehicle exiting it.
    fn get_closing_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        vehicle.get_pce() / self.effective_flow
    }

    /// Consumes the [Bottleneck] and returns a [PwlTTF] with the simulated waiting time.
    fn into_simulated_ttf(self) -> TTF<Time<T>> {
        let mut ttf = self.waiting_time_history.finish();
        ttf.ensure_fifo();
        ttf
    }

    /// Sets the status of the bottleneck to pending, with the given length of the first vehicle
    /// pending.
    fn set_pending_state(&mut self, vehicle_length: Length<T>) {
        self.status = BottleneckStatus::Pending(vehicle_length);
    }
}

impl<'a, T: TTFNum> Bottleneck<'a, T> {
    /// Records the entry of a vehicle in the bottleneck.
    ///
    /// Returns the status of the bottleneck as a [BottleneckResult].
    /// This is the status of the bottleneck just before the entry (i.e., if the bottleneck is open
    /// when the vehicle enters, the status of the bottleneck is `Open`).
    fn enters(
        &mut self,
        event: VehicleEvent<'a, T>,
        vehicle: &'a Vehicle<T>,
        edge_index: EdgeIndex,
        has_room: bool,
    ) -> Option<Box<dyn Event<'a, T> + 'a>> {
        let current_time = event.get_time();
        let closing_time = self.get_closing_time(vehicle);
        let is_open = match self.status {
            BottleneckStatus::Open => true,
            BottleneckStatus::Closed(next_opening) => next_opening <= current_time,
            BottleneckStatus::Pending(_) => false,
        };
        match (is_open, has_room) {
            (true, true) => {
                debug_assert!(self.queue.is_empty());
                // The bottleneck is open and there is room.
                self.status = BottleneckStatus::Closed(current_time + closing_time);
                self.record(current_time, current_time);
                // The vehicle can cross immediately.
                Some(Box::new(event))
            }
            (true, false) => {
                debug_assert!(self.queue.is_empty());
                // The bottleneck is open but there is not enough room for the vehicle.
                self.status = BottleneckStatus::Pending(vehicle.get_headway());
                self.queue.push_back(BottleneckEntry {
                    event,
                    closing_time,
                    vehicle_length: vehicle.get_headway(),
                });
                // No event is planned for now. When enough room gets free, an event will trigger
                // the vehicle exit.
                None
            }
            (false, true) | (false, false) => {
                // The bottleneck is closed.
                let bottleneck_event = if self.queue.is_empty() {
                    // A queue starts to build up.
                    // Create a BottleneckEvent to trigger the exit from the bottleneck at the
                    // correct time.
                    // Note: At this point, the status of the bottleneck can only be `Closed` (the
                    // bottleneck is not open and there would be a non-empty queue if the status
                    // was `Pending`).
                    Some(Box::new(BottleneckEvent::new(
                        self.status.into_closed().expect("Invalid bottleneck state"),
                        edge_index,
                        self.position,
                    )))
                } else {
                    // A BottleneckEvent already exists or the bottleneck status is `Pending`.
                    None
                };
                self.status = match self.status {
                    BottleneckStatus::Open => unreachable!(),
                    BottleneckStatus::Closed(next_opening) => {
                        BottleneckStatus::Closed(next_opening + closing_time)
                    }
                    BottleneckStatus::Pending(l) => BottleneckStatus::Pending(l),
                };
                self.queue.push_back(BottleneckEntry {
                    event,
                    closing_time,
                    vehicle_length: vehicle.get_headway(),
                });
                bottleneck_event
            }
        }
    }

    /// Records the entry and exit of a vehicle in the bottleneck at a given time.
    fn record(&mut self, entry_time: Time<T>, exit_time: Time<T>) {
        self.waiting_time_history
            .push(entry_time, exit_time - entry_time);
    }

    /// Returns `true` if there is a vehicle pending to enter the edge and the edge's available
    /// length is large enough to make it enter.
    fn pending_vehicle_can_enter(&self, edge_length: Length<T>) -> bool {
        self.status
            .into_pending()
            .map(|vl| vl >= edge_length)
            .unwrap_or(false)
    }
}

#[derive(Clone, Debug)]
struct SimulatedFunctions<T> {
    in_bottleneck: TTF<Time<T>>,
    out_bottleneck: TTF<Time<T>>,
    road: XYF<Time<T>, Length<T>, NoUnit<T>>,
}

/// Struct that holds data on the current state of a [RoadEdge].
#[derive(Clone, Debug)]
pub struct RoadEdgeState<'a, T> {
    reference: &'a RoadEdge<T>,
    edge_index: EdgeIndex,
    // TODO: Can we allow multiple RoadSegment on the same edge (e.g., a segment every 200m)?
    road: RoadSegment<T>,
    /// Bottleneck representing the state of the bottleneck at the beginning of the edge, or `None`
    /// if the edge has no in-bottleneck (i.e., inflow is infinite).
    in_bottleneck: Option<Bottleneck<'a, T>>,
    /// Bottleneck representing the state of the bottleneck at the end of the edge, or `None` if
    /// the edge has no out-bottleneck (i.e., outflow is infinite).
    out_bottleneck: Option<Bottleneck<'a, T>>,
    /// Current length available for vehicles on the edge, i.e., total length of the edge minus the
    /// total headway length of vehicles currently on the road segment or out bottleneck of the
    /// edge, or on the in bottleneck of a downstream edge.
    /// Equal to `None` if there is no restriction to the length of vehicles that can be on the
    /// edge (i.e., the parameter `spillback` of the edge is `false`).
    available_length: Option<Length<T>>,
}

impl<'a, T: TTFNum> RoadEdgeState<'a, T> {
    /// Creates a new RoadEdgeState.
    pub fn new(
        reference: &'a RoadEdge<T>,
        edge_index: EdgeIndex,
        recording_period: Interval<T>,
        recording_interval: Time<T>,
    ) -> Self {
        let effective_inflow = reference.get_effective_inflow();
        let in_bottleneck = if effective_inflow.is_finite() || reference.spillback {
            Some(Bottleneck::new(
                effective_inflow,
                BottleneckPosition::In,
                recording_period,
                recording_interval,
            ))
        } else {
            None
        };
        let effective_outflow = reference.get_effective_outflow();
        let out_bottleneck = if effective_outflow.is_finite() {
            Some(Bottleneck::new(
                effective_outflow,
                BottleneckPosition::Out,
                recording_period,
                recording_interval,
            ))
        } else {
            None
        };
        let available_length = if reference.spillback {
            Some(reference.total_length())
        } else {
            None
        };
        RoadEdgeState {
            reference,
            edge_index,
            road: RoadSegment::new(recording_period, recording_interval),
            in_bottleneck,
            out_bottleneck,
            available_length,
        }
    }

    /// Records the entry of a new vehicle on the edge and returns the travel time of this vehicle
    /// up to the Bottleneck.
    fn enters_road_segment(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) -> Time<T> {
        self.road.enters(vehicle, current_time);
        self.get_travel_time(vehicle)
    }

    /// A vehicle is entering the edge.
    fn vehicle_entry(&mut self, vehicle: &Vehicle<T>) {
        self.available_length
            .as_mut()
            .map(|l| *l -= vehicle.get_headway());
    }

    /// A vehicle is exiting the edge.
    ///
    /// Returns `true` if there is room for a pending vehicle.
    fn vehicle_exit(&mut self, vehicle: &Vehicle<T>) -> bool {
        self.available_length
            .as_mut()
            .map(|l| *l += vehicle.get_headway());
        if let (Some(bottleneck), Some(length)) = (self.in_bottleneck, self.available_length) {
            bottleneck.pending_vehicle_can_enter(length)
        } else {
            false
        }
    }

    /// Returns the current travel time of the vehicle on the running part of the edge.
    fn get_travel_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.reference
            .get_travel_time(self.road.occupied_length, vehicle)
    }

    fn into_simulated_functions(self) -> SimulatedFunctions<T> {
        SimulatedFunctions {
            in_bottleneck: self
                .in_bottleneck
                .map(|b| b.into_simulated_ttf())
                .unwrap_or_else(|| TTF::Constant(Time::zero())),
            out_bottleneck: self
                .out_bottleneck
                .map(|b| b.into_simulated_ttf())
                .unwrap_or_else(|| TTF::Constant(Time::zero())),
            road: self.road.into_simulated_length_function(),
        }
    }

    /// Returns `true` if there is enough room of the edge for the given additional length.
    fn has_room_for(&self, length: Length<T>) -> bool {
        self.available_length.map(|l| l >= length).unwrap_or(true)
    }

    /// Records the entry of a vehicle at the in-bottleneck of the edge.
    ///
    /// Returns a [BottleneckResult] that represents the state of the Bottleneck.
    fn enters_in_bottleneck(
        &mut self,
        event: VehicleEvent<'a, T>,
        vehicle: &'a Vehicle<T>,
    ) -> Option<Box<dyn Event<'a, T> + 'a>> {
        if let Some(bottleneck) = &mut self.in_bottleneck {
            let has_room = self.has_room_for(vehicle.get_headway());
            bottleneck.enters(event, vehicle, self.edge_index, has_room)
        } else {
            // There is no bottleneck, just act like if the bottleneck was open.
            Some(Box::new(event))
        }
    }

    /// Record the entry of a vehicle at the out-bottleneck of the edge.
    ///
    /// Return a [BottleneckResult] that represents the state of the Bottleneck.
    fn enters_out_bottleneck(
        &mut self,
        event: VehicleEvent<'a, T>,
        vehicle: &'a Vehicle<T>,
    ) -> Option<Box<dyn Event<'a, T> + 'a>> {
        // Remove the vehicle from the road part of the edge.
        self.road.exits(vehicle, event.get_time());
        if let Some(bottleneck) = &mut self.out_bottleneck {
            bottleneck.enters(event, vehicle, self.edge_index, true)
        } else {
            // There is no bottleneck, just act like if the bottleneck was open.
            Some(Box::new(event))
        }
    }
}

/// Struct that represents the state of a [RoadNetwork] at a given time.
#[derive(Clone, Debug)]
pub struct RoadNetworkState<'a, T> {
    graph: DiGraph<RoadNodeState<'a>, RoadEdgeState<'a, T>>,
    network: &'a RoadNetwork<T>,
}

impl<'a, T: TTFNum> RoadNetworkState<'a, T> {
    /// Create an empty [RoadNetworkState] from a [RoadNetwork].
    pub fn from_network(
        network: &'a RoadNetwork<T>,
        recording_period: Interval<T>,
        recording_interval: Time<T>,
    ) -> Self {
        let graph = network.get_graph().map(
            |node_id, n| RoadNodeState::new(n, node_id),
            |edge_id, e| RoadEdgeState::new(e, edge_id, recording_period, recording_interval),
        );
        RoadNetworkState { graph, network }
    }

    /// Return a [RoadNetworkWeights] (i.e., travel times) from the observations recorded in the
    /// [RoadNetworkState].
    pub fn into_weights(
        self,
        preprocess_data: &RoadNetworkPreprocessingData<T>,
    ) -> RoadNetworkWeights<T> {
        let mut weights = RoadNetworkWeights::with_capacity(
            preprocess_data.nb_unique_vehicles(),
            self.graph.edge_count(),
        );
        let (_, edge_states) = self.graph.into_nodes_edges();
        let edge_refs: Vec<_> = edge_states.iter().map(|e| e.weight.reference).collect();
        let edge_simulated_functions: Vec<SimulatedFunctions<T>> = edge_states
            .into_iter()
            .map(|e| e.weight.into_simulated_functions())
            .collect();
        for (uvehicle_id, vehicle) in preprocess_data
            .unique_vehicles
            .iter_uniques(&self.network.vehicles)
        {
            let vehicle_weights = &mut weights[uvehicle_id];
            for (funcs, edge_ref) in edge_simulated_functions.iter().zip(edge_refs.iter()) {
                let road_ttf = match &funcs.road {
                    XYF::Piecewise(road_pwl_length) => {
                        let road_pwl_ttf =
                            road_pwl_length.map(|l| edge_ref.get_travel_time(l, vehicle));
                        if road_pwl_ttf.is_cst() {
                            TTF::Constant(road_pwl_ttf.y_at_index(0))
                        } else {
                            TTF::Piecewise(road_pwl_ttf.to_ttf())
                        }
                    }
                    XYF::Constant(l) => TTF::Constant(edge_ref.get_travel_time(*l, vehicle)),
                };
                let mut ttf = funcs
                    .in_bottleneck
                    .link(&road_ttf)
                    .link(&funcs.out_bottleneck);
                ttf.ensure_fifo();
                vehicle_weights.push(ttf);
            }
        }
        weights
    }

    pub fn enters_in_bottleneck(
        &mut self,
        event: VehicleEvent<'a, T>,
        vehicle: &Vehicle<T>,
    ) -> Option<Box<dyn Event<'a, T> + 'a>> {
        let current_edge = &mut self.graph[event.current_edge()];
        current_edge.enters_in_bottleneck(event, vehicle)
    }

    /// Records the entry of a new vehicle on the road segment of an edge and returns the travel
    /// time of this vehicle up to the Bottleneck.
    pub fn enters_road(&mut self, event: VehicleEvent<'a, T>, vehicle: &Vehicle<T>) -> Time<T> {
        // Increase the available length of the vehicle's previous edge.
        if let Some(edge_index) = event.previous_edge() {
            let previous_edge = &mut self.graph[edge_index];
            if previous_edge.vehicle_exit(vehicle) {
                // A pending vehicle is now free to enter the edge.
                let event =
                    BottleneckEvent::new(event.get_time(), edge_index, BottleneckPosition::In);
            }
        }
        let current_edge = &mut self.graph[event.current_edge()];
        // Decrease the available length of the vehicle's current edge.
        current_edge.vehicle_entry(vehicle);
        current_edge.enters_road_segment(vehicle, event.get_time())
    }
}

/// Event representing the opening of a Bottleneck.
#[derive(Clone, Debug, PartialEq)]
pub struct BottleneckEvent<T> {
    /// Time at which the Bottleneck opens.
    at_time: Time<T>,
    /// Id of the edge where the Bottleneck is located.
    edge: EdgeIndex,
    /// In or out bottleneck.
    position: BottleneckPosition,
}

impl<T> BottleneckEvent<T> {
    /// Creates a new BottleneckEvent.
    pub const fn new(at_time: Time<T>, edge: EdgeIndex, position: BottleneckPosition) -> Self {
        BottleneckEvent {
            at_time,
            edge,
            position,
        }
    }
}

impl<'a, T: TTFNum> Event<'a, T> for BottleneckEvent<T> {
    fn execute<'b: 'a>(
        mut self: Box<Self>,
        _network: &'b Network<T>,
        _skims: &NetworkSkim<T>,
        state: &mut NetworkState<'a, T>,
        _preprocess_data: &PreprocessingData<T>,
        _result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<'a, T>,
    ) -> Result<()> {
        let road_network_state = state.get_mut_road_network().unwrap();
        let edge_state = &mut road_network_state.graph[self.edge];
        let bottleneck = match self.position {
            BottleneckPosition::In => edge_state.in_bottleneck.as_mut().unwrap(),
            BottleneckPosition::Out => edge_state.out_bottleneck.as_mut().unwrap(),
        };
        let vehicle_length = bottleneck
            .peek()
            .expect("Cannot execute BottleneckEvent with empty queue")
            .vehicle_length;
        let has_room = edge_state.has_room_for(vehicle_length);
        if has_room {
            // TODO: Update state.
            bottleneck.remove_pending_state();
        } else {
            // The next vehicle can cross the bottleneck but there is not enough room on the edge.
            // We set the status of the bottleneck to pending. An event will be executed as soon as
            // there is enough room on the edge.
            bottleneck.set_pending_state(vehicle_length);
            return Ok(());
        }
        let entry = bottleneck
            .pop()
            .expect("Cannot execute BottleneckEvent with empty queue");
        // Record the vehicle entry and exit.
        // (Vehicle entry time is the current timing of the vehicle event).
        bottleneck.record(entry.event.get_time(), self.at_time);
        // Trigger an event to make the vehicle exits.
        entry.event.set_time(self.at_time);
        events.push(Box::new(entry.event));
        if bottleneck.queue.is_empty() {
            // Record that the bottleneck is now open.
            bottleneck.record(self.at_time, self.at_time);
        } else {
            // Trigger an event to open the bottleneck later.
            self.at_time += entry.closing_time;
            events.push(self);
        }
        Ok(())
    }
    fn get_time(&self) -> Time<T> {
        self.at_time
    }
}

#[derive(Clone, Debug)]
struct PwlXYFBuilder<X, Y, T> {
    points: Vec<Y>,
    start_x: X,
    end_x: X,
    interval_x: X,
    current_index: usize,
    last_point: (X, Y),
    weighted_y: T,
    convert_type: PhantomData<T>,
}

impl<X, Y, T> PwlXYFBuilder<X, Y, T>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    fn new(period: [X; 2], interval_x: X) -> Self {
        let n = ((period[1] - period[0]) / interval_x)
            .trunc()
            .to_usize()
            .unwrap()
            + 1;
        PwlXYFBuilder {
            points: Vec::with_capacity(n),
            start_x: period[0],
            end_x: period[1],
            interval_x,
            current_index: 0,
            last_point: (period[0], Y::zero()),
            weighted_y: T::zero(),
            convert_type: PhantomData,
        }
    }

    fn push(&mut self, x: X, y: Y) {
        debug_assert!(x >= self.start_x);
        if x > self.end_x {
            // Skip.
            return;
        }
        let index = ((x - self.start_x) / self.interval_x)
            .round()
            .to_usize()
            .unwrap();
        debug_assert!(index >= self.current_index);
        if index > self.current_index {
            self.finish_interval(index);
        }
        let duration = x - self.last_point.0;
        debug_assert!(duration >= X::zero());
        self.weighted_y += duration.into() * self.last_point.1.into();
        self.last_point = (x, y);
    }

    fn finish_interval(&mut self, index: usize) {
        // Find interval length and end.
        let half_interval_length = X::average(self.interval_x, X::zero());
        let interval_end = self.start_x
            + self.interval_x * X::from(self.current_index).unwrap()
            + half_interval_length;
        // Add last point.
        let duration = interval_end - self.last_point.0;
        debug_assert!(duration >= X::zero());
        self.weighted_y += duration.into() * self.last_point.1.into();
        self.last_point = (interval_end, self.last_point.1);
        // Compute and add `y` value for current interval.
        let interval_length =
            if self.current_index == 0 || self.current_index == self.nb_intervals() - 1 {
                half_interval_length
            } else {
                self.interval_x
            };
        let y = self.weighted_y / interval_length.into();
        self.points.push(y.into());
        // Switch to next interval.
        self.weighted_y = T::zero();
        self.current_index += 1;
        // Go recursive (multiple intervals can end at the same time).
        if index > self.current_index {
            self.finish_interval(index)
        }
    }

    fn nb_intervals(&self) -> usize {
        ((self.end_x - self.start_x) / self.interval_x)
            .trunc()
            .to_usize()
            .unwrap()
            + 1
    }

    fn finish(mut self) -> XYF<X, Y, T> {
        self.finish_interval(self.nb_intervals());
        if self.points.iter().all(|&y| y == self.points[0]) {
            // All `y` values are identical.
            XYF::Constant(self.points[0])
        } else {
            XYF::Piecewise(PwlXYF::from_values(
                self.points,
                self.start_x,
                self.interval_x,
            ))
        }
    }
}
