// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of [RoadNetworkState].
use std::collections::VecDeque;
use std::ops::{Index, IndexMut};

use num_traits::{Float, Zero};
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use ttf::{PwlTTFBuilder, PwlXYFBuilder, TTFNum, TTF, XYF};

use super::super::{Network, NetworkSkim, NetworkState};
use super::vehicle::Vehicle;
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetwork, RoadNetworkParameters, RoadNode};
use crate::event::{Event, EventQueue};
use crate::mode::road::VehicleEvent;
use crate::simulation::results::AgentResult;
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
    /// Total weighted length so far in the current recording interval.
    weighted_length: Length<T>,
    /// Last time at which an event occured.
    last_timing: Time<T>,
    /// History of the length of vehicles on the segment.
    length_history: PwlXYFBuilder<Time<T>, Length<T>, NoUnit<T>>,
}

impl<T: TTFNum> RoadSegment<T> {
    fn new(period: Interval<T>) -> Self {
        let mut length_history = PwlXYFBuilder::new(period.0);
        length_history.push(period.start(), Length::zero());
        RoadSegment {
            occupied_length: Length::zero(),
            weighted_length: Length::zero(),
            last_timing: period.start(),
            length_history,
        }
    }

    /// Record the entry of a new vehicle on the segment.
    fn enters(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) {
        let new_length = self.occupied_length + vehicle.get_length();
        self.set_length(new_length, current_time);
    }

    /// Record the exit of a vehicle from the segment.
    fn exits(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) {
        let new_length = self.occupied_length - vehicle.get_length();
        self.set_length(new_length, current_time);
    }

    /// Change the occupied length to the new value.
    ///
    /// Also update the weighted length for the period that elapsed since the last event.
    fn set_length(&mut self, length: Length<T>, timing: Time<T>) {
        debug_assert!(timing >= self.last_timing);
        self.weighted_length += Length(self.occupied_length.0 * (timing - self.last_timing).0);
        self.occupied_length = length;
        self.last_timing = timing;
    }

    /// Record the average observed length during the interval that just elapsed.
    fn interval_is_completed(&mut self, interval: Interval<T>) {
        debug_assert!(interval.end() >= self.last_timing);
        self.weighted_length +=
            Length(self.occupied_length.0 * (interval.end() - self.last_timing).0);
        self.length_history.push(
            Time::average(interval.start(), interval.end()),
            Length(self.weighted_length.0 / interval.length().0),
        );
        self.weighted_length = Length::zero();
        self.last_timing = interval.end();
    }

    /// Consumes the [RoadSegment] and returns a [PwlXYF] with the simulated Length.
    fn into_simulated_length_function(self) -> XYF<Time<T>, Length<T>, NoUnit<T>> {
        let pwl_xyf = self.length_history.finish();
        if pwl_xyf.iter_y().all(|y| y == &pwl_xyf[0].y) {
            XYF::Constant(pwl_xyf[0].y)
        } else {
            XYF::Piecewise(pwl_xyf)
        }
    }
}

/// Entry for a [BottleneckQueue].
///
/// It contains three values:
///
/// - The [VehicleEvent] associated with the vehicle waiting.
///
/// - The [Vehicle] type of the vehicle waiting.
///
/// - The time at which the vehicle started waiting.
type BottleneckEntry<'a, T> = (Box<VehicleEvent<T>>, &'a Vehicle<T>);

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
pub enum BottleneckStatus<T> {
    /// The bottleneck is open.
    ///
    /// The vehicle associated to the given [VehicleEvent] can cross immediately.
    Open(Box<VehicleEvent<T>>),
    /// The bottleneck is closed.
    ///
    /// If a [BottleneckEvent] is not created yet, it is returned here.
    Closed(Option<BottleneckEvent<T>>),
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
    /// Indicates if the bottleneck is open, i.e., vehicles can freely cross it.
    is_open: bool,
    /// Indicates the time at which the bottleneck is expected to open again.
    next_opening: Time<T>,
    /// Indicates if there is an event in the queue to trigger the bottleneck opening.
    has_event: bool,
    /// Queue of vehicles currently waiting at the bottleneck.
    queue: BottleneckQueue<'a, T>,
    /// Total weighted waiting time so far in the current recording interval.
    weighted_waiting_time: Time<T>,
    /// Last time at which an event occured.
    last_timing: Time<T>,
    /// History of the entry / exit of vehicles.
    waiting_time_history: PwlTTFBuilder<Time<T>>,
}

impl<'a, T> Bottleneck<'a, T> {
    /// Set the Bottleneck to open.
    fn open(&mut self) {
        self.is_open = true;
        self.has_event = false;
    }

    /// Return the next [BottleneckEntry] in the [BottleneckQueue] of the Bottleneck.
    fn pop(&mut self) -> Option<BottleneckEntry<'a, T>> {
        self.queue.pop_front()
    }
}

impl<T: TTFNum> Bottleneck<'_, T> {
    fn new(effective_flow: Flow<T>, position: BottleneckPosition, period: Interval<T>) -> Self {
        let mut waiting_time_history = PwlTTFBuilder::new(period.0);
        waiting_time_history.push(period.start(), Time::zero());
        Bottleneck {
            effective_flow,
            position,
            is_open: true,
            next_opening: period.start(),
            has_event: false,
            queue: Default::default(),
            weighted_waiting_time: Time::zero(),
            last_timing: period.start(),
            waiting_time_history,
        }
    }

    /// Return the time at which the bottleneck will open again, given the currently planned next
    /// opening and the vehicle which just entered.
    fn get_next_opening(&self, vehicle: &Vehicle<T>, opening_time: Time<T>) -> Time<T> {
        opening_time + vehicle.get_pce() / self.effective_flow
    }

    /// Close the bottleneck and set the time of the next opening.
    fn set_next_opening(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) {
        self.is_open = false;
        self.next_opening = self.get_next_opening(vehicle, current_time);
    }

    fn update_weighted_waiting_time(&mut self, current_time: Time<T>) {
        // Duration that elapsed since the last recording.
        let duration = current_time - self.last_timing;
        // From `last_timing` to `current_time`, the exit time is `next_opening`.
        // The average waiting time during this period was thus `next_opening` - (`last_timing` +
        // `current_time`) / 2. We multiply by the duration of the period.
        self.weighted_waiting_time +=
            duration * (self.next_opening - TTFNum::average(self.last_timing, current_time));
    }

    /// Record the average observed waiting time during the interval that just elapsed.
    fn interval_is_completed(&mut self, interval: Interval<T>) {
        debug_assert!(interval.end() >= self.last_timing);
        if self.is_open {
            // No waiting time
        } else if self.next_opening <= interval.end() {
            // The bottleneck was closed but it is now open.
            self.update_weighted_waiting_time(self.next_opening);
            self.open();
        } else {
            self.update_weighted_waiting_time(interval.end());
        };
        self.waiting_time_history.push(
            Time::average(interval.start(), interval.end()),
            self.weighted_waiting_time / interval.length(),
        );
        self.weighted_waiting_time = Time::zero();
        self.last_timing = interval.end();
    }

    /// Consumes the [Bottleneck] and returns a [PwlTTF] with the simulated waiting time.
    fn into_simulated_ttf(self) -> TTF<Time<T>> {
        let pwl_ttf = self.waiting_time_history.finish();
        if pwl_ttf.iter_y().all(|y| y == &pwl_ttf[0].y) {
            TTF::Constant(pwl_ttf[0].y)
        } else {
            TTF::Piecewise(pwl_ttf)
        }
    }
}

impl<'a, T: TTFNum + 'static> Bottleneck<'a, T> {
    /// Record the entry of a vehicle in the bottleneck.
    ///
    /// Return the status of the bottleneck as a [BottleneckStatus].
    /// This is the status of the bottleneck just before the entry (i.e., if the bottleneck is open
    /// when the vehicle enters, the status of the bottleneck is `open`).
    fn enters(
        &mut self,
        event: Box<VehicleEvent<T>>,
        vehicle: &'a Vehicle<T>,
        edge_index: EdgeIndex,
    ) -> BottleneckStatus<T> {
        let current_time = event.get_time();
        debug_assert!(current_time >= self.last_timing);
        let status = if self.is_open {
            // The bottleneck is open, the vehicle can cross immediately.
            self.set_next_opening(vehicle, current_time);
            BottleneckStatus::Open(event)
        } else if self.has_event {
            debug_assert!(self.next_opening >= current_time, "The bottleneck is open?");
            // The bottleneck is closed and there is a BottleneckEvent in the event queue that will
            // trigger the next time it opens.
            self.update_weighted_waiting_time(current_time);
            self.set_next_opening(vehicle, self.next_opening);
            self.queue.push_back((event, vehicle));
            BottleneckStatus::Closed(None)
        } else if self.next_opening.approx_le(&current_time) {
            // The bottleneck was closed but it is now open.
            self.update_weighted_waiting_time(self.next_opening);
            self.set_next_opening(vehicle, current_time);
            BottleneckStatus::Open(event)
        } else {
            // The bottleneck is closed and there is no BottleneckEvent in the event queue yet.
            self.update_weighted_waiting_time(current_time);
            // Create a BottleneckEvent with a queue to trigger the exit from the bottleneck at
            // the correct time.
            let event_time = self.next_opening;
            self.set_next_opening(vehicle, self.next_opening);
            self.queue.push_back((event, vehicle));
            self.has_event = true;
            BottleneckStatus::Closed(Some(BottleneckEvent::new(
                event_time,
                edge_index,
                self.position,
            )))
        };
        self.last_timing = current_time;
        status
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
    /// Total length of vehicles which entered the road edge since the beginning of the period.
    total_length: Length<T>,
    /// Timing intervals between which the average road travel time needs to be computed.
    recording_intervals: &'a [Time<T>],
    /// Next time threshold when a new interval will begin and index of the next time interval.
    next_threshold: Option<(Time<T>, usize)>,
}

impl<'a, T: TTFNum> RoadEdgeState<'a, T> {
    /// Creates a new RoadEdgeState.
    pub fn new(
        reference: &'a RoadEdge<T>,
        edge_index: EdgeIndex,
        recording_intervals: &'a [Time<T>],
    ) -> Self {
        debug_assert!(recording_intervals.len() >= 2);
        let recording_period = Interval([
            *recording_intervals.first().unwrap(),
            *recording_intervals.last().unwrap(),
        ]);
        let effective_inflow = reference.get_effective_inflow();
        let in_bottleneck = if effective_inflow.is_infinite() {
            None
        } else {
            Some(Bottleneck::new(
                effective_inflow,
                BottleneckPosition::In,
                recording_period,
            ))
        };
        let effective_outflow = reference.get_effective_outflow();
        let out_bottleneck = if effective_outflow.is_infinite() {
            None
        } else {
            Some(Bottleneck::new(
                effective_outflow,
                BottleneckPosition::Out,
                recording_period,
            ))
        };
        RoadEdgeState {
            reference,
            edge_index,
            road: RoadSegment::new(recording_period),
            in_bottleneck,
            out_bottleneck,
            total_length: Default::default(),
            next_threshold: Some((recording_intervals[1], 1)),
            recording_intervals,
        }
    }

    fn check_recording_interval(&mut self, current_time: Time<T>) {
        if let Some((threshold, i)) = self.next_threshold {
            if current_time >= threshold {
                // A new recording interval started.
                let interval = Interval([self.recording_intervals[i - 1], threshold]);
                self.road.interval_is_completed(interval);
                if let Some(bottleneck) = &mut self.in_bottleneck {
                    bottleneck.interval_is_completed(interval);
                }
                if let Some(bottleneck) = &mut self.out_bottleneck {
                    bottleneck.interval_is_completed(interval);
                }
                // Update the next threshold.
                self.next_threshold = if self.recording_intervals.len() == i + 1 {
                    // The last recording interval has been reached.
                    None
                } else {
                    Some((self.recording_intervals[i + 1], i + 1))
                };
                // Go recursive in case more than one interval ended.
                self.check_recording_interval(current_time);
            }
        }
    }

    /// Record the entry of a new vehicle on the edge and return the travel time of this vehicle up
    /// to the Bottleneck.
    pub fn enters_road(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) -> Time<T> {
        self.check_recording_interval(current_time);
        self.total_length += vehicle.get_length();
        self.road.enters(vehicle, current_time);
        self.get_travel_time(vehicle)
    }

    /// Return the current travel time of the vehicle on the running part of the edge.
    fn get_travel_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.reference
            .get_travel_time(self.road.occupied_length, vehicle)
    }

    fn into_simulated_functions(mut self) -> SimulatedFunctions<T> {
        self.check_recording_interval(*self.recording_intervals.last().unwrap());
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
}

impl<'a, T: TTFNum + 'static> RoadEdgeState<'a, T> {
    /// Record the entry of a vehicle at the in-bottleneck of the edge.
    ///
    /// Return a [BottleneckStatus] that represents the state of the Bottleneck.
    pub fn enters_in_bottleneck(
        &mut self,
        vehicle: &'a Vehicle<T>,
        event: Box<VehicleEvent<T>>,
    ) -> BottleneckStatus<T> {
        self.check_recording_interval(event.get_time());
        if let Some(bottleneck) = &mut self.in_bottleneck {
            bottleneck.enters(event, vehicle, self.edge_index)
        } else {
            // There is no bottleneck, just act like if the bottleneck was open.
            BottleneckStatus::Open(event)
        }
    }

    /// Record the entry of a vehicle at the out-bottleneck of the edge.
    ///
    /// Return a [BottleneckStatus] that represents the state of the Bottleneck.
    pub fn enters_out_bottleneck(
        &mut self,
        vehicle: &'a Vehicle<T>,
        event: Box<VehicleEvent<T>>,
    ) -> BottleneckStatus<T> {
        self.check_recording_interval(event.get_time());
        // Remove the vehicle from the road part of the edge.
        self.road.exits(vehicle, event.get_time());
        if let Some(bottleneck) = &mut self.out_bottleneck {
            bottleneck.enters(event, vehicle, self.edge_index)
        } else {
            // There is no bottleneck, just act like if the bottleneck was open.
            BottleneckStatus::Open(event)
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
    pub fn from_network(network: &'a RoadNetwork<T>, recording_intervals: &'a [Time<T>]) -> Self {
        let graph = network.get_graph().map(
            |node_id, n| RoadNodeState::new(n, node_id),
            |edge_id, e| RoadEdgeState::new(e, edge_id, recording_intervals),
        );
        RoadNetworkState { graph, network }
    }

    /// Return a [RoadNetworkWeights] (i.e., travel times) from the observations recorded in the
    /// [RoadNetworkState].
    pub fn into_weights(self, parameters: &RoadNetworkParameters<T>) -> RoadNetworkWeights<T> {
        let mut weights =
            RoadNetworkWeights::with_capacity(self.network.vehicles.len(), self.graph.edge_count());
        let (_, edge_states) = self.graph.into_nodes_edges();
        let edge_refs: Vec<_> = edge_states.iter().map(|e| e.weight.reference).collect();
        let edge_simulated_functions: Vec<SimulatedFunctions<T>> = edge_states
            .into_iter()
            .map(|e| e.weight.into_simulated_functions())
            .collect();
        for (vehicle_id, vehicle) in self.network.iter_vehicles() {
            let vehicle_weights = &mut weights[vehicle_id];
            for (funcs, edge_ref) in edge_simulated_functions.iter().zip(edge_refs.iter()) {
                let road_ttf = funcs
                    .road
                    .map(|l| edge_ref.get_travel_time(l, vehicle))
                    .to_ttf();
                let mut ttf = funcs
                    .in_bottleneck
                    .link(&road_ttf)
                    .link(&funcs.out_bottleneck);
                parameters.simulated_simplification.simplify(&mut ttf);
                vehicle_weights.push(ttf);
            }
        }
        weights
    }
}

impl<'a, T> Index<NodeIndex> for RoadNetworkState<'a, T> {
    type Output = RoadNodeState<'a>;

    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.graph[index]
    }
}

impl<T> IndexMut<NodeIndex> for RoadNetworkState<'_, T> {
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.graph[index]
    }
}

impl<'a, T> Index<EdgeIndex> for RoadNetworkState<'a, T> {
    type Output = RoadEdgeState<'a, T>;

    fn index(&self, index: EdgeIndex) -> &Self::Output {
        &self.graph[index]
    }
}

impl<T> IndexMut<EdgeIndex> for RoadNetworkState<'_, T> {
    fn index_mut(&mut self, index: EdgeIndex) -> &mut Self::Output {
        &mut self.graph[index]
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

impl<T: TTFNum + 'static> Event<T> for BottleneckEvent<T> {
    fn execute<'a: 'b, 'b>(
        mut self: Box<Self>,
        _network: &'a Network<T>,
        _exp_skims: &NetworkSkim<T>,
        state: &mut NetworkState<'b, T>,
        _result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<T>,
    ) {
        let road_network_state = state.get_mut_road_network().unwrap();
        let edge_state = &mut road_network_state[self.edge];
        edge_state.check_recording_interval(self.at_time);
        let bottleneck = match self.position {
            BottleneckPosition::In => edge_state.in_bottleneck.as_mut().unwrap(),
            BottleneckPosition::Out => edge_state.out_bottleneck.as_mut().unwrap(),
        };
        if let Some((mut vehicle_event, vehicle)) = bottleneck.pop() {
            // Trigger an event to make the vehicle exits.
            vehicle_event.set_time(self.at_time);
            events.push(vehicle_event);
            // Trigger an event to open the bottleneck later.
            self.at_time += vehicle.get_pce() / bottleneck.effective_flow;
            events.push(self);
        } else {
            // The bottleneck is now open.
            bottleneck.update_weighted_waiting_time(self.at_time);
            bottleneck.open();
        }
    }
    fn get_time(&self) -> Time<T> {
        self.at_time
    }
}
