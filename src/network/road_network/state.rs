// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of [RoadNetworkState].
use std::collections::VecDeque;

use anyhow::Result;
use either::Either;
use enum_as_inner::EnumAsInner;
use hashbrown::HashMap;
use log::warn;
use num_traits::{Float, FromPrimitive, ToPrimitive, Zero};
use petgraph::graph::{DiGraph, EdgeIndex};
use ttf::{PwlXYF, TTFNum, TTF, XYF};

use super::vehicle::Vehicle;
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetwork, RoadNetworkParameters, RoadNetworkPreprocessingData};
use crate::agent::AgentIndex;
use crate::event::{Event, EventAlloc, EventInput, EventQueue};
use crate::mode::trip::event::VehicleEvent;
use crate::units::{Flow, Interval, Length, NoUnit, Time, PCE};

const MAX_WARNINGS: usize = 20;

/// Struct that holds data on the current state of a [RoadNode].
#[derive(Clone, Debug)]
struct RoadNodeState {}

/// Struct representing the current state of the running part of a [RoadEdge].
#[derive(Clone, Debug)]
struct RoadSegment<T> {
    /// Total length of the vehicles currently on the segment.
    occupied_length: Length<T>,
    /// History of the length of vehicles on the segment.
    length_history: LengthXYFBuilder<T>,
}

impl<T: TTFNum> RoadSegment<T> {
    fn new(period: Interval<T>, interval: Time<T>) -> Self {
        let length_history = LengthXYFBuilder::new(period, interval);
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

#[derive(Clone, Copy, Debug, PartialEq, EnumAsInner)]
enum EdgeEntryStatus {
    /// The bottleneck is open.
    Open,
    /// The bottleneck is closed.
    Closed,
    /// The edge is full.
    Full,
}

#[derive(Clone, Copy, Debug, PartialEq, EnumAsInner)]
enum EdgeExitStatus {
    /// The bottleneck is open.
    Open,
    /// The bottleneck is closed.
    Closed,
}

/// Enum representing the position of a bottleneck.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum BottleneckPosition {
    /// The bottleneck is at the edge entry.
    Entry,
    /// The bottleneck is at the edge exit.
    Exit,
}

#[derive(Clone, Debug)]
struct SimulatedFunctions<T> {
    entry: TTF<Time<T>>,
    exit: TTF<Time<T>>,
    road: XYF<Time<T>, Length<T>, NoUnit<T>>,
}

/// Next event to execute for a queued vehicle, time at which the vehicle entered the queue and
/// edge it is coming from (if any).
#[derive(Clone, Debug)]
struct QueuedVehicle<T> {
    event: VehicleEvent<T>,
    vehicle_pce: PCE<T>,
    entry_time: Time<T>,
}

/// Queue of vehicles.
type VehicleQueue<T> = VecDeque<QueuedVehicle<T>>;

/// State of the congestion at the entry of the edge, that can result from the entry bottleneck or
/// from the edge being full.
#[derive(Clone, Debug)]
struct EdgeEntryState<T> {
    /// Current length available for vehicles on the edge, i.e., total length of the edge minus the
    /// total headway length of vehicles currently on the edge.
    /// Or `None` if spillback is disabled.
    available_length: Option<Length<T>>,
    /// Effective flow of the edge.
    /// Or `None` if the flow is infinite.
    effective_flow: Option<Flow<T>>,
    /// Indicates the status of the edge entry (open, closed or pending).
    status: EdgeEntryStatus,
    /// Queue of vehicles currently waiting to enter the edge.
    queue: VehicleQueue<T>,
    /// Waiting time PwlTTF function.
    waiting_time_history: WaitXYFBuilder<T>,
}

impl<T: TTFNum> EdgeEntryState<T> {
    /// Initializes a new [EdgeEntryState] for a given edge.
    fn new(
        edge: &RoadEdge<T>,
        period: Interval<T>,
        interval: Time<T>,
        spillback_enabled: bool,
    ) -> Option<Self> {
        let (effective_flow, available_length) =
            match (edge.get_effective_flow(), spillback_enabled) {
                (flow, true) if flow.is_finite() => (Some(flow), Some(edge.total_length())),
                (flow, false) if flow.is_finite() => (Some(flow), None),
                (_, true) => (None, Some(edge.total_length())),
                (_, false) => {
                    return None;
                }
            };
        Some(Self {
            available_length,
            effective_flow,
            status: EdgeEntryStatus::Open,
            queue: VehicleQueue::new(),
            waiting_time_history: WaitXYFBuilder::new(period, interval),
        })
    }

    /// Returns `true` if the edge entry is open, i.e., the bottleneck is not closed and the edge
    /// is not full.
    fn is_open(&self) -> bool {
        self.status == EdgeEntryStatus::Open
    }

    /// Returns `true` if the edge is full, i.e., there is more vehicle occupying the length than
    /// the edge can handle.
    fn is_full(&self) -> bool {
        self.available_length
            .map(|l| l.is_sign_negative())
            .unwrap_or(false)
    }

    /// Reduces the available length of the edge by the given amount.
    fn reduce_available_length(&mut self, length: Length<T>) {
        if let Some(available_length) = self.available_length.as_mut() {
            *available_length -= length;
        }
    }

    /// Increases the available length of the edge by the given amount.
    fn increase_available_length(&mut self, length: Length<T>) {
        if let Some(available_length) = self.available_length.as_mut() {
            *available_length += length;
        }
    }

    /// Returns the closing time of the bottleneck when the given vehicle crosses it.
    ///
    /// Returns zero if there is no bottleneck.
    fn get_closing_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.effective_flow
            .map(|f| vehicle.get_pce() / f)
            .unwrap_or(Time::zero())
    }

    /// A vehicle is reaching the edge entry.
    ///
    /// Three possible cases:
    ///
    /// - If the edge is open and not full: closes the edge entry and returns `Some(Left)` with the
    ///   next event to execute for the vehicle.
    /// - If there is closed: the vehicle is pushed to the queue of pending vehicles, returns
    ///   `None`.
    /// - If the edge is open but full: the vehicle is pushed to the queue of pending vehicles,
    ///   returns `Some(Right)` with the index of the current edge of the pending vehicle (or
    ///   `None` if the pending vehicle is not currently on an edge).
    fn vehicle_reaches_entry(
        &mut self,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
        next_event: VehicleEvent<T>,
    ) -> Option<Either<VehicleEvent<T>, AgentIndex>> {
        match (self.is_open(), self.is_full()) {
            (true, false) => {
                // Free to go.
                debug_assert!(self.queue.is_empty());
                // Close the edge entry. It will re-open again when the vehicle will have
                // successfully entered the edge.
                self.status = EdgeEntryStatus::Closed;
                Some(Either::Left(next_event))
            }
            (true, true) => {
                // Edge entry is open but edge is full.
                debug_assert!(self.queue.is_empty());
                let agent_id = next_event.agent_id();
                self.status = EdgeEntryStatus::Full;
                self.queue.push_back(QueuedVehicle {
                    event: next_event,
                    vehicle_pce: vehicle.get_pce(),
                    entry_time: current_time,
                });
                Some(Either::Right(agent_id))
            }
            (false, _) => {
                // Edge is closed.
                self.queue.push_back(QueuedVehicle {
                    event: next_event,
                    vehicle_pce: vehicle.get_pce(),
                    entry_time: current_time,
                });
                None
            }
        }
    }

    /// A vehicle has successfully entered the edge.
    ///
    /// Returns the closing time of the bottleneck.
    fn vehicle_enters(&mut self, vehicle: &Vehicle<T>) -> Time<T> {
        debug_assert_ne!(self.status, EdgeEntryStatus::Open);
        self.reduce_available_length(vehicle.get_headway());
        self.status = EdgeEntryStatus::Closed;
        self.get_closing_time(vehicle)
    }

    /// The edge entry re-opens.
    ///
    /// Three possible cases:
    ///
    /// - If there is not vehicle in the queue: the edge entry is open, returns `None`.
    /// - If there is a vehicle in the queue and the edge is not full: the edge entry stays closed,
    ///   returns `Some(Left)` with the next event to execute for the released vehicle.
    /// - If there is a vehicle in the queue but the edge is full: the edge entry is switch to
    ///   `Full`, returns `Some(Right)` with the index of the agent of the pending vehicle.
    fn try_open_entry(
        &mut self,
        current_time: Time<T>,
    ) -> Option<Either<VehicleEvent<T>, AgentIndex>> {
        if let Some(queued_vehicle) = self.queue.pop_front() {
            if self.is_full() {
                // The edge is full, put the vehicle back in the queue (at the front).
                let agent_id = queued_vehicle.event.agent_id();
                self.status = EdgeEntryStatus::Full;
                self.queue.push_front(queued_vehicle);
                Some(Either::Right(agent_id))
            } else {
                // A new vehicle is released, the bottleneck stays closed.
                self.status = EdgeEntryStatus::Closed;
                self.record(queued_vehicle.entry_time, current_time);
                let mut event = queued_vehicle.event;
                event.set_time(current_time);
                Some(Either::Left(event))
            }
        } else {
            // The bottleneck is open and there is no vehicle in the queue: the edge can be opened.
            self.status = EdgeEntryStatus::Open;
            None
        }
    }

    /// Forces the release of the next pending vehicle.
    fn force_release(&mut self, current_time: Time<T>) -> VehicleEvent<T> {
        let queued_vehicle = self.queue.pop_front().expect("No vehicle to release");
        self.status = EdgeEntryStatus::Closed;
        self.record(queued_vehicle.entry_time, current_time);
        let mut event = queued_vehicle.event;
        event.set_time(current_time);
        event
    }

    /// A vehicle has successfully exited the edge.
    ///
    /// Increases the length available on the edge according to the vehicle which just exited.
    ///
    /// Returns `Some` with the [VehicleEvent] of the pending vehicle being released (if any).
    /// Returns `None` if there is no pending vehicle, the bottleneck is closed or the edge is
    /// still full.
    fn vehicle_exits(
        &mut self,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
    ) -> Option<VehicleEvent<T>> {
        self.increase_available_length(vehicle.get_headway());
        if self.status == EdgeEntryStatus::Full && !self.is_full() {
            // The edge was full but it is not anymore.
            // Release the pending vehicle.
            self.status = EdgeEntryStatus::Closed;
            let queued_vehicle = self.queue.pop_front().unwrap();
            self.record(queued_vehicle.entry_time, current_time);
            let mut event = queued_vehicle.event;
            event.set_time(current_time);
            Some(event)
        } else {
            // The bottleneck is either open with no vehicle pending, closed or still full.
            None
        }
    }

    /// Records the entry and exit of a vehicle from the edge's entry at a given time.
    fn record(&mut self, entry_time: Time<T>, exit_time: Time<T>) {
        self.waiting_time_history.push(entry_time, exit_time);
    }

    /// Consumes the [EdgeEntryState] and returns a [TTF] with the simulated waiting time.
    fn into_simulated_ttf(self) -> TTF<Time<T>> {
        let mut ttf = self.waiting_time_history.finish();
        ttf.ensure_fifo();
        ttf
    }
}

/// State of the congestion at the exit of the edge.
#[derive(Clone, Debug)]
struct EdgeExitState<T> {
    /// Effective flow of the edge.
    /// Or `None` if the flow is infinite.
    effective_flow: Option<Flow<T>>,
    /// Indicates the status of the edge exit (open or closed).
    status: EdgeExitStatus,
    /// Queue of vehicles currently waiting to exit the edge.
    queue: VehicleQueue<T>,
    /// Waiting time PwlTTF function.
    waiting_time_history: WaitXYFBuilder<T>,
    /// Is overtaking allowed at the edge exit?
    overtaking_allowed: bool,
}

impl<T: TTFNum> EdgeExitState<T> {
    /// Initializes a new [EdgeExitState] for a given edge.
    fn new(edge: &RoadEdge<T>, period: Interval<T>, interval: Time<T>) -> Self {
        let effective_flow = if edge.get_effective_flow().is_finite() {
            Some(edge.get_effective_flow())
        } else {
            None
        };
        Self {
            effective_flow,
            status: EdgeExitStatus::Open,
            queue: VehicleQueue::new(),
            waiting_time_history: WaitXYFBuilder::new(period, interval),
            overtaking_allowed: edge.overtaking_is_allowed(),
        }
    }

    /// Returns `true` if the edge exit is open.
    fn is_open(&self) -> bool {
        self.status == EdgeExitStatus::Open
    }

    /// Returns the closing time of the bottleneck given the PCE of the vehicle which crosses it.
    fn get_closing_time(&self, vehicle_pce: PCE<T>) -> Time<T> {
        self.effective_flow
            .map(|f| vehicle_pce / f)
            .unwrap_or(Time::zero())
    }

    /// A vehicle is reaching the end of the edge.
    ///
    /// If the exit is open, returns the next event of the vehicle.
    /// If the exit is closed, pushes the vehicle to the end of the queue and returns `None`.
    ///
    /// If the exit is open and overtaking is allowed, also returns the closing time of the
    /// bottleneck.
    fn vehicle_reaches_exit(
        &mut self,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
        next_event: VehicleEvent<T>,
    ) -> Option<(VehicleEvent<T>, Option<Time<T>>)> {
        if self.is_open() {
            debug_assert!(self.queue.is_empty());
            // Close the edge exit.
            self.status = EdgeExitStatus::Closed;
            let closing_time = if self.overtaking_allowed {
                if self.get_closing_time(vehicle.get_pce()).is_zero() {
                    // The bottleneck does not close.
                    self.status = EdgeExitStatus::Open;
                    None
                } else {
                    // Return the closing time of the bottleneck so that an event is created to
                    // re-open it.
                    Some(self.get_closing_time(vehicle.get_pce()))
                }
            } else {
                // The edge exit will re-open again when the vehicle will have successfully exited
                // the edge (it can get trapped at the entry of the downstream edge).
                None
            };
            Some((next_event, closing_time))
        } else {
            // Bottleneck is closed.
            self.queue.push_back(QueuedVehicle {
                event: next_event,
                vehicle_pce: vehicle.get_pce(),
                entry_time: current_time,
            });
            None
        }
    }

    /// A vehicle has successfully exited the edge.
    ///
    /// Returns the closing time of the bottleneck.
    fn vehicle_exits(&mut self, vehicle: &Vehicle<T>) -> Option<Time<T>> {
        if self.overtaking_allowed {
            // The bottleneck was already closed for this vehicle when it crossed the bottleneck.
            None
        } else {
            debug_assert_eq!(self.status, EdgeExitStatus::Closed);
            self.status = EdgeExitStatus::Closed;
            Some(self.get_closing_time(vehicle.get_pce()))
        }
    }

    /// The bottleneck re-opens.
    ///
    /// Returns the event to execute for the next vehicle in the queue (if any).
    ///
    /// Returns the closing time of the bottleneck, if it gets closed.
    fn open_bottleneck(
        &mut self,
        current_time: Time<T>,
    ) -> Option<(VehicleEvent<T>, Option<Time<T>>)> {
        debug_assert_eq!(self.status, EdgeExitStatus::Closed);
        if let Some(queued_vehicle) = self.queue.pop_front() {
            // A new vehicle is released.
            self.record(queued_vehicle.entry_time, current_time);
            let closing_time_opt = if self.overtaking_allowed {
                // Return the closing time of the bottleneck so that an event is created to
                // re-open it.
                Some(self.get_closing_time(queued_vehicle.vehicle_pce))
            } else {
                // The bottleneck stays close until the vehicle has successfully entered its next
                // edge.
                None
            };
            let mut event = queued_vehicle.event;
            event.set_time(current_time);
            Some((event, closing_time_opt))
        } else {
            // The bottleneck is now open.
            self.status = EdgeExitStatus::Open;
            None
        }
    }

    /// Records the entry and exit of a vehicle from the edge's exit at a given time.
    fn record(&mut self, entry_time: Time<T>, exit_time: Time<T>) {
        self.waiting_time_history.push(entry_time, exit_time);
    }

    /// Consumes the [EdgeExitState] and returns a [TTF] with the simulated waiting time.
    fn into_simulated_ttf(self) -> TTF<Time<T>> {
        let mut ttf = self.waiting_time_history.finish();
        ttf.ensure_fifo();
        ttf
    }
}

/// Struct that holds data on the current state of a [RoadEdge].
#[derive(Clone, Debug)]
struct RoadEdgeState<T> {
    // TODO: Can we allow multiple RoadSegment on the same edge (e.g., a segment every 200m)?
    /// [RoadSegment] representing the road part of the edge.
    road: RoadSegment<T>,
    /// [EdgeEntryState] representing the state of the edge entry.
    /// Or `None` if the edge has infinite flow and spillback is disabled.
    entry: Option<EdgeEntryState<T>>,
    // TODO: Make EdgeExitState optional when overtaking is allowed (and flow is infinite).
    /// [EdgeExitState] representing the state of the edge exit.
    /// Or `None` if the edge has infinite flow and spillback is disabled.
    exit: Option<EdgeExitState<T>>,
}

impl<T: TTFNum> RoadEdgeState<T> {
    /// Creates a new RoadEdgeState.
    fn new(
        reference: &RoadEdge<T>,
        recording_period: Interval<T>,
        recording_interval: Time<T>,
        spillback_enabled: bool,
    ) -> Self {
        let entry = EdgeEntryState::new(
            reference,
            recording_period,
            recording_interval,
            spillback_enabled,
        );
        let exit = EdgeExitState::new(reference, recording_period, recording_interval);
        RoadEdgeState {
            road: RoadSegment::new(recording_period, recording_interval),
            entry,
            exit: Some(exit),
        }
    }

    /// A vehicle is reaching the edge entry.
    fn vehicle_reaches_entry(
        &mut self,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
        next_event: VehicleEvent<T>,
    ) -> Option<Either<VehicleEvent<T>, AgentIndex>> {
        if let Some(entry) = self.entry.as_mut() {
            entry.vehicle_reaches_entry(current_time, vehicle, next_event)
        } else {
            // Infinite flow + spillback is disabled: the vehicles can freely cross.
            Some(Either::Left(next_event))
        }
    }

    /// A vehicle is reaching the edge exit.
    ///
    /// If the vehicle can enter, returns `Some` with the next event that needs to be executed for
    /// the vehicle.
    /// Also returns the closing time of the bottleneck (if it gets closed).
    ///
    /// If the vehicle cannot enter (the bottleneck is closed), returns `None`.
    /// The next event of the vehicle will be triggered as soon as it can enter.
    fn vehicle_reaches_exit(
        &mut self,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
        next_event: VehicleEvent<T>,
    ) -> Option<(VehicleEvent<T>, Option<Time<T>>)> {
        if let Some(exit) = self.exit.as_mut() {
            exit.vehicle_reaches_exit(current_time, vehicle, next_event)
        } else {
            // Infinite flow + spillback is disabled: the vehicles can freely cross.
            // The bottleneck does not close.
            Some((next_event, None))
        }
    }

    /// A vehicle can successfully enter the edge.
    ///
    /// Returns the travel time of the vehicle until the end of the edge and the closing time of
    /// the edge entry.
    fn enters(
        &mut self,
        vehicle: &Vehicle<T>,
        current_time: Time<T>,
        edge: &RoadEdge<T>,
    ) -> (Time<T>, Time<T>) {
        // Notify the EdgeEntryState that a vehicle is entering and gets the closing time of the
        // bottleneck.
        let closing_time = self
            .entry
            .as_mut()
            .map(|entry| entry.vehicle_enters(vehicle))
            .unwrap_or(Time::zero());
        let travel_time = self.enters_road_segment(vehicle, current_time, edge);
        (travel_time, closing_time)
    }

    /// The entry bottleneck of the edge is re-opening.
    fn open_entry_bottleneck(
        &mut self,
        current_time: Time<T>,
    ) -> Option<Either<VehicleEvent<T>, AgentIndex>> {
        self.entry
            .as_mut()
            .and_then(|entry| entry.try_open_entry(current_time))
    }

    /// Forces the release of the next vehicle pending at the edge entry.
    fn force_release(&mut self, current_time: Time<T>) -> VehicleEvent<T> {
        self.entry
            .as_mut()
            .expect("Cannot force vehicle release when there is no edge entry")
            .force_release(current_time)
    }

    /// The exit bottleneck of the edge is re-opening.
    ///
    /// Returns the [VehicleEvent] of the released vehicle (if any).
    ///
    /// Returns the closing time of the bottleneck (if it gets closed).
    fn open_exit_bottleneck(
        &mut self,
        current_time: Time<T>,
    ) -> Option<(VehicleEvent<T>, Option<Time<T>>)> {
        self.exit
            .as_mut()
            .and_then(|exit| exit.open_bottleneck(current_time))
    }

    /// A vehicle can successfully exit the edge.
    ///
    /// Two values are returned:
    ///
    /// - The [VehicleEvent] of a vehicle pending to enter the edge, which is now released.
    ///   Or `None` if there is no vehicle pending or if the edge is still full.
    /// - The closing time of the exit bottleneck of the edge (if it gets closed).
    fn vehicle_exits(
        &mut self,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
    ) -> (Option<VehicleEvent<T>>, Option<Time<T>>) {
        // Try to release a vehicle at the entry of the edge.
        let released_vehicle_event = self
            .entry
            .as_mut()
            .and_then(|entry| entry.vehicle_exits(current_time, vehicle));
        // Remove the vehicle from the road segment.
        self.road.exits(vehicle, current_time);
        // Close the exit bottleneck.
        let closing_time_opt = self
            .exit
            .as_mut()
            .and_then(|exit| exit.vehicle_exits(vehicle));
        (released_vehicle_event, closing_time_opt)
    }

    /// Records the entry of a new vehicle on the edge and returns the travel time of this vehicle
    /// up to the Bottleneck.
    fn enters_road_segment(
        &mut self,
        vehicle: &Vehicle<T>,
        current_time: Time<T>,
        edge: &RoadEdge<T>,
    ) -> Time<T> {
        self.road.enters(vehicle, current_time);
        edge.get_travel_time(self.road.occupied_length, vehicle)
    }

    fn into_simulated_functions(self) -> SimulatedFunctions<T> {
        SimulatedFunctions {
            entry: self
                .entry
                .map(|entry| entry.into_simulated_ttf())
                .unwrap_or(TTF::Constant(Time::zero())),
            exit: self
                .exit
                .map(|exit| exit.into_simulated_ttf())
                .unwrap_or(TTF::Constant(Time::zero())),
            road: self.road.into_simulated_length_function(),
        }
    }
}

/// Struct that represents the state of a [RoadNetwork] at a given time.
#[derive(Clone, Debug)]
pub struct RoadNetworkState<T> {
    graph: DiGraph<RoadNodeState, RoadEdgeState<T>>,
    /// Map to find the current edge of all pending agents.
    pending_edges: HashMap<AgentIndex, EdgeIndex>,
    /// Maximum amout of time a vehicle is allowed to be pending.
    max_pending_duration: Time<T>,
    /// Record the number of warnings sent to the user.
    warnings: usize,
}

impl<T: TTFNum> RoadNetworkState<T> {
    /// Create an empty [RoadNetworkState] from a [RoadNetwork].
    pub fn from_network(
        network: &RoadNetwork<T>,
        recording_period: Interval<T>,
        recording_interval: Time<T>,
        spillback_enabled: bool,
        max_pending_duration: Time<T>,
    ) -> Self {
        let graph = network.get_graph().map(
            |_node_id, _n| RoadNodeState {},
            |_edge_id, e| {
                RoadEdgeState::new(e, recording_period, recording_interval, spillback_enabled)
            },
        );
        RoadNetworkState {
            graph,
            pending_edges: HashMap::new(),
            max_pending_duration,
            warnings: 0,
        }
    }

    /// Return a [RoadNetworkWeights] (i.e., travel times) from the observations recorded in the
    /// [RoadNetworkState].
    pub fn into_weights(
        self,
        network: &RoadNetwork<T>,
        parameters: &RoadNetworkParameters<T>,
        preprocess_data: &RoadNetworkPreprocessingData<T>,
    ) -> RoadNetworkWeights<T> {
        let mut weights = RoadNetworkWeights::with_capacity(
            preprocess_data.nb_unique_vehicles(),
            self.graph.edge_count(),
        );
        let (_, edge_states) = self.graph.into_nodes_edges();
        let edge_simulated_functions: Vec<SimulatedFunctions<T>> = edge_states
            .into_iter()
            .map(|e| e.weight.into_simulated_functions())
            .collect();
        for (uvehicle_id, vehicle) in preprocess_data
            .unique_vehicles
            .iter_uniques(&network.vehicles)
        {
            let edge_refs_iter = network.graph.edge_references();
            let vehicle_weights = &mut weights[uvehicle_id];
            for (funcs, edge_ref) in edge_simulated_functions.iter().zip(edge_refs_iter) {
                if vehicle.can_access(edge_ref.weight().id) {
                    let road_ttf = match &funcs.road {
                        XYF::Piecewise(road_pwl_length) => {
                            let road_pwl_ttf = road_pwl_length
                                .map(|l| edge_ref.weight().get_travel_time(l, vehicle));
                            if road_pwl_ttf.is_practically_cst(parameters.approximation_bound) {
                                TTF::Constant(road_pwl_ttf.y_at_index(0))
                            } else {
                                let mut road_ttf = road_pwl_ttf.to_ttf();
                                road_ttf.ensure_fifo();
                                TTF::Piecewise(road_ttf)
                            }
                        }
                        XYF::Constant(l) => {
                            TTF::Constant(edge_ref.weight().get_travel_time(*l, vehicle))
                        }
                    };
                    let mut ttf = funcs.entry.link(&road_ttf);
                    ttf.ensure_fifo();
                    ttf = ttf.link(&funcs.exit);
                    ttf.ensure_fifo();
                    vehicle_weights.insert(edge_ref.weight().id, ttf);
                } else {
                    vehicle_weights.insert(edge_ref.weight().id, TTF::Constant(Time::infinity()));
                }
            }
        }
        weights
    }

    /// Simulates the entry of a vehicle on an edge of the road network.
    ///
    /// Returns the next event to execute for this vehicle, if it can be executed immediately.
    /// Otherwise, returns `None` and the next event will be executed later.
    pub fn try_enter_edge(
        &mut self,
        edge_index: EdgeIndex,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
        next_event: VehicleEvent<T>,
        event_queue: &mut EventQueue<T>,
    ) -> Option<VehicleEvent<T>> {
        let edge = &mut self.graph[edge_index];
        match edge.vehicle_reaches_entry(current_time, vehicle, next_event) {
            Some(Either::Left(event)) => {
                // Next event can be executed immediately.
                Some(event)
            }
            Some(Either::Right(agent)) => {
                // Edge is full.
                // Create an event in `max_pending_duration` seconds to unlock the vehicle if it is
                // still stuck.
                self.pending_edges.insert(agent, edge_index);
                event_queue.push(Box::new(ForceVehicleRelease {
                    at_time: current_time + self.max_pending_duration,
                    agent,
                    edge: edge_index,
                }));
                None
            }
            None => {
                // Vehicle is queued.
                None
            }
        }
    }

    /// Simulates the exit of a vehicle from an edge of the road network.
    ///
    /// Returns the next event to execute for this vehicle, if it can be executed immediately.
    /// Otherwise, returns `None` and the next event will be executed later.
    pub fn try_exit_edge(
        &mut self,
        edge_index: EdgeIndex,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
        next_event: VehicleEvent<T>,
        event_queue: &mut EventQueue<T>,
    ) -> Option<VehicleEvent<T>> {
        let edge = &mut self.graph[edge_index];
        if let Some((next_event, closing_time_opt)) =
            edge.vehicle_reaches_exit(current_time, vehicle, next_event)
        {
            if let Some(closing_time) = closing_time_opt {
                debug_assert!(closing_time.is_sign_positive());
                event_queue.push(Box::new(BottleneckEvent {
                    at_time: current_time + closing_time,
                    edge_index,
                    position: BottleneckPosition::Exit,
                }));
            }
            Some(next_event)
        } else {
            None
        }
    }

    /// A vehicle is entering an edge of the road network.
    ///
    /// Returns the travel time of the vehicle until the end of the edge.
    ///
    /// The vehicle gets released from its previous edge (if any), which might trigger events of
    /// vehicle being allowed to enter this edge.
    ///
    /// Events to trigger the bottleneck re-opening at the edge entry and at the exit of the
    /// previous edge (if any) might be pushed to the event queue.
    pub fn enters_edge<'sim: 'event, 'event>(
        &mut self,
        edge_index: EdgeIndex,
        from: Option<EdgeIndex>,
        current_time: Time<T>,
        vehicle: &'sim Vehicle<T>,
        agent_id: AgentIndex,
        event_input: &'event mut EventInput<'sim, T>,
        event_alloc: &'event mut EventAlloc<T>,
        event_queue: &'event mut EventQueue<T>,
    ) -> Result<Time<T>> {
        let edge = &event_input.network.get_road_network().unwrap().graph[edge_index];
        let edge_state = &mut self.graph[edge_index];
        // The agent is no longer pending.
        self.pending_edges.remove(&agent_id);
        let (travel_time, closing_time) = edge_state.enters(vehicle, current_time, edge);
        if closing_time.is_zero() {
            // The edge's entry bottleneck can be open immediately.
            match edge_state.open_entry_bottleneck(current_time) {
                Some(Either::Left(event)) => {
                    // The vehicle entry has triggered the entry of a second vehicle.
                    // We can execute its event immediately.
                    debug_assert_eq!(event.get_time(), current_time);
                    event.execute(event_input, self, event_alloc, event_queue)?;
                }
                Some(Either::Right(agent)) => {
                    // The given agent is pending to enter the edge.
                    // Create an event to force release him / her in `max_pending_duration`
                    // seconds.
                    self.pending_edges.insert(agent, edge_index);
                    event_queue.push(Box::new(ForceVehicleRelease {
                        at_time: current_time + self.max_pending_duration,
                        agent,
                        edge: edge_index,
                    }));
                }
                None => (),
            }
        } else {
            // Push an event to open the edge's entry bottleneck later.
            debug_assert!(closing_time.is_sign_positive());
            event_queue.push(Box::new(BottleneckEvent {
                at_time: current_time + closing_time,
                edge_index,
                position: BottleneckPosition::Entry,
            }));
        }
        if let Some(previous_edge_index) = from {
            debug_assert_ne!(previous_edge_index, edge_index);
            self.release_from_edge(
                previous_edge_index,
                current_time,
                vehicle,
                event_input,
                event_alloc,
                event_queue,
            )?;
        }
        Ok(travel_time)
    }

    /// Releases a vehicle from an edge.
    ///
    /// If spillback is enabled, some vehicles can be released at the entry of the edge. The
    /// function will trigger their events.
    ///
    /// If the edge has a limited bottleneck flow, an event will be triggered later to re-open the
    /// edge's exit bottleneck.
    pub fn release_from_edge<'sim: 'event, 'event>(
        &mut self,
        edge_index: EdgeIndex,
        current_time: Time<T>,
        vehicle: &'sim Vehicle<T>,
        event_input: &'event mut EventInput<'sim, T>,
        event_alloc: &'event mut EventAlloc<T>,
        event_queue: &'event mut EventQueue<T>,
    ) -> Result<()> {
        let edge = &mut self.graph[edge_index];
        // Removes the vehicle from its previous edge and release any pending vehicle.
        let (event_opt, closing_time_opt) = edge.vehicle_exits(current_time, vehicle);
        if let Some(closing_time) = closing_time_opt {
            if closing_time.is_zero() {
                // The edge's exit bottleneck can be open immediately.
                if let Some((event, closing_time_opt)) = edge.open_exit_bottleneck(current_time) {
                    // The vehicle entry has triggered the entry of a second vehicle.
                    // We can execute its event immediately.
                    event.execute(event_input, self, event_alloc, event_queue)?;
                    // No closing time should be returned because overtaking is disabled on this
                    // edge.
                    debug_assert!(closing_time_opt.is_none());
                }
            } else {
                // Push an event to open the edge's exit bottleneck later.
                debug_assert!(closing_time.is_sign_positive());
                event_queue.push(Box::new(BottleneckEvent {
                    at_time: current_time + closing_time,
                    edge_index,
                    position: BottleneckPosition::Exit,
                }));
            }
        }
        if let Some(event) = event_opt {
            // Execute the event of the release vehicle.
            event.execute(event_input, self, event_alloc, event_queue)?;
        }
        Ok(())
    }
}

/// Event used to force the release of a vehicle pending to enter a link.
#[derive(Clone, Debug, PartialEq)]
pub struct ForceVehicleRelease<T> {
    /// Time at which the vehicle must be released.
    at_time: Time<T>,
    /// Id of the agent the vehicle belongs to.
    agent: AgentIndex,
    /// Id of the edge the vehicle is pending on.
    edge: EdgeIndex,
}

impl<T: TTFNum> Event<T> for ForceVehicleRelease<T> {
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim, T>,
        road_network_state: &'event mut RoadNetworkState<T>,
        alloc: &'event mut EventAlloc<T>,
        events: &'event mut EventQueue<T>,
    ) -> Result<bool> {
        if road_network_state.pending_edges.get(&self.agent) != Some(&self.edge) {
            // The agent is no longer pending on the edge.
            return Ok(false);
        }
        let edge = &mut road_network_state.graph[self.edge];
        let event = edge.force_release(self.at_time);
        debug_assert_eq!(event.agent_id(), self.agent);
        if road_network_state.warnings <= MAX_WARNINGS {
            input.progress_bar.suspend(|| {
                warn!(
                    "Forcing the release of agent {} from edge {} at time {}",
                    self.agent.index(),
                    self.edge.index(),
                    self.at_time
                );
            });
            if road_network_state.warnings == MAX_WARNINGS {
                input.progress_bar.suspend(|| {
                    warn!("Ignoring further warnings...");
                });
            }
            road_network_state.warnings += 1;
        }
        event.execute(input, road_network_state, alloc, events)
    }
    fn get_time(&self) -> Time<T> {
        self.at_time
    }
}

/// Event representing the opening of a Bottleneck.
#[derive(Clone, Debug, PartialEq)]
pub struct BottleneckEvent<T> {
    /// Time at which the Bottleneck opens.
    at_time: Time<T>,
    /// Id of the edge where the Bottleneck is located.
    edge_index: EdgeIndex,
    /// Position of the bottleneck (entry or exit of the edge).
    position: BottleneckPosition,
}

impl<T: TTFNum> Event<T> for BottleneckEvent<T> {
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim, T>,
        road_network_state: &'event mut RoadNetworkState<T>,
        alloc: &'event mut EventAlloc<T>,
        events: &'event mut EventQueue<T>,
    ) -> Result<bool> {
        let edge_state = &mut road_network_state.graph[self.edge_index];
        match self.position {
            BottleneckPosition::Entry => {
                match edge_state.open_entry_bottleneck(self.at_time) {
                    Some(Either::Left(event)) => {
                        // Vehicle can enter.
                        debug_assert_eq!(self.at_time, event.get_time());
                        event.execute(input, road_network_state, alloc, events)?;
                    }
                    Some(Either::Right(agent)) => {
                        // The given agent is pending to enter the edge.
                        // Create an event to force release him / her in `max_pending_duration`
                        // seconds.
                        road_network_state
                            .pending_edges
                            .insert(agent, self.edge_index);
                        events.push(Box::new(ForceVehicleRelease {
                            at_time: self.at_time + road_network_state.max_pending_duration,
                            agent,
                            edge: self.edge_index,
                        }));
                    }
                    None => {
                        // No vehicle to release.
                    }
                }
            }
            BottleneckPosition::Exit => {
                if let Some((event, closing_time_opt)) =
                    edge_state.open_exit_bottleneck(self.at_time)
                {
                    debug_assert_eq!(self.at_time, event.get_time());
                    event.execute(input, road_network_state, alloc, events)?;
                    if let Some(closing_time) = closing_time_opt {
                        let bottleneck_event = Box::new(BottleneckEvent {
                            at_time: self.at_time + closing_time,
                            edge_index: self.edge_index,
                            position: self.position,
                        });
                        if closing_time.is_zero() {
                            // Execute immediately the bottleneck opening.
                            bottleneck_event.execute(input, road_network_state, alloc, events)?;
                        } else {
                            debug_assert!(closing_time.is_sign_positive());
                            // Push the bottleneck event to the queue.
                            events.push(bottleneck_event);
                        }
                    }
                }
            }
        }
        Ok(false)
    }
    fn get_time(&self) -> Time<T> {
        self.at_time
    }
}

#[derive(Clone, Debug)]
struct WaitXYFBuilder<T> {
    points: Vec<Time<T>>,
    start_x: Time<T>,
    end_x: Time<T>,
    interval_x: Time<T>,
    current_index: usize,
    last_point: (Time<T>, Time<T>),
    weighted_y: Time<T>,
}

impl<T> WaitXYFBuilder<T>
where
    T: TTFNum,
{
    fn new(period: Interval<T>, interval_x: Time<T>) -> Self {
        let n = (period.length() / interval_x).trunc().to_usize().unwrap() + 1;
        WaitXYFBuilder {
            points: Vec::with_capacity(n),
            start_x: period.start(),
            end_x: period.end(),
            interval_x,
            current_index: 0,
            last_point: (period.start(), period.start()),
            weighted_y: Time::zero(),
        }
    }

    fn push(&mut self, entry_time: Time<T>, exit_time: Time<T>) {
        debug_assert!(entry_time >= self.start_x);
        if entry_time > self.end_x {
            // Skip.
            return;
        }
        let index = ((entry_time - self.start_x) / self.interval_x)
            .round()
            .to_usize()
            .unwrap();
        debug_assert!(index >= self.current_index);
        if index > self.current_index {
            self.finish_interval(index);
        }
        self.add_record(entry_time, exit_time);
    }

    fn add_record(&mut self, en_t1: Time<T>, ex_t1: Time<T>) {
        let (en_t0, ex_t0) = self.last_point;
        // The exiting time cannot decrease.
        debug_assert!(ex_t0 <= ex_t1);
        let duration = en_t1 - en_t0;
        debug_assert!(duration.is_sign_positive());
        // At `en_t0`, the waiting time was `ex_t0 - en_t0`.
        // At `en_t1`, the waiting time was `ex_t1 - en_t1`.
        // Just before `en_t1`, the exit time was `max(en_t1, ex_t0)`.
        // Just before `en_t1`, the waiting time was `max(en_t1, ex_t0) - en_t1
        // = max(0, ex_t0 - en_t1)`
        // Therefore, from `en_t0` to `en_t1`, the average waiting time was the average between
        // `ex_t0 - en_t0` and `max(0, ex_t0 - en_t1)`.
        let average_y = Time::average(ex_t0 - en_t0, std::cmp::max(Time::zero(), ex_t0 - en_t1));
        self.weighted_y += duration * average_y;
        self.last_point = (en_t1, ex_t1);
    }

    fn finish_interval(&mut self, index: usize) {
        // Find current interval bounds.
        let half_interval_length = Time::average(self.interval_x, Time::zero());
        let interval_mid =
            self.start_x + self.interval_x * Time::from_usize(self.current_index).unwrap();
        let interval_start = std::cmp::max(self.start_x, interval_mid - half_interval_length);
        let interval_end = std::cmp::min(self.end_x, interval_mid + half_interval_length);
        // The last event that occured was in the interval and we know that no other event occurs
        // in this interval.
        debug_assert!(self.last_point.0 >= interval_start);
        debug_assert!(self.last_point.0 <= interval_end);
        // Compute the exit time at the end of the interval.
        let end_exit_time = std::cmp::max(self.last_point.1, interval_end);
        self.add_record(interval_end, end_exit_time);
        // Compute and add `y` value for current interval.
        let interval_length = interval_end - interval_start;
        let y = self.weighted_y / interval_length;
        self.points.push(y);
        // Switch to next interval.
        self.weighted_y = Time::zero();
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

    fn finish(mut self) -> TTF<Time<T>> {
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

#[derive(Clone, Debug)]
struct LengthXYFBuilder<T> {
    points: Vec<Length<T>>,
    start_x: Time<T>,
    end_x: Time<T>,
    interval_x: Time<T>,
    current_index: usize,
    last_point: (Time<T>, Length<T>),
    weighted_y: NoUnit<T>,
}

impl<T> LengthXYFBuilder<T>
where
    T: TTFNum,
{
    fn new(period: Interval<T>, interval_x: Time<T>) -> Self {
        let n = (period.length() / interval_x).trunc().to_usize().unwrap() + 1;
        LengthXYFBuilder {
            points: Vec::with_capacity(n),
            start_x: period.start(),
            end_x: period.end(),
            interval_x,
            current_index: 0,
            last_point: (period.start(), Length::zero()),
            weighted_y: NoUnit::zero(),
        }
    }

    fn push(&mut self, time: Time<T>, length: Length<T>) {
        debug_assert!(time >= self.start_x);
        if time > self.end_x {
            // Skip.
            return;
        }
        let index = ((time - self.start_x) / self.interval_x)
            .round()
            .to_usize()
            .unwrap();
        debug_assert!(index >= self.current_index);
        if index > self.current_index {
            self.finish_interval(index);
        }
        self.add_record(time, length);
    }

    fn add_record(&mut self, t1: Time<T>, l1: Length<T>) {
        let (t0, l0) = self.last_point;
        let duration = t1 - t0;
        debug_assert!(duration.is_sign_positive());
        // From `t0` to `t1`, the length is `l0`.
        self.weighted_y += Into::<NoUnit<T>>::into(duration) * Into::<NoUnit<T>>::into(l0);
        self.last_point = (t1, l1);
    }

    fn finish_interval(&mut self, index: usize) {
        // Find current interval bounds.
        let half_interval_length = Time::average(self.interval_x, Time::zero());
        let interval_mid =
            self.start_x + self.interval_x * Time::from_usize(self.current_index).unwrap();
        let interval_start = std::cmp::max(self.start_x, interval_mid - half_interval_length);
        let interval_end = std::cmp::min(self.end_x, interval_mid + half_interval_length);
        // The last event that occured was in the interval and we know that no other event occurs
        // in this interval.
        // Therefore, the length at the end of the interval was the same as the last recorded
        // length.
        debug_assert!(self.last_point.0 >= interval_start);
        debug_assert!(self.last_point.0 <= interval_end);
        self.add_record(interval_end, self.last_point.1);
        // Compute and add `y` value for current interval.
        let interval_length = interval_end - interval_start;
        let y = self.weighted_y / interval_length.into();
        self.points.push(y.into());
        // Switch to next interval.
        self.weighted_y = NoUnit::zero();
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

    fn finish(mut self) -> XYF<Time<T>, Length<T>, NoUnit<T>> {
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
