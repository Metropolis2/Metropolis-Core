// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of [RoadNetworkState].
use std::collections::VecDeque;
use std::marker::PhantomData;

use anyhow::Result;
use either::Either;
use enum_as_inner::EnumAsInner;
use hashbrown::HashSet;
use log::warn;
use num_traits::{Float, Zero};
use petgraph::graph::{DiGraph, EdgeIndex};
use ttf::{PwlXYF, TTFNum, TTF, XYF};

use super::vehicle::Vehicle;
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetwork, RoadNetworkPreprocessingData};
use crate::event::{Event, EventInput, EventQueue};
use crate::mode::trip::event::VehicleEvent;
use crate::units::{Flow, Interval, Length, NoUnit, Time};

/// Struct that holds data on the current state of a [RoadNode].
#[derive(Clone, Debug)]
struct RoadNodeState {}

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

/// Next event to execute for a queued vehicle and time at which the vehicle entered the queue.
type QueuedVehicle<T> = (VehicleEvent<T>, Time<T>);

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
    waiting_time_history: PwlXYFBuilder<Time<T>, Time<T>, Time<T>>,
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
            waiting_time_history: PwlXYFBuilder::new(period.0, interval),
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
        next_event: VehicleEvent<T>,
    ) -> Option<Either<VehicleEvent<T>, EdgeIndex>> {
        match (self.is_open(), self.is_full()) {
            (true, false) => {
                // Free to go.
                debug_assert!(self.queue.is_empty());
                // Close the edge entry. It will re-open again when the vehicle will have
                // succesfully entered the edge.
                self.status = EdgeEntryStatus::Closed;
                self.record(current_time, current_time);
                Some(Either::Left(next_event))
            }
            (true, true) => {
                // Edge entry is open but edge is full.
                debug_assert!(self.queue.is_empty());
                let edge_id = next_event.previous_edge();
                self.status = EdgeEntryStatus::Full;
                self.queue.push_back((next_event, current_time));
                edge_id.map(|e| Either::Right(e))
            }
            (false, _) => {
                // Edge is closed.
                self.queue.push_back((next_event, current_time));
                None
            }
        }
    }

    /// A vehicle has succesfully enterd the edge.
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
    ///   `Full`, returns `Some(Right)` with the index of the current edge of the pending vehicle
    ///   (or `None` if the pending vehicle is not currently on an edge).
    fn try_open_entry(
        &mut self,
        current_time: Time<T>,
    ) -> Option<Either<VehicleEvent<T>, EdgeIndex>> {
        if let Some((mut event, entry_time)) = self.queue.pop_front() {
            if self.is_full() {
                // The edge is full, put the vehicle back in the queue (at the front).
                let edge_id = event.previous_edge();
                self.status = EdgeEntryStatus::Full;
                self.queue.push_front((event, entry_time));
                edge_id.map(|e| Either::Right(e))
            } else {
                // A new vehicle is released, the bottleneck stays closed.
                self.status = EdgeEntryStatus::Closed;
                self.record(entry_time, current_time);
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
        let (mut event, entry_time) = self.queue.pop_front().expect("No vehicle to release");
        self.status = EdgeEntryStatus::Closed;
        self.record(entry_time, current_time);
        event.set_time(current_time);
        event
    }

    /// A vehicle has succesfully exited the edge.
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
            let (mut event, entry_time) = self.queue.pop_front().unwrap();
            self.record(entry_time, current_time);
            event.set_time(current_time);
            Some(event)
        } else {
            // The bottleneck is either open with no vehicle pending, closed or still full.
            None
        }
    }

    /// Records the entry and exit of a vehicle from the edge's entry at a given time.
    fn record(&mut self, entry_time: Time<T>, exit_time: Time<T>) {
        // The average waiting time from last entry time to this entry time is half of the waiting
        // time for the vehicle which entered at this entry time.
        self.waiting_time_history.push(
            entry_time,
            Time::average(exit_time - entry_time, Time::zero()),
        );
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
    waiting_time_history: PwlXYFBuilder<Time<T>, Time<T>, Time<T>>,
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
            waiting_time_history: PwlXYFBuilder::new(period.0, interval),
        }
    }

    /// Returns `true` if the edge exit is open.
    fn is_open(&self) -> bool {
        self.status == EdgeExitStatus::Open
    }

    /// Returns the closing time of the bottleneck when the given vehicle crosses it.
    fn get_closing_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.effective_flow
            .map(|f| vehicle.get_pce() / f)
            .unwrap_or(Time::zero())
    }

    /// A vehicle is reaching the end of the edge.
    ///
    /// If the exit is open, returns the next event of the vehicle.
    ///
    /// If the exit is closed, pushes the vehicle to the end of the queue and returns `None`.
    fn vehicle_reaches_exit(
        &mut self,
        current_time: Time<T>,
        next_event: VehicleEvent<T>,
    ) -> Option<VehicleEvent<T>> {
        if self.is_open() {
            debug_assert!(self.queue.is_empty());
            // Close the edge exit. It will re-open again when the vehicle will have succesfully
            // exited the edge (it can get trapped at the entry of the downstream edge).
            self.status = EdgeExitStatus::Closed;
            self.record(current_time, current_time);
            Some(next_event)
        } else {
            // Bottleneck is closed.
            self.queue.push_back((next_event, current_time));
            None
        }
    }

    /// A vehicle has succesfully exited the edge.
    ///
    /// Returns the closing time of the bottleneck.
    fn vehicle_exits(&mut self, vehicle: &Vehicle<T>) -> Time<T> {
        debug_assert_eq!(self.status, EdgeExitStatus::Closed);
        self.status = EdgeExitStatus::Closed;
        self.get_closing_time(vehicle)
    }

    /// The bottleneck re-opens.
    ///
    /// Returns the event to execute for the next vehicle in the queue (if any).
    fn open_bottleneck(&mut self, current_time: Time<T>) -> Option<VehicleEvent<T>> {
        debug_assert_eq!(self.status, EdgeExitStatus::Closed);
        if let Some((mut event, entry_time)) = self.queue.pop_front() {
            // A new vehicle is released, the bottleneck stays closed.
            self.record(entry_time, current_time);
            event.set_time(current_time);
            Some(event)
        } else {
            // The bottleneck is now open.
            self.status = EdgeExitStatus::Open;
            None
        }
    }

    /// Records the entry and exit of a vehicle from the edge's exit at a given time.
    fn record(&mut self, entry_time: Time<T>, exit_time: Time<T>) {
        // The average waiting time from last entry time to this entry time is half of the waiting
        // time for the vehicle which entered at this entry time.
        self.waiting_time_history.push(
            entry_time,
            Time::average(exit_time - entry_time, Time::zero()),
        );
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
        next_event: VehicleEvent<T>,
    ) -> Option<Either<VehicleEvent<T>, EdgeIndex>> {
        if let Some(entry) = self.entry.as_mut() {
            entry.vehicle_reaches_entry(current_time, next_event)
        } else {
            // Infinite flow + spillback is disabled: the vehicles can freely cross.
            Some(Either::Left(next_event))
        }
    }

    /// A vehicle is reaching the edge exit.
    ///
    /// If the vehicle can enter, returns `Some` with the next event that needs to be executed for
    /// the vehicle.
    ///
    /// If the vehicle cannot enter (the bottleneck is closed), returns `None`.
    /// The next event of the vehicle will be triggered as soon as it can enter.
    fn vehicle_reaches_exit(
        &mut self,
        current_time: Time<T>,
        next_event: VehicleEvent<T>,
    ) -> Option<VehicleEvent<T>> {
        if let Some(exit) = self.exit.as_mut() {
            exit.vehicle_reaches_exit(current_time, next_event)
        } else {
            // Infinite flow + spillback is disabled: the vehicles can freely cross.
            Some(next_event)
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
    ) -> Option<Either<VehicleEvent<T>, EdgeIndex>> {
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
    fn open_exit_bottleneck(&mut self, current_time: Time<T>) -> Option<VehicleEvent<T>> {
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
    /// - The closing time of the exit bottleneck of the edge.
    fn vehicle_exits(
        &mut self,
        current_time: Time<T>,
        vehicle: &Vehicle<T>,
    ) -> (Option<VehicleEvent<T>>, Time<T>) {
        // Try to release a vehicle at the entry of the edge.
        let released_vehicle_event = self
            .entry
            .as_mut()
            .and_then(|entry| entry.vehicle_exits(current_time, vehicle));
        // Remove the vehicle from the road segment.
        self.road.exits(vehicle, current_time);
        // Close the exit bottleneck.
        let closing_time = self
            .exit
            .as_mut()
            .map(|exit| exit.vehicle_exits(vehicle))
            .unwrap_or(Time::zero());
        (released_vehicle_event, closing_time)
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
    /// For each edge that is blocked because a vehicle is pending to exit, value is `Some` with the
    /// id of the next edge for the pending vehicle.
    /// For edges that are not full, value is `None`.
    edges_full: Vec<Option<EdgeIndex>>,
}

impl<T: TTFNum> RoadNetworkState<T> {
    /// Create an empty [RoadNetworkState] from a [RoadNetwork].
    pub fn from_network(
        network: &RoadNetwork<T>,
        recording_period: Interval<T>,
        recording_interval: Time<T>,
        spillback_enabled: bool,
    ) -> Self {
        let graph = network.get_graph().map(
            |_node_id, _n| RoadNodeState {},
            |_edge_id, e| {
                RoadEdgeState::new(e, recording_period, recording_interval, spillback_enabled)
            },
        );
        RoadNetworkState {
            edges_full: vec![None; graph.edge_count()],
            graph,
        }
    }

    /// Return a [RoadNetworkWeights] (i.e., travel times) from the observations recorded in the
    /// [RoadNetworkState].
    pub fn into_weights(
        self,
        network: &RoadNetwork<T>,
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
            let edge_refs_iter = network.graph.edge_weights();
            let vehicle_weights = &mut weights[uvehicle_id];
            for (funcs, edge_ref) in edge_simulated_functions.iter().zip(edge_refs_iter) {
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
                let mut ttf = funcs.entry.link(&road_ttf).link(&funcs.exit);
                ttf.ensure_fifo();
                vehicle_weights.push(ttf);
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
        next_event: VehicleEvent<T>,
    ) -> Option<VehicleEvent<T>> {
        let edge = &mut self.graph[edge_index];
        match edge.vehicle_reaches_entry(current_time, next_event) {
            Some(Either::Left(event)) => {
                // Next event can be executed immediately.
                Some(event)
            }
            Some(Either::Right(previous_edge)) => {
                // Edge is full.
                debug_assert!(self.edges_full[previous_edge.index()].is_none());
                self.edges_full[previous_edge.index()] = Some(edge_index);
                // Force the release of the vehicle if it is needed to prevent a gridlock.
                self.check_gridlock(edge_index, current_time)
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
        next_event: VehicleEvent<T>,
    ) -> Option<VehicleEvent<T>> {
        let edge = &mut self.graph[edge_index];
        edge.vehicle_reaches_exit(current_time, next_event)
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
        event_input: &'event mut EventInput<'sim, T>,
        event_queue: &'event mut EventQueue<T>,
    ) -> Result<Time<T>> {
        let edge = &event_input.network.get_road_network().unwrap().graph[edge_index];
        let edge_state = &mut self.graph[edge_index];
        // Reset the indicator that the edge is full (if needed).
        self.edges_full[edge_index.index()] = None;
        let (travel_time, closing_time) = edge_state.enters(vehicle, current_time, edge);
        if closing_time.is_zero() {
            // The edge's entry bottleneck can be open immediately.
            match edge_state.open_entry_bottleneck(current_time) {
                Some(Either::Left(event)) => {
                    // The vehicle entry has triggered the entry of a second vehicle.
                    // We can execute its event immediately.
                    debug_assert_eq!(event.get_time(), current_time);
                    event.execute(event_input, self, event_queue)?;
                }
                Some(Either::Right(previous_edge)) => {
                    // Vehicle from `previous_edge` is pending to enter the current edge, which
                    // is full.
                    debug_assert!(self.edges_full[previous_edge.index()].is_none());
                    self.edges_full[previous_edge.index()] = Some(edge_index);
                    if let Some(event) = self.check_gridlock(edge_index, current_time) {
                        debug_assert_eq!(event.get_time(), current_time);
                        event.execute(event_input, self, event_queue)?;
                    }
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
            self.release_from_edge(
                previous_edge_index,
                current_time,
                vehicle,
                event_input,
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
        event_queue: &'event mut EventQueue<T>,
    ) -> Result<()> {
        let edge = &mut self.graph[edge_index];
        // Removes the vehicle from its previous edge and release any pending vehicle.
        let (event_opt, closing_time) = edge.vehicle_exits(current_time, vehicle);
        if closing_time.is_zero() {
            // The edge's exit bottleneck can be open immediately.
            if let Some(event) = edge.open_exit_bottleneck(current_time) {
                // The vehicle entry has triggered the entry of a second vehicle.
                // We can execute its event immediately.
                event.execute(event_input, self, event_queue)?;
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
        if let Some(event) = event_opt {
            // Execute the event of the release vehicle.
            event.execute(event_input, self, event_queue)?;
        }
        Ok(())
    }

    /// Checks if there is a gridlock with edge `from`.
    ///
    /// If there is a gridlock, returns the [VehicleEvent] of the vehicle to release to prevent the
    /// gridlock.
    /// Otherwise, returns `None`.
    fn check_gridlock(
        &mut self,
        from: EdgeIndex,
        current_time: Time<T>,
    ) -> Option<VehicleEvent<T>> {
        if self.has_gridlock(from) {
            // Force the release of the pending vehicle to prevent a gridlock from
            // forming.
            warn!(
                "Forcing the release of a vehicle on edge {} to prevent a gridlock",
                from.index()
            );
            Some(self.graph[from].force_release(current_time))
        } else {
            None
        }
    }

    /// Returns `true` if there is a gridlock with edge `from`, i.e., there is a loop of pending
    /// edges which includes edge `from`.
    fn has_gridlock(&self, from: EdgeIndex) -> bool {
        let mut current_edge = from;
        let mut edges = HashSet::new();
        if cfg!(debug_assertions) {
            edges.insert(current_edge);
        }
        while let Some(target) = self.edges_full[current_edge.index()] {
            if target == from {
                return true;
            }
            if cfg!(debug_assertions) {
                debug_assert!(!edges.contains(&target));
            }
            current_edge = target;
        }
        false
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
        events: &'event mut EventQueue<T>,
    ) -> Result<bool> {
        let edge_state = &mut road_network_state.graph[self.edge_index];
        match self.position {
            BottleneckPosition::Entry => {
                match edge_state
                    .entry
                    .as_mut()
                    .unwrap()
                    .try_open_entry(self.at_time)
                {
                    Some(Either::Left(event)) => {
                        // Vehicle can enter.
                        debug_assert_eq!(self.at_time, event.get_time());
                        event.execute(input, road_network_state, events)?;
                    }
                    Some(Either::Right(previous_edge)) => {
                        // Vehicle from `previous_edge` is pending to enter the current edge, which
                        // is full.
                        debug_assert!(
                            road_network_state.edges_full[previous_edge.index()].is_none()
                        );
                        road_network_state.edges_full[previous_edge.index()] =
                            Some(self.edge_index);
                        if let Some(event) =
                            road_network_state.check_gridlock(self.edge_index, self.at_time)
                        {
                            debug_assert_eq!(event.get_time(), self.at_time);
                            event.execute(input, road_network_state, events)?;
                        }
                    }
                    None => {
                        // No vehicle to release.
                    }
                }
            }
            BottleneckPosition::Exit => {
                if let Some(event) = edge_state
                    .exit
                    .as_mut()
                    .unwrap()
                    .open_bottleneck(self.at_time)
                {
                    debug_assert_eq!(self.at_time, event.get_time());
                    event.execute(input, road_network_state, events)?;
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
