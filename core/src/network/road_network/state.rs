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
use num_traits::{ConstZero, Zero};
use petgraph::graph::{DiGraph, EdgeIndex};
use ttf::{PwlXYF, TTF, XYF};

use super::vehicle::Vehicle;
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetworkPreprocessingData};
use crate::event::{Event, EventAlloc, EventInput, EventQueue};
use crate::mode::trip::event::VehicleEvent;
use crate::population::AgentIndex;
use crate::units::*;

const MAX_WARNINGS: usize = 20;

/// Struct that holds data on the current state of a [RoadNode].
#[derive(Clone, Debug)]
struct RoadNodeState {}

/// Struct representing the current state of the running part of a [RoadEdge].
#[derive(Clone, Debug)]
struct RoadSegment {
    /// Total length of the vehicles currently on the segment.
    occupied_length: NonNegativeMeters,
    /// History of the length of vehicles on the segment.
    length_history: LengthXYFBuilder,
}

impl RoadSegment {
    fn new() -> Self {
        let length_history = LengthXYFBuilder::new();
        RoadSegment {
            occupied_length: NonNegativeMeters::ZERO,
            length_history,
        }
    }

    /// Records the entry of a new vehicle on the segment.
    fn enters(&mut self, vehicle_headway: NonNegativeMeters, current_time: NonNegativeSeconds) {
        // Record the occupied length when the vehicle entered.
        self.length_history.push(current_time, self.occupied_length);
        self.occupied_length += vehicle_headway;
    }

    /// Records the exit of a vehicle from the segment.
    fn exits(&mut self, vehicle_headway: NonNegativeMeters) {
        // The result of this operation is guaranteed to be non-negative because we only substract
        // vehicle headways that were previously added.
        self.occupied_length =
            NonNegativeMeters::try_from(self.occupied_length - vehicle_headway).unwrap();
    }

    /// Consumes the [RoadSegment] and returns a [PwlXYF] with the simulated length.
    fn into_simulated_length_function(self) -> XYF<AnySeconds, AnyMeters, AnyNum> {
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
struct SimulatedFunctions {
    entry: TTF<AnySeconds>,
    exit: TTF<AnySeconds>,
    road: XYF<AnySeconds, AnyMeters, AnyNum>,
}

/// Next event to execute for a queued vehicle, time at which the vehicle entered the queue and
/// edge it is coming from (if any).
#[derive(Clone, Debug)]
struct QueuedVehicle {
    event: VehicleEvent,
    vehicle_pce: PCE,
    entry_time: NonNegativeSeconds,
}

/// Queue of vehicles.
type VehicleQueue = VecDeque<QueuedVehicle>;

/// State of the congestion at the entry of the edge, that can result from the entry bottleneck or
/// from the edge being full.
#[derive(Clone, Debug)]
struct EdgeEntryState {
    /// Current length available for vehicles on the edge, i.e., total length of the edge minus the
    /// total headway length of vehicles currently on the edge.
    /// Or `None` if spillback is disabled.
    available_length: Option<AnyMeters>,
    /// Effective flow of the edge.
    /// Or `None` if the flow is infinite.
    effective_flow: Option<Flow>,
    /// Indicates the status of the edge entry (open, closed or pending).
    status: EdgeEntryStatus,
    /// Queue of vehicles currently waiting to enter the edge.
    queue: VehicleQueue,
    /// Waiting time PwlTTF function.
    waiting_time_history: WaitXYFBuilder,
}

impl EdgeEntryState {
    /// Initializes a new [EdgeEntryState] for a given edge.
    fn new(edge: &RoadEdge) -> Option<Self> {
        let available_length = if super::parameters::spillback() {
            Some(edge.total_length().into())
        } else {
            None
        };
        let effective_flow =
            if super::parameters::constrain_inflow() && edge.get_effective_flow().is_some() {
                Some(edge.get_effective_flow().unwrap())
            } else {
                None
            };
        Some(Self {
            available_length,
            effective_flow,
            status: EdgeEntryStatus::Open,
            queue: VehicleQueue::new(),
            waiting_time_history: WaitXYFBuilder::new(),
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
            .map(|l| l.is_negative())
            .unwrap_or(false)
    }

    /// Reduces the available length of the edge by the given amount.
    fn reduce_available_length(&mut self, length: NonNegativeMeters) {
        if let Some(available_length) = self.available_length.as_mut() {
            *available_length -= length.into();
        }
    }

    /// Increases the available length of the edge by the given amount.
    fn increase_available_length(&mut self, length: NonNegativeMeters) {
        if let Some(available_length) = self.available_length.as_mut() {
            *available_length += length.into();
        }
    }

    /// Returns the closing time of the bottleneck when the given vehicle crosses it.
    ///
    /// Returns zero if there is no bottleneck.
    fn get_closing_time(&self, vehicle_pce: PCE) -> NonNegativeSeconds {
        self.effective_flow
            .map(|f| vehicle_pce / f)
            .unwrap_or(NonNegativeSeconds::ZERO)
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
        current_time: NonNegativeSeconds,
        vehicle_pce: PCE,
        next_event: VehicleEvent,
    ) -> Option<Either<VehicleEvent, AgentIndex>> {
        match (self.is_open(), self.is_full()) {
            (true, false) => {
                // Free to go.
                debug_assert!(self.queue.is_empty());
                // Record the null waiting time.
                self.record(current_time, current_time);
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
                    vehicle_pce,
                    entry_time: current_time,
                });
                Some(Either::Right(agent_id))
            }
            (false, _) => {
                // Edge is closed.
                self.queue.push_back(QueuedVehicle {
                    event: next_event,
                    vehicle_pce,
                    entry_time: current_time,
                });
                None
            }
        }
    }

    /// A vehicle has successfully entered the edge.
    ///
    /// Returns the closing time of the bottleneck.
    fn vehicle_enters(
        &mut self,
        vehicle_pce: PCE,
        vehicle_headway: NonNegativeMeters,
        is_phantom: bool,
    ) -> NonNegativeSeconds {
        debug_assert_ne!(self.status, EdgeEntryStatus::Open);
        let vehicle_headway = if is_phantom {
            // The vehicle has been phantomed, the available length is not reduced.
            NonNegativeMeters::ZERO
        } else {
            vehicle_headway
        };
        self.reduce_available_length(vehicle_headway);
        self.status = EdgeEntryStatus::Closed;
        self.get_closing_time(vehicle_pce)
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
        current_time: NonNegativeSeconds,
    ) -> Option<Either<VehicleEvent, AgentIndex>> {
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
    fn force_release(&mut self, current_time: NonNegativeSeconds) -> VehicleEvent {
        self.release_next_queued_vehicle(current_time, true)
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
        current_time: NonNegativeSeconds,
        vehicle_headway: NonNegativeMeters,
    ) -> Option<VehicleEvent> {
        self.increase_available_length(vehicle_headway);
        if self.status == EdgeEntryStatus::Full && !self.is_full() {
            // The edge was full but it is not anymore.
            // Release the pending vehicle.
            Some(self.release_next_queued_vehicle(current_time, false))
        } else {
            // The bottleneck is either open with no vehicle pending, closed or still full.
            None
        }
    }

    /// Releases the next vehicle in the queue and returns its next event.
    fn release_next_queued_vehicle(
        &mut self,
        current_time: NonNegativeSeconds,
        phantom: bool,
    ) -> VehicleEvent {
        let queued_vehicle = self.queue.pop_front().expect("No vehicle to release");
        self.status = EdgeEntryStatus::Closed;
        self.record(queued_vehicle.entry_time, current_time);
        let mut event = queued_vehicle.event;
        event.set_time(current_time);
        if phantom {
            event.set_phantom();
        }
        event
    }

    /// Records the entry and exit of a vehicle from the edge's entry at a given time.
    fn record(&mut self, entry_time: NonNegativeSeconds, exit_time: NonNegativeSeconds) {
        self.waiting_time_history.push(entry_time, exit_time);
    }

    /// Consumes the [EdgeEntryState] and returns a [TTF] with the simulated waiting time.
    fn into_simulated_ttf(self) -> TTF<AnySeconds> {
        let mut ttf = self.waiting_time_history.finish();
        ttf.ensure_fifo();
        ttf
    }
}

/// State of the congestion at the exit of the edge.
#[derive(Clone, Debug)]
struct EdgeExitState {
    /// Effective flow of the edge.
    /// Or `None` if the flow is infinite.
    effective_flow: Option<Flow>,
    /// Indicates the status of the edge exit (open or closed).
    status: EdgeExitStatus,
    /// Queue of vehicles currently waiting to exit the edge.
    queue: VehicleQueue,
    /// Waiting time PwlTTF function.
    waiting_time_history: WaitXYFBuilder,
    /// Is overtaking allowed at the edge exit?
    overtaking_allowed: bool,
}

impl EdgeExitState {
    /// Initializes a new [EdgeExitState] for a given edge.
    fn new(edge: &RoadEdge) -> Self {
        let effective_flow = if edge.get_effective_flow().is_some() {
            Some(edge.get_effective_flow().unwrap())
        } else {
            None
        };
        Self {
            effective_flow,
            status: EdgeExitStatus::Open,
            queue: VehicleQueue::new(),
            waiting_time_history: WaitXYFBuilder::new(),
            overtaking_allowed: edge.overtaking_is_allowed(),
        }
    }

    /// Returns `true` if the edge exit is open.
    fn is_open(&self) -> bool {
        self.status == EdgeExitStatus::Open
    }

    /// Returns the closing time of the bottleneck given the PCE of the vehicle which crosses it.
    fn get_closing_time(&self, vehicle_pce: PCE) -> NonNegativeSeconds {
        self.effective_flow
            .map(|f| vehicle_pce / f)
            .unwrap_or(NonNegativeSeconds::ZERO)
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
        current_time: NonNegativeSeconds,
        vehicle_pce: PCE,
        next_event: VehicleEvent,
    ) -> Option<(VehicleEvent, Option<NonNegativeSeconds>)> {
        if self.is_open() {
            debug_assert!(self.queue.is_empty());
            // Record the null waiting time.
            self.record(current_time, current_time);
            // Close the edge exit.
            self.status = EdgeExitStatus::Closed;
            let closing_time = if self.overtaking_allowed {
                if self.get_closing_time(vehicle_pce).is_zero() {
                    // The bottleneck does not close.
                    self.status = EdgeExitStatus::Open;
                    None
                } else {
                    // Return the closing time of the bottleneck so that an event is created to
                    // re-open it.
                    Some(self.get_closing_time(vehicle_pce))
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
                vehicle_pce,
                entry_time: current_time,
            });
            None
        }
    }

    /// A vehicle has successfully exited the edge.
    ///
    /// Returns the closing time of the bottleneck.
    fn vehicle_exits(&mut self, vehicle_pce: PCE) -> Option<NonNegativeSeconds> {
        if self.overtaking_allowed {
            // The bottleneck was already closed for this vehicle when it crossed the bottleneck.
            None
        } else {
            debug_assert_eq!(self.status, EdgeExitStatus::Closed);
            self.status = EdgeExitStatus::Closed;
            Some(self.get_closing_time(vehicle_pce))
        }
    }

    /// The bottleneck re-opens.
    ///
    /// Returns the event to execute for the next vehicle in the queue (if any).
    ///
    /// Returns the closing time of the bottleneck, if it gets closed.
    fn open_bottleneck(
        &mut self,
        current_time: NonNegativeSeconds,
    ) -> Option<(VehicleEvent, Option<NonNegativeSeconds>)> {
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
    fn record(&mut self, entry_time: NonNegativeSeconds, exit_time: NonNegativeSeconds) {
        self.waiting_time_history.push(entry_time, exit_time);
    }

    /// Consumes the [EdgeExitState] and returns a [TTF] with the simulated waiting time.
    fn into_simulated_ttf(self) -> TTF<AnySeconds> {
        let mut ttf = self.waiting_time_history.finish();
        ttf.ensure_fifo();
        ttf
    }
}

/// Struct that holds data on the current state of a [RoadEdge].
#[derive(Clone, Debug)]
struct RoadEdgeState {
    // TODO: Can we allow multiple RoadSegment on the same edge (e.g., a segment every 200m)?
    /// [RoadSegment] representing the road part of the edge.
    road: RoadSegment,
    /// [EdgeEntryState] representing the state of the edge entry.
    /// Or `None` if the edge has infinite flow and spillback is disabled.
    entry: Option<EdgeEntryState>,
    // TODO: Make EdgeExitState optional when overtaking is allowed (and flow is infinite).
    /// [EdgeExitState] representing the state of the edge exit.
    /// Or `None` if the edge has infinite flow and spillback is disabled.
    exit: Option<EdgeExitState>,
    /// Reference to the corresponding [RoadEdge].
    reference: RoadEdge,
}

impl RoadEdgeState {
    /// Creates a new RoadEdgeState.
    fn new(reference: &RoadEdge) -> Self {
        let entry = EdgeEntryState::new(reference);
        let exit = EdgeExitState::new(reference);
        RoadEdgeState {
            road: RoadSegment::new(),
            entry,
            exit: Some(exit),
            reference: reference.clone(),
        }
    }

    /// A vehicle is reaching the edge entry.
    fn vehicle_reaches_entry(
        &mut self,
        current_time: NonNegativeSeconds,
        vehicle_pce: PCE,
        next_event: VehicleEvent,
    ) -> Option<Either<VehicleEvent, AgentIndex>> {
        if let Some(entry) = self.entry.as_mut() {
            entry.vehicle_reaches_entry(current_time, vehicle_pce, next_event)
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
        current_time: NonNegativeSeconds,
        vehicle_pce: PCE,
        next_event: VehicleEvent,
    ) -> Option<(VehicleEvent, Option<NonNegativeSeconds>)> {
        if let Some(exit) = self.exit.as_mut() {
            exit.vehicle_reaches_exit(current_time, vehicle_pce, next_event)
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
        vehicle: &'static Vehicle,
        current_time: NonNegativeSeconds,
        is_phantom: bool,
    ) -> (NonNegativeSeconds, NonNegativeSeconds) {
        // Notify the EdgeEntryState that a vehicle is entering and gets the closing time of the
        // bottleneck.
        let closing_time = self
            .entry
            .as_mut()
            .map(|entry| entry.vehicle_enters(vehicle.pce, vehicle.headway, is_phantom))
            .unwrap_or(NonNegativeSeconds::ZERO);
        let travel_time = self.enters_road_segment(vehicle, current_time);
        (travel_time, closing_time)
    }

    /// The entry bottleneck of the edge is re-opening.
    fn open_entry_bottleneck(
        &mut self,
        current_time: NonNegativeSeconds,
    ) -> Option<Either<VehicleEvent, AgentIndex>> {
        self.entry
            .as_mut()
            .and_then(|entry| entry.try_open_entry(current_time))
    }

    /// Forces the release of the next vehicle pending at the edge entry.
    fn force_release(&mut self, current_time: NonNegativeSeconds) -> VehicleEvent {
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
        current_time: NonNegativeSeconds,
    ) -> Option<(VehicleEvent, Option<NonNegativeSeconds>)> {
        self.exit
            .as_mut()
            .and_then(|exit| exit.open_bottleneck(current_time))
    }

    /// A vehicle can successfully exit the edge's exit bottleneck.
    ///
    /// Returns the closing time of the exit bottleneck of the edge (if it gets closed).
    fn vehicle_exits_bottleneck(&mut self, vehicle_pce: PCE) -> Option<NonNegativeSeconds> {
        self.exit
            .as_mut()
            .and_then(|exit| exit.vehicle_exits(vehicle_pce))
    }

    /// A vehicle has been fully released from the edge, i.e., the hole it generated when leaving
    /// has reached the beginning of the edge.
    fn vehicle_is_released(
        &mut self,
        current_time: NonNegativeSeconds,
        vehicle_headway: NonNegativeMeters,
        was_phantom: bool,
    ) -> Option<VehicleEvent> {
        let released_vehicle_event = if was_phantom {
            // The vehicle was a phantom so we do not increase the available length on the edge.
            None
        } else {
            // Try to release a vehicle at the entry of the edge.
            self.entry
                .as_mut()
                .and_then(|entry| entry.vehicle_exits(current_time, vehicle_headway))
        };
        // Remove the vehicle from the road segment.
        self.road.exits(vehicle_headway);
        released_vehicle_event
    }

    /// Records the entry of a new vehicle on the edge and returns the travel time of this vehicle
    /// up to the Bottleneck.
    fn enters_road_segment(
        &mut self,
        vehicle: &'static Vehicle,
        current_time: NonNegativeSeconds,
    ) -> NonNegativeSeconds {
        // The travel time needs to be computed before the vehicle enters so that it does not
        // generate its own congestion.
        // TODO
        let tt = self.get_travel_time(vehicle);
        self.road.enters(vehicle.headway, current_time);
        tt
    }

    fn get_travel_time(&self, vehicle: &'static Vehicle) -> NonNegativeSeconds {
        let vehicle_base_speed = vehicle.get_speed(self.reference.base_speed);
        let actual_speed = self.reference.speed_density.get_speed(
            vehicle_base_speed,
            self.road.occupied_length,
            self.reference.total_length(),
        );
        let variable_tt = self.reference.length() / actual_speed;
        variable_tt + self.reference.constant_travel_time
    }

    fn into_simulated_functions(self) -> SimulatedFunctions {
        SimulatedFunctions {
            entry: self
                .entry
                .map(|entry| entry.into_simulated_ttf())
                .unwrap_or(TTF::Constant(AnySeconds::ZERO)),
            exit: self
                .exit
                .map(|exit| exit.into_simulated_ttf())
                .unwrap_or(TTF::Constant(AnySeconds::ZERO)),
            road: self.road.into_simulated_length_function(),
        }
    }
}

/// Struct that represents the state of a [RoadNetwork] at a given time.
#[derive(Clone, Debug)]
pub(crate) struct RoadNetworkState {
    graph: DiGraph<RoadNodeState, RoadEdgeState>,
    /// Map to find the current edge of all pending agents.
    pending_edges: HashMap<AgentIndex, EdgeIndex>,
    /// Maximum amout of time a vehicle is allowed to be pending.
    max_pending_duration: NonNegativeSeconds,
    /// Speed at which the holes liberated by a vehicle leaving an edge is traveling backward.
    ///
    /// `None` if the holes propagate backward instantaneously.
    backward_wave_speed: Option<MetersPerSecond>,
    /// Record the number of warnings sent to the user.
    warnings: usize,
}

impl RoadNetworkState {
    /// Create an empty [RoadNetworkState].
    pub(crate) fn init() -> Self {
        let graph = super::graph().map(
            |_node_id, _n| RoadNodeState {},
            |_edge_id, e| RoadEdgeState::new(e),
        );
        RoadNetworkState {
            graph,
            pending_edges: HashMap::new(),
            max_pending_duration: super::parameters::max_pending_duration(),
            warnings: 0,
            backward_wave_speed: super::parameters::backward_wave_speed(),
        }
    }

    /// Return a [RoadNetworkWeights] (i.e., travel times) from the observations recorded in the
    /// [RoadNetworkState].
    pub(crate) fn into_weights(
        self,
        preprocess_data: &RoadNetworkPreprocessingData,
    ) -> RoadNetworkWeights {
        let mut weights = RoadNetworkWeights::with_capacity(
            &preprocess_data.unique_vehicles,
            self.graph.edge_count(),
        );
        let (_, edge_states) = self.graph.into_nodes_edges();
        let edge_simulated_functions: Vec<SimulatedFunctions> = edge_states
            .into_iter()
            .map(|e| e.weight.into_simulated_functions())
            .collect();
        for (uvehicle_id, vehicle) in preprocess_data
            .unique_vehicles
            .iter_uniques(super::vehicles())
        {
            let edge_refs_iter = super::graph().edge_references();
            let vehicle_weights = &mut weights[uvehicle_id];
            for (funcs, edge_ref) in edge_simulated_functions.iter().zip(edge_refs_iter) {
                if vehicle.can_access(edge_ref.weight().id) {
                    let road_ttf = match &funcs.road {
                        XYF::Piecewise(road_pwl_length) => {
                            let road_pwl_ttf =
                                road_pwl_length.map(|l| {
                                    // The uncheck is safe because we ensured that the occupied
                                    // length cannot be negative.
                                    AnySeconds::from(edge_ref.weight().get_travel_time(
                                        l.assume_non_negative_unchecked(),
                                        vehicle,
                                    ))
                                });
                            if road_pwl_ttf.is_practically_cst(AnySeconds::from(
                                super::parameters::approximation_bound(),
                            )) {
                                TTF::Constant(road_pwl_ttf.y_at_index(0))
                            } else {
                                let mut road_ttf = road_pwl_ttf.to_ttf();
                                road_ttf.ensure_fifo();
                                TTF::Piecewise(road_ttf)
                            }
                        }
                        XYF::Constant(l) => TTF::Constant(AnySeconds::from(
                            edge_ref
                                .weight()
                                .get_travel_time(l.assume_non_negative_unchecked(), vehicle),
                        )),
                    };
                    let mut ttf = funcs.entry.link(&road_ttf);
                    ttf.ensure_fifo();
                    ttf = ttf.link(&funcs.exit);
                    ttf.ensure_fifo();
                    vehicle_weights
                        .weights_mut()
                        .insert(edge_ref.weight().id, ttf);
                }
            }
            vehicle_weights.weights_mut().shrink_to_fit();
        }
        weights
    }

    /// Simulates the entry of a vehicle on an edge of the road network.
    ///
    /// Returns the next event to execute for this vehicle, if it can be executed immediately.
    /// Otherwise, returns `None` and the next event will be executed later.
    pub(crate) fn try_enter_edge(
        &mut self,
        edge_index: EdgeIndex,
        current_time: NonNegativeSeconds,
        vehicle: &'static Vehicle,
        next_event: VehicleEvent,
        event_queue: &mut EventQueue,
    ) -> Option<VehicleEvent> {
        let edge = &mut self.graph[edge_index];
        match edge.vehicle_reaches_entry(current_time, vehicle.pce, next_event) {
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
    pub(crate) fn try_exit_edge(
        &mut self,
        edge_index: EdgeIndex,
        current_time: NonNegativeSeconds,
        vehicle: &'static Vehicle,
        next_event: VehicleEvent,
        event_queue: &mut EventQueue,
    ) -> Option<VehicleEvent> {
        let edge = &mut self.graph[edge_index];
        if let Some((next_event, closing_time_opt)) =
            edge.vehicle_reaches_exit(current_time, vehicle.pce, next_event)
        {
            if let Some(closing_time) = closing_time_opt {
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
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn enters_edge<'sim: 'event, 'event>(
        &mut self,
        edge_index: EdgeIndex,
        from: Option<EdgeIndex>,
        current_time: NonNegativeSeconds,
        vehicle: &'static Vehicle,
        agent_id: AgentIndex,
        is_phantom: bool,
        was_phantom: bool,
        event_input: &'event mut EventInput<'sim>,
        event_alloc: &'event mut EventAlloc,
        event_queue: &'event mut EventQueue,
    ) -> Result<NonNegativeSeconds> {
        let edge_state = &mut self.graph[edge_index];
        // The agent is no longer pending.
        self.pending_edges.remove(&agent_id);
        let (travel_time, closing_time) = edge_state.enters(vehicle, current_time, is_phantom);
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
                was_phantom,
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
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn release_from_edge<'sim: 'event, 'event>(
        &mut self,
        edge_index: EdgeIndex,
        current_time: NonNegativeSeconds,
        vehicle: &'static Vehicle,
        was_phantom: bool,
        event_input: &'event mut EventInput<'sim>,
        event_alloc: &'event mut EventAlloc,
        event_queue: &'event mut EventQueue,
    ) -> Result<()> {
        let edge = &mut self.graph[edge_index];
        let edge_length = edge.reference.length;
        // Make the vehicle cross its previous edge's exit bottleneck.
        let closing_time_opt = edge.vehicle_exits_bottleneck(vehicle.pce);
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
                event_queue.push(Box::new(BottleneckEvent {
                    at_time: current_time + closing_time,
                    edge_index,
                    position: BottleneckPosition::Exit,
                }));
            }
        }
        let mut release_event = Box::new(ReleaseVehicleEvent {
            at_time: current_time,
            edge_index,
            vehicle_headway: vehicle.headway,
            was_phantom,
        });
        if let Some(speed) = self.backward_wave_speed {
            // Time delay after which the length liberated by the vehicle can be released from the
            // previous edge.
            let release_delay = edge_length / speed;
            debug_assert!(release_delay > NonNegativeSeconds::ZERO);
            release_event.at_time += release_delay;
            // Push an event to release the vehicle later.
            event_queue.push(release_event);
        } else {
            // The release event can be executed immediately.
            release_event.execute(event_input, self, event_alloc, event_queue)?;
        }
        Ok(())
    }
}

/// Event used to force the release of a vehicle pending to enter a link.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct ForceVehicleRelease {
    /// Time at which the vehicle must be released.
    at_time: NonNegativeSeconds,
    /// Id of the agent the vehicle belongs to.
    agent: AgentIndex,
    /// Id of the edge the vehicle is pending on.
    edge: EdgeIndex,
}

impl Event for ForceVehicleRelease {
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim>,
        road_network_state: &'event mut RoadNetworkState,
        alloc: &'event mut EventAlloc,
        events: &'event mut EventQueue,
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
    fn get_time(&self) -> NonNegativeSeconds {
        self.at_time
    }
}

/// Event representing a vehicle being fully released from an edge (after the backward wave
/// propagation elapsed).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct ReleaseVehicleEvent {
    /// Time at which the vehicle is released.
    at_time: NonNegativeSeconds,
    /// Id of the edge where the vehicle was located.
    edge_index: EdgeIndex,
    /// Length of the vehicle being released.
    vehicle_headway: NonNegativeMeters,
    /// `true` if the vehicle was a phantom, i.e., it did not take space on the edge for spillback
    /// (but it did for road-segment density).
    was_phantom: bool,
}

impl Event for ReleaseVehicleEvent {
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim>,
        road_network_state: &'event mut RoadNetworkState,
        alloc: &'event mut EventAlloc,
        events: &'event mut EventQueue,
    ) -> Result<bool> {
        let edge_state = &mut road_network_state.graph[self.edge_index];
        // Removes the vehicle from its previous edge and release any pending vehicle.
        let event_opt =
            edge_state.vehicle_is_released(self.at_time, self.vehicle_headway, self.was_phantom);
        if let Some(event) = event_opt {
            // Execute the event of the release vehicle.
            event.execute(input, road_network_state, alloc, events)?;
        }
        Ok(false)
    }
    fn get_time(&self) -> NonNegativeSeconds {
        self.at_time
    }
}

/// Event representing the opening of a Bottleneck.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct BottleneckEvent {
    /// Time at which the Bottleneck opens.
    at_time: NonNegativeSeconds,
    /// Id of the edge where the Bottleneck is located.
    edge_index: EdgeIndex,
    /// Position of the bottleneck (entry or exit of the edge).
    position: BottleneckPosition,
}

impl Event for BottleneckEvent {
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim>,
        road_network_state: &'event mut RoadNetworkState,
        alloc: &'event mut EventAlloc,
        events: &'event mut EventQueue,
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
                    let is_arrived = event.execute(input, road_network_state, alloc, events)?;
                    if let Some(closing_time) = closing_time_opt {
                        let bottleneck_event = Box::new(BottleneckEvent {
                            at_time: self.at_time + closing_time,
                            edge_index: self.edge_index,
                            position: self.position,
                        });
                        if closing_time.is_zero() {
                            // Execute immediately the bottleneck opening.
                            return Ok(bottleneck_event.execute(
                                input,
                                road_network_state,
                                alloc,
                                events,
                            )? || is_arrived);
                        } else {
                            // Push the bottleneck event to the queue.
                            events.push(bottleneck_event);
                            return Ok(is_arrived);
                        }
                    }
                }
            }
        }
        Ok(false)
    }
    fn get_time(&self) -> NonNegativeSeconds {
        self.at_time
    }
}

#[derive(Clone, Debug)]
struct WaitXYFBuilder {
    points: Vec<NonNegativeSeconds>,
    start_x: NonNegativeSeconds,
    end_x: NonNegativeSeconds,
    interval_x: PositiveSeconds,
    /// Middle of the current interval.
    threshold: NonNegativeSeconds,
    /// Total waiting time and weight for the previous interval.
    prev_interval: (NonNegativeSeconds, NonNegativeNum),
    /// Total waiting time and weight for the next interval.
    next_interval: (NonNegativeSeconds, NonNegativeNum),
}

impl WaitXYFBuilder {
    fn new() -> Self {
        let period = crate::parameters::period();
        let interval_x = super::parameters::recording_interval();
        let n = (period.length() / interval_x).to_usize_unchecked() + 1;
        WaitXYFBuilder {
            points: Vec::with_capacity(n),
            start_x: period.start(),
            end_x: period.end(),
            interval_x,
            threshold: (period.start() + interval_x).into(),
            prev_interval: (NonNegativeSeconds::ZERO, NonNegativeNum::ZERO),
            next_interval: (NonNegativeSeconds::ZERO, NonNegativeNum::ZERO),
        }
    }

    fn push(&mut self, entry_time: NonNegativeSeconds, exit_time: NonNegativeSeconds) {
        debug_assert!(entry_time >= self.start_x);
        if entry_time > self.end_x {
            // Skip.
            return;
        }
        if entry_time > self.threshold {
            self.finish_interval(entry_time);
        }
        self.add_record(entry_time, exit_time);
    }

    fn add_record(&mut self, entry_time: NonNegativeSeconds, exit_time: NonNegativeSeconds) {
        debug_assert!(entry_time <= self.threshold);
        debug_assert!(entry_time <= exit_time);
        let waiting_time = (exit_time - entry_time).assume_non_negative_unchecked();
        // The waiting time is distributed to the two closest intervals, proportionally to the
        // distance to the interval midpoint.
        let alpha = ((self.threshold - entry_time) / self.interval_x).assume_zero_one_unchecked();
        self.prev_interval.0 += waiting_time * alpha;
        self.prev_interval.1 += alpha;
        self.next_interval.0 += waiting_time * alpha.one_minus();
        self.next_interval.1 += alpha.one_minus();
    }

    fn finish_interval(&mut self, entry_time: NonNegativeSeconds) {
        debug_assert!(self.threshold < entry_time);
        let y = if self.prev_interval.1.is_zero() {
            // No entry at this interval.
            NonNegativeSeconds::ZERO
        } else {
            self.prev_interval.0 / self.prev_interval.1.assume_positive_unchecked()
        };
        self.points.push(y);
        self.prev_interval = self.next_interval;
        self.next_interval = (NonNegativeSeconds::ZERO, NonNegativeNum::ZERO);
        // Switch to next interval.
        self.threshold += self.interval_x;
        // Go recursive (multiple intervals can end at the same time).
        if entry_time > self.threshold {
            self.finish_interval(entry_time)
        }
    }

    fn finish(mut self) -> TTF<AnySeconds> {
        // Finish the last intervals.
        // We force the threshold to go to end_x + 2 * interval_x so that the last interval is
        // added (the prev interval is at this point end_x + interval_x and the next one is end_x +
        // 2 * interval_x).
        self.finish_interval((self.end_x + self.interval_x + self.interval_x).into());
        debug_assert_eq!(
            ((self.end_x - self.start_x) / self.interval_x).to_usize_unchecked() + 1,
            self.points.len()
        );
        if self.points.iter().all(|&y| y == self.points[0]) {
            // All `y` values are identical.
            XYF::Constant(AnySeconds::from(self.points[0]))
        } else {
            XYF::Piecewise(PwlXYF::from_values(
                self.points.into_iter().map(AnySeconds::from).collect(),
                AnySeconds::from(self.start_x),
                AnySeconds::from(self.interval_x),
            ))
        }
    }
}

#[derive(Clone, Debug)]
struct LengthXYFBuilder {
    points: Vec<NonNegativeMeters>,
    start_x: NonNegativeSeconds,
    end_x: NonNegativeSeconds,
    interval_x: PositiveSeconds,
    /// Middle of the current interval.
    threshold: NonNegativeSeconds,
    /// Total length and weight for the previous interval.
    prev_interval: (NonNegativeMeters, NonNegativeNum),
    /// Total length and weight for the next interval.
    next_interval: (NonNegativeMeters, NonNegativeNum),
}

impl LengthXYFBuilder {
    fn new() -> Self {
        let period = crate::parameters::period();
        let interval_x = super::parameters::recording_interval();
        let n = (period.length() / interval_x).to_usize_unchecked() + 1;
        LengthXYFBuilder {
            points: Vec::with_capacity(n),
            start_x: period.start(),
            end_x: period.end(),
            interval_x,
            threshold: (period.start() + interval_x).into(),
            prev_interval: (NonNegativeMeters::ZERO, NonNegativeNum::ZERO),
            next_interval: (NonNegativeMeters::ZERO, NonNegativeNum::ZERO),
        }
    }

    fn push(&mut self, entry_time: NonNegativeSeconds, length: NonNegativeMeters) {
        debug_assert!(entry_time >= self.start_x);
        if entry_time > self.end_x {
            // Skip.
            return;
        }
        if entry_time > self.threshold {
            self.finish_interval(entry_time);
        }
        self.add_record(entry_time, length);
    }

    fn add_record(&mut self, entry_time: NonNegativeSeconds, length: NonNegativeMeters) {
        debug_assert!(entry_time <= self.threshold);
        // The value is distributed to the two closest intervals, proportionally to the
        // distance to the interval midpoint.
        let alpha = ((self.threshold - entry_time) / self.interval_x).assume_zero_one_unchecked();
        self.prev_interval.0 += length * alpha;
        self.prev_interval.1 += alpha;
        self.next_interval.0 += length * alpha.one_minus();
        self.next_interval.1 += alpha.one_minus();
    }

    fn finish_interval(&mut self, entry_time: NonNegativeSeconds) {
        debug_assert!(self.threshold < entry_time);
        let y = if self.prev_interval.1.is_zero() {
            // No entry at this interval.
            NonNegativeMeters::ZERO
        } else {
            self.prev_interval.0 / self.prev_interval.1.assume_positive_unchecked()
        };
        self.points.push(y);
        self.prev_interval = self.next_interval;
        self.next_interval = (NonNegativeMeters::ZERO, NonNegativeNum::ZERO);
        // Switch to next interval.
        self.threshold += self.interval_x;
        // Go recursive (multiple intervals can end at the same time).
        if entry_time > self.threshold {
            self.finish_interval(entry_time)
        }
    }

    fn finish(mut self) -> XYF<AnySeconds, AnyMeters, AnyNum> {
        // Finish the last intervals.
        // We force the threshold to go to end_x + 2 * interval_x so that the last interval is
        // added (the prev interval is at this point end_x + interval_x and the next one is end_x +
        // 2 * interval_x).
        self.finish_interval((self.end_x + self.interval_x + self.interval_x).into());
        debug_assert_eq!(
            ((self.end_x - self.start_x) / self.interval_x).to_usize_unchecked() + 1,
            self.points.len()
        );
        if self.points.iter().all(|&y| y == self.points[0]) {
            // All `y` values are identical.
            XYF::Constant(AnyMeters::from(self.points[0]))
        } else {
            XYF::Piecewise(PwlXYF::from_values(
                self.points.into_iter().map(AnyMeters::from).collect(),
                AnySeconds::from(self.start_x),
                AnySeconds::from(self.interval_x),
            ))
        }
    }
}
