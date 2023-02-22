// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of [RoadNetworkState].
use std::collections::VecDeque;
use std::ops::{Index, IndexMut};

use anyhow::Result;
use num_traits::{Float, Zero};
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use ttf::{PwlTTFBuilder, PwlXYFBuilder, TTFNum, TTF, XYF};

use super::super::{Network, NetworkSkim, NetworkState};
use super::vehicle::Vehicle;
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetwork, RoadNetworkParameters, RoadNetworkPreprocessingData, RoadNode};
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
    fn new(period: Interval<T>, approximation: NoUnit<T>) -> Self {
        let mut length_history: PwlXYFBuilder<Time<T>, Length<T>, NoUnit<T>> =
            PwlXYFBuilder::with_approximation(period.0, approximation);
        length_history.push(period.start(), Length::zero());
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
        let pwl_xyf = self.length_history.finish();
        debug_assert_eq!(pwl_xyf.iter_y().last().unwrap(), &Length::zero());
        if pwl_xyf.iter_y().all(|y| y == &pwl_xyf[0].y) {
            XYF::Constant(pwl_xyf[0].y)
        } else {
            XYF::Piecewise(pwl_xyf)
        }
    }
}

/// Entry for a [BottleneckQueue].
///
/// It contains two values:
///
/// - The [VehicleEvent] associated with the vehicle waiting.
/// - The closing time induced by the vehicle waiting.
type BottleneckEntry<'a, T> = (Box<VehicleEvent<'a, T>>, Time<T>);

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
pub enum BottleneckStatus<'a, T> {
    /// The bottleneck is open.
    ///
    /// The vehicle associated to the given [VehicleEvent] can cross immediately.
    Open(Box<VehicleEvent<'a, T>>),
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
    /// Indicates the time at which the bottleneck is expected to open again.
    next_opening: Time<T>,
    /// Queue of vehicles currently waiting at the bottleneck.
    queue: BottleneckQueue<'a, T>,
    /// Waiting time PwlTTF function.
    waiting_time_history: PwlTTFBuilder<Time<T>>,
}

impl<'a, T> Bottleneck<'a, T> {
    /// Return the next [BottleneckEntry] in the [BottleneckQueue] of the Bottleneck.
    fn pop(&mut self) -> Option<BottleneckEntry<'a, T>> {
        self.queue.pop_front()
    }
}

impl<T: TTFNum> Bottleneck<'_, T> {
    fn new(
        effective_flow: Flow<T>,
        position: BottleneckPosition,
        period: Interval<T>,
        approximation: Time<T>,
    ) -> Self {
        let mut waiting_time_history = PwlTTFBuilder::with_approximation(period.0, approximation);
        waiting_time_history.push(period.start(), Time::zero());
        Bottleneck {
            effective_flow,
            position,
            next_opening: period.start(),
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
        let pwl_ttf = self.waiting_time_history.finish();
        debug_assert_eq!(pwl_ttf.iter_y().last().unwrap(), &Time::zero());
        if pwl_ttf.iter_y().all(|y| y == &pwl_ttf[0].y) {
            TTF::Constant(pwl_ttf[0].y)
        } else {
            TTF::Piecewise(pwl_ttf)
        }
    }
}

impl<'a, T: TTFNum> Bottleneck<'a, T> {
    /// Records the entry of a vehicle in the bottleneck.
    ///
    /// Returns the status of the bottleneck as a [BottleneckStatus].
    /// This is the status of the bottleneck just before the entry (i.e., if the bottleneck is open
    /// when the vehicle enters, the status of the bottleneck is `open`).
    fn enters(
        &mut self,
        event: Box<VehicleEvent<'a, T>>,
        vehicle: &'a Vehicle<T>,
        edge_index: EdgeIndex,
    ) -> BottleneckStatus<'a, T> {
        let current_time = event.get_time();
        let closing_time = self.get_closing_time(vehicle);
        let status = if self.next_opening <= current_time {
            debug_assert!(self.queue.is_empty());
            // The bottleneck is open: the vehicle can cross immediately.
            self.next_opening = current_time + closing_time;
            self.record(current_time, current_time);
            BottleneckStatus::Open(event)
        } else {
            // The bottleneck is closed.
            let bottleneck_event = if self.queue.is_empty() {
                // Create a BottleneckEvent to trigger the exit from the bottleneck at the correct
                // time.
                Some(BottleneckEvent::new(
                    self.next_opening,
                    edge_index,
                    self.position,
                ))
            } else {
                // A BottleneckEvent already exists.
                None
            };
            self.next_opening += closing_time;
            self.queue.push_back((event, closing_time));
            BottleneckStatus::Closed(bottleneck_event)
        };
        status
    }

    /// Records the entry and exit of a vehicle in the bottleneck at a given time.
    fn record(&mut self, entry_time: Time<T>, exit_time: Time<T>) {
        self.waiting_time_history
            .push(entry_time, exit_time - entry_time);
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
}

impl<'a, T: TTFNum> RoadEdgeState<'a, T> {
    /// Creates a new RoadEdgeState.
    pub fn new(
        reference: &'a RoadEdge<T>,
        edge_index: EdgeIndex,
        recording_period: Interval<T>,
        bottleneck_approximation: Time<T>,
        road_approximation: NoUnit<T>,
    ) -> Self {
        let effective_inflow = reference.get_effective_inflow();
        let in_bottleneck = if effective_inflow.is_infinite() {
            None
        } else {
            Some(Bottleneck::new(
                effective_inflow,
                BottleneckPosition::In,
                recording_period,
                bottleneck_approximation,
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
                bottleneck_approximation,
            ))
        };
        RoadEdgeState {
            reference,
            edge_index,
            road: RoadSegment::new(recording_period, road_approximation),
            in_bottleneck,
            out_bottleneck,
            total_length: Default::default(),
        }
    }

    /// Record the entry of a new vehicle on the edge and return the travel time of this vehicle up
    /// to the Bottleneck.
    pub fn enters_road(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) -> Time<T> {
        self.total_length += vehicle.get_headway();
        self.road.enters(vehicle, current_time);
        self.get_travel_time(vehicle)
    }

    /// Return the current travel time of the vehicle on the running part of the edge.
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
}

impl<'a, T: TTFNum> RoadEdgeState<'a, T> {
    /// Record the entry of a vehicle at the in-bottleneck of the edge.
    ///
    /// Return a [BottleneckStatus] that represents the state of the Bottleneck.
    pub fn enters_in_bottleneck(
        &mut self,
        vehicle: &'a Vehicle<T>,
        event: Box<VehicleEvent<'a, T>>,
    ) -> BottleneckStatus<'a, T> {
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
        event: Box<VehicleEvent<'a, T>>,
    ) -> BottleneckStatus<'a, T> {
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
    pub fn from_network(
        network: &'a RoadNetwork<T>,
        recording_period: Interval<T>,
        bottleneck_approximation: Time<T>,
        road_approximation: NoUnit<T>,
    ) -> Self {
        let graph = network.get_graph().map(
            |node_id, n| RoadNodeState::new(n, node_id),
            |edge_id, e| {
                RoadEdgeState::new(
                    e,
                    edge_id,
                    recording_period,
                    bottleneck_approximation,
                    road_approximation,
                )
            },
        );
        RoadNetworkState { graph, network }
    }

    /// Return a [RoadNetworkWeights] (i.e., travel times) from the observations recorded in the
    /// [RoadNetworkState].
    pub fn into_weights(
        self,
        preprocess_data: &RoadNetworkPreprocessingData<T>,
        parameters: &RoadNetworkParameters<T>,
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
        let edge_state = &mut road_network_state[self.edge];
        let bottleneck = match self.position {
            BottleneckPosition::In => edge_state.in_bottleneck.as_mut().unwrap(),
            BottleneckPosition::Out => edge_state.out_bottleneck.as_mut().unwrap(),
        };
        let (mut vehicle_event, closing_time) = bottleneck
            .pop()
            .expect("Cannot execute BottleneckEvent with empty queue");
        // Record the vehicle entry and exit.
        // (Vehicle entry time is the current timing of the vehicle event).
        bottleneck.record(vehicle_event.get_time(), self.at_time);
        // Trigger an event to make the vehicle exits.
        vehicle_event.set_time(self.at_time);
        events.push(vehicle_event);
        if bottleneck.queue.is_empty() {
            debug_assert_eq!(self.at_time, bottleneck.next_opening - closing_time);
            // Record that the bottleneck is now open.
            bottleneck.record(self.at_time, self.at_time);
        } else {
            // Trigger an event to open the bottleneck later.
            self.at_time += closing_time;
            events.push(self);
        }
        Ok(())
    }
    fn get_time(&self) -> Time<T> {
        self.at_time
    }
}
