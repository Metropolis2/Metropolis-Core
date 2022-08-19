//! Description of [RoadNetworkState].
use super::super::{Network, NetworkSkim, NetworkState};
use super::vehicle::Vehicle;
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetwork, RoadNode};
use crate::event::{Event, EventQueue};
use crate::mode::road::VehicleEvent;
use crate::simulation::results::AgentResult;
use crate::units::{Interval, Length, Outflow, Time};

use num_traits::{Float, Zero};
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::mem::MaybeUninit;
use std::ops::{Index, IndexMut};
use ttf::{PwlTTF, TTFNum, TTFSimplification, TTF};

/// Struct that holds data on the current state of a [RoadNode].
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct RoadNodeState<'a> {
    reference: &'a RoadNode,
    node_index: NodeIndex,
}

impl<'a> RoadNodeState<'a> {
    /// Creates a new RoadNodeState.
    pub fn new(reference: &'a RoadNode, node_index: NodeIndex) -> Self {
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
    /// Times at which a vehicle entered or exited the segment.
    timings: Vec<Time<T>>,
    /// Occupied length at each time a vehicle entered or exited the segment.
    history: Vec<Length<T>>,
}

impl<T: TTFNum> Default for RoadSegment<T> {
    fn default() -> Self {
        RoadSegment {
            occupied_length: Length::zero(),
            timings: Default::default(),
            history: Default::default(),
        }
    }
}

impl<T: TTFNum> RoadSegment<T> {
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
    /// Also record that a change of length occured at the given time.
    fn set_length(&mut self, length: Length<T>, time: Time<T>) {
        self.occupied_length = length;
        debug_assert!(self.timings.is_empty() || *self.last_timing().unwrap() <= time);
        if self
            .last_timing()
            .map(|t| t.approx_eq(&time))
            .unwrap_or(false)
        {
            // Last event occured at the same time, replace the new length instead of pushing a new
            // entry.
            *self.history.last_mut().unwrap() = length;
        } else {
            self.timings.push(time);
            self.history.push(length);
        }
    }

    /// Return the number of records, i.e., the number of times the length changed.
    fn len(&self) -> usize {
        self.timings.len()
    }

    /// Return the time at which the last change of occupied length occured.
    fn last_timing(&self) -> Option<&Time<T>> {
        self.timings.last()
    }

    /// Return an iterator of tuples `(l, t)`, where `t` is the time at which a change of length
    /// occured and `l` is the new occupied length after this time.
    ///
    /// The tuples are ordered by increasing `t`.
    fn iter(&self) -> impl Iterator<Item = (&Length<T>, &Time<T>)> {
        self.history.iter().zip(self.timings.iter())
    }

    /// Return the occupied length of the segment at the given time.
    ///
    /// **Panics** if `time` is not between the first and last timing.
    fn get_length_at(&self, time: Time<T>) -> Length<T> {
        let index = self.timings.binary_search(&time);
        match index {
            Ok(i) => self.history[i],
            Err(i) => self.history[i],
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
type BottleneckEntry<'a, T> = (Box<VehicleEvent<T>>, &'a Vehicle<T>, Time<T>);

/// Type representing a queue of vehicles waiting at a Bottleneck.
type BottleneckQueue<'a, T> = VecDeque<BottleneckEntry<'a, T>>;

/// Enum representing the status of a Bottleneck (open or closed).
///
/// If the bottleneck is open, the enum store the VehicleEvent associated to the vehicle that just
/// entered.
///
/// If the bottleneck is closed, the enum can store a [BottleneckEvent] that triggers the next time
/// it open.
#[derive(Clone, Debug, PartialEq)]
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

/// Struct representing the current state of the bottleneck queue of an edge.
#[derive(Clone, Debug)]
struct Bottleneck<'a, T> {
    /// Effective outflow of the bottleneck (i.e., bottleneck outflow of all the lanes of the
    /// edge).
    effective_outflow: Outflow<T>,
    /// Indicate if the bottleneck is open, i.e., vehicles can freely cross it.
    is_open: bool,
    /// Indicate the time at which the bottleneck is expected to open again.
    next_opening: Option<Time<T>>,
    /// Queue of vehicles currently waiting at the bottleneck.
    queue: BottleneckQueue<'a, T>,
    /// History of when vehicles crossed the bottleneck.
    entry_times: Vec<Time<T>>,
    /// History of when the bottleneck opened again after the vehicles which crossed it.
    opening_times: Vec<Time<T>>,
}

impl<'a, T> Bottleneck<'a, T> {
    fn new(effective_outflow: Outflow<T>) -> Self {
        Bottleneck {
            effective_outflow,
            is_open: true,
            next_opening: None,
            queue: Default::default(),
            entry_times: Default::default(),
            opening_times: Default::default(),
        }
    }

    /// Set the Bottleneck to open.
    fn open(&mut self) {
        self.is_open = true;
        self.next_opening = None;
    }

    /// Return the next [BottleneckEntry] in the [BottleneckQueue] of the Bottleneck.
    fn pop(&mut self) -> Option<BottleneckEntry<'a, T>> {
        self.queue.pop_front()
    }

    /// Iterator over values `(t, s)` where `t` is the time at which a vehicle entered the
    /// bottleneck and `s` is the time at which the bottleneck opened again after this vehicle left
    /// the bottleneck.
    ///
    /// The values are ordered by increasing `t` (and `s`).
    fn iter(&self) -> impl Iterator<Item = (&Time<T>, &Time<T>)> {
        self.entry_times.iter().zip(self.opening_times.iter())
    }
}

impl<T: TTFNum> Bottleneck<'_, T> {
    /// Return the time at which the bottleneck will open again, given the currently planned next
    /// opening and the vehicle which just entered.
    fn get_next_opening(&self, vehicle: &Vehicle<T>, opening_time: Time<T>) -> Time<T> {
        opening_time + vehicle.get_pce() / self.effective_outflow
    }

    /// Close the bottleneck and set the time of the next opening.
    fn set_next_opening(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) {
        self.is_open = false;
        self.next_opening = Some(self.get_next_opening(vehicle, current_time));
    }

    /// Record a new bottleneck event (the entry and exit of a vehicle at the Bottleneck).
    ///
    /// What is recorded is:
    ///
    /// - The entry time of the vehicle.
    ///
    /// - The time at which the bottleneck opened again after the vehicle left it, i.e., the time
    /// at which another vehicle could cross the bottleneck if it were to arrive after.
    fn record(&mut self, entry_time: Time<T>, opening_time: Time<T>) {
        debug_assert!(
            self.opening_times.is_empty() || opening_time >= *self.opening_times.last().unwrap()
        );
        if self
            .entry_times
            .last()
            .map(|t| t.approx_eq(&entry_time))
            .unwrap_or(false)
        {
            // Two records with the same entry time, we keep only the last one.
            *self.opening_times.last_mut().unwrap() = opening_time;
        } else {
            self.entry_times.push(entry_time);
            self.opening_times.push(opening_time);
        }
    }

    /// Return the waiting time of a vehicle in the Bottleneck if it were to arrive at the
    /// bottleneck at the given time.
    ///
    /// The waiting time is computed using the recorded entry and opening times.
    /// If there is a recorded vehicle with the exact same entry time, the function returns the
    /// waiting time of this vehicle that arrived at the same time.
    fn get_waiting_time_at(&self, entry_time: Time<T>) -> Time<T> {
        let i = self.entry_times.binary_search(&entry_time).into_ok_or_err();
        if i == 0 {
            // The entry time is such that `entry_time <= t_0`, i.e., the vehicle arrive before any
            // other vehicle.
            return Time::zero();
        }

        // The entry time is such that `t_{i-1} < entry_time <= t_i`.
        // The exit time is `max(entry_time, s_{i-1})`, where `s_{i-1}` is the opening time of the
        // bottleneck after the vehicle just before.
        if self.opening_times[i - 1] > entry_time {
            // The bottleneck was still close because of the previous vehicle, the exit
            // time is when the bottleneck opened after the previous vehicle.
            self.opening_times[i - 1] - entry_time
        } else {
            // The bottleneck was open.
            Time::zero()
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
        if self.is_open {
            // The bottleneck is open, the vehicle can cross immediately.
            self.set_next_opening(vehicle, current_time);
            return BottleneckStatus::Open(event);
        }
        if let Some(opening_time) = self.next_opening {
            if opening_time <= current_time {
                // The bottleneck was closed but it is now open.
                self.set_next_opening(vehicle, current_time);
                return BottleneckStatus::Open(event);
            } else {
                // The bottleneck is closed and there is no BottleneckEvent in the event queue yet.
                let next_opening = self.next_opening.take().unwrap();
                self.queue.push_back((event, vehicle, current_time));
                return BottleneckStatus::Closed(Some(BottleneckEvent::new(
                    next_opening,
                    edge_index,
                )));
            }
        }
        // The bottleneck is closed, there is a BottleneckEvent in the event queue that will
        // trigger the next time it opens.
        self.queue.push_back((event, vehicle, current_time));
        BottleneckStatus::Closed(None)
    }
}

/// Struct that holds data on the current state of a [RoadEdge].
#[derive(Clone, Debug)]
pub struct RoadEdgeState<'a, T> {
    reference: &'a RoadEdge<T>,
    edge_index: EdgeIndex,
    // TODO: Can we allow multiple RoadSegment on the same edge (e.g., a segment every 200m)?
    road: RoadSegment<T>,
    /// Bottleneck representing the state of the edge's bottleneck, or `None` if the edge has no
    /// bottleneck (outflow is infinite).
    bottleneck: Option<Bottleneck<'a, T>>,
    /// Total length of vehicles which entered the road edge since the beginning of the period.
    total_length: Length<T>,
}

impl<'a, T: TTFNum> RoadEdgeState<'a, T> {
    /// Creates a new RoadEdgeState.
    pub fn new(reference: &'a RoadEdge<T>, edge_index: EdgeIndex) -> Self {
        let effective_outflow = reference.get_effective_outflow();
        let bottleneck = if effective_outflow.is_infinite() {
            None
        } else {
            Some(Bottleneck::new(effective_outflow))
        };
        RoadEdgeState {
            reference,
            edge_index,
            road: Default::default(),
            bottleneck,
            total_length: Default::default(),
        }
    }

    /// Record the entry of a new vehicle on the edge and return the travel time of this vehicle up
    /// to the Bottleneck.
    pub fn enters_edge(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) -> Time<T> {
        self.total_length = self.total_length + vehicle.get_length();
        self.road.enters(vehicle, current_time);
        self.get_travel_time(vehicle)
    }

    /// Return the current travel time of the vehicle on the running part of the edge.
    fn get_travel_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.reference
            .get_travel_time(self.road.occupied_length, vehicle)
    }

    /// Return the observed travel-time function on this edge for the day simulated.
    ///
    /// The travel-time function is specific to a [Vehicle] and computed for a given time interval.
    ///
    /// The travel-time function is composed of:
    ///
    /// - The travel time on the running part of the edge, which depends on the occupied length on
    /// the segment at any time breakpoints.
    ///
    /// - The waiting time at the bottleneck that the vehicle would face at each arrival time
    /// breakpoints.
    fn get_travel_time_function(&self, vehicle: &Vehicle<T>, period: Interval<T>) -> TTF<Time<T>> {
        let mut departure_times = Vec::with_capacity(self.road.len() + 2);
        let mut travel_times = Vec::with_capacity(self.road.len() + 2);
        let mut length_iter = self
            .road
            .iter()
            .take_while(|(_, &dt)| dt <= period.end())
            .peekable();
        assert!(length_iter
            .peek()
            .map(|(_, &dt)| dt >= period.start())
            .unwrap_or(true));
        let (mut bottleneck_iter, has_bottleneck) = if let Some(bottleneck) = &self.bottleneck {
            (MaybeUninit::new(bottleneck.iter().peekable()), true)
        } else {
            (MaybeUninit::uninit(), false)
        };
        let mut last_ta_opt = None;
        let ff_tt = self.reference.get_free_flow_travel_time(vehicle);
        let mut is_constant = true;
        // Adjust first departure time to match simulation period's start.
        if length_iter.peek().map(|(_, &dt)| dt == period.start()) != Some(true) {
            departure_times.push(period.start());
            travel_times.push(ff_tt);
            last_ta_opt = Some(period.start() + ff_tt);
        }
        while let Some((&length, &dt)) = length_iter.next() {
            let on_road_tt = self.reference.get_travel_time(length, vehicle);
            let waiting_time = if let Some(bottleneck) = &self.bottleneck {
                bottleneck.get_waiting_time_at(dt + on_road_tt)
            } else {
                Time::zero()
            };
            let mut tt = on_road_tt + waiting_time;
            if let Some(last_ta) = last_ta_opt {
                // Fix travel time so that FIFO is respected.
                if last_ta > dt + tt {
                    tt = last_ta - dt + Time::small_margin();
                }
            }
            if tt.approx_ne(&ff_tt) {
                is_constant = false;
            }
            debug_assert!(departure_times.is_empty() || *departure_times.last().unwrap() < dt);
            debug_assert!(last_ta_opt.is_none() || last_ta_opt.unwrap() <= dt + tt);
            departure_times.push(dt);
            travel_times.push(tt);
            last_ta_opt = Some(dt + tt);
            let next_dt = if let Some((_, &next_dt)) = length_iter.peek() {
                next_dt
            } else {
                period.end()
            };
            if has_bottleneck {
                while let Some((&entry_time, &opening_time)) =
                    unsafe { bottleneck_iter.assume_init_mut().peek() }
                {
                    let edge_entry_time = entry_time - on_road_tt;
                    if edge_entry_time <= dt {
                        unsafe { bottleneck_iter.assume_init_mut().next() };
                        continue;
                    } else if edge_entry_time >= next_dt {
                        break;
                    }
                    unsafe { bottleneck_iter.assume_init_mut().next() };
                    let mut tt = opening_time - edge_entry_time;
                    if let Some(last_ta) = last_ta_opt {
                        // Fix travel time so that FIFO is respected.
                        if last_ta > edge_entry_time + tt {
                            tt = last_ta - edge_entry_time + Time::small_margin();
                        }
                    }
                    debug_assert!(edge_entry_time > *departure_times.last().unwrap());
                    if tt.approx_ne(&ff_tt) {
                        is_constant = false;
                    }
                    debug_assert!(last_ta_opt.unwrap() <= edge_entry_time + tt);
                    departure_times.push(edge_entry_time);
                    travel_times.push(tt);
                    last_ta_opt = Some(edge_entry_time + tt);
                }
            }
        }
        if has_bottleneck {
            unsafe {
                bottleneck_iter.assume_init_drop();
            }
        }
        // Adjust last departure time to match simulation period's end.
        if departure_times.last() != Some(&period.end()) {
            let on_road_tt = if self.road.last_timing() > Some(&period.end()) {
                let length = self.road.get_length_at(period.end());
                self.reference.get_travel_time(length, vehicle)
            } else {
                ff_tt
            };
            let waiting_time = if let Some(bottleneck) = &self.bottleneck {
                bottleneck.get_waiting_time_at(period.end() + on_road_tt)
            } else {
                Time::zero()
            };
            let mut tt = on_road_tt + waiting_time;
            // Fix travel time so that FIFO is respected.
            if last_ta_opt.unwrap() > period.end() + tt {
                tt = last_ta_opt.unwrap() - period.end() + Time::small_margin();
            }
            if tt.approx_ne(&ff_tt) {
                is_constant = false;
            }
            debug_assert!(*departure_times.last().unwrap() < period.end());
            debug_assert!(last_ta_opt.unwrap() <= period.end() + tt);
            departure_times.push(period.end());
            travel_times.push(tt);
        }
        if is_constant {
            TTF::Constant(ff_tt)
        } else {
            let mut ttf = PwlTTF::from_x_and_y(departure_times, travel_times);
            ttf.ensure_fifo();
            TTF::Piecewise(ttf)
        }
    }

    #[allow(dead_code)]
    fn get_flows(&self, breakpoints: &[Time<T>]) {
        let mut in_flows = vec![Length::zero(); breakpoints.len() - 1];
        let mut out_flows = vec![Length::zero(); breakpoints.len() - 1];
        let mut road_iter = self
            .road
            .iter()
            .zip(self.road.iter().skip(1))
            .skip_while(|((_, &t), _)| t < breakpoints[0])
            .peekable();
        for (i, &bp) in breakpoints[1..].iter().enumerate() {
            while let Some(&((&prev_length, _), (&next_length, &t))) = road_iter.peek() {
                if t > bp {
                    break;
                }
                match prev_length.cmp(&next_length) {
                    Ordering::Less => {
                        in_flows[i] = in_flows[i] + next_length - prev_length;
                    }
                    Ordering::Greater => {
                        out_flows[i] = out_flows[i] + prev_length - next_length;
                    }
                    _ => (),
                }
                road_iter.next();
            }
        }
    }
}

impl<'a, T: TTFNum + 'static> RoadEdgeState<'a, T> {
    /// Record the entry of a vehicle at the bottleneck of the edge (and thus the exit of this same
    /// vehicle from the running part).
    ///
    /// Return a [BottleneckStatus] that represents the state of the Bottleneck.
    pub fn enters_bottleneck(
        &mut self,
        vehicle: &'a Vehicle<T>,
        event: Box<VehicleEvent<T>>,
    ) -> BottleneckStatus<T> {
        // Remove the vehicle from the road part of the edge.
        self.road.exits(vehicle, event.get_time());
        if let Some(bottleneck) = &mut self.bottleneck {
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
    pub fn from_network(network: &'a RoadNetwork<T>) -> Self {
        let graph = network.get_graph().map(
            |node_id, n| RoadNodeState::new(n, node_id),
            |edge_id, e| RoadEdgeState::new(e, edge_id),
        );
        RoadNetworkState { graph, network }
    }

    /// Return a [RoadNetworkWeights] (i.e., travel times) from the observations recorded in the
    /// [RoadNetworkState].
    ///
    /// The travel times are only stored for the given time interval and are simplified using the
    /// given [TTFSimplification] method.
    pub fn get_weights(
        &self,
        period: Interval<T>,
        simplification: TTFSimplification<Time<T>>,
    ) -> RoadNetworkWeights<T> {
        let mut weights =
            RoadNetworkWeights::with_capacity(self.network.vehicles.len(), self.graph.edge_count());
        for (vehicle_id, vehicle) in self.network.iter_vehicles() {
            let vehicle_weights = &mut weights[vehicle_id];
            for edge_state in self.graph.edge_references() {
                let mut ttf = edge_state
                    .weight()
                    .get_travel_time_function(vehicle, period);
                simplification.simplify(&mut ttf);
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
}

impl<T> BottleneckEvent<T> {
    /// Creates a new BottleneckEvent.
    pub fn new(at_time: Time<T>, edge: EdgeIndex) -> Self {
        BottleneckEvent { at_time, edge }
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
        let bottleneck = road_network_state[self.edge].bottleneck.as_mut().unwrap();
        if let Some((mut vehicle_event, vehicle, entry_time)) = bottleneck.pop() {
            // Trigger an event to make the vehicle exits.
            vehicle_event.set_time(self.at_time);
            events.push(vehicle_event);
            // Record the next opening time of the vehicle.
            let opening_time = self.at_time + vehicle.get_pce() / bottleneck.effective_outflow;
            bottleneck.record(entry_time, opening_time);
            // Trigger an event to open the bottleneck later.
            self.at_time = opening_time;
            events.push(self);
        } else {
            // The bottleneck is now open.
            bottleneck.open();
            // Record that, at the current time, waiting time is null.
            bottleneck.record(self.at_time, self.at_time);
        }
    }
    fn get_time(&self) -> Time<T> {
        self.at_time
    }
}
