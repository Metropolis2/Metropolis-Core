use super::super::{NetworkSkim, NetworkState};
use super::vehicle::{Vehicle, VehicleIndex};
use super::weights::RoadNetworkWeights;
use super::{RoadEdge, RoadNetwork, RoadNode};
use crate::event::{Event, EventQueue};
use crate::mode::car::VehicleEvent;
use crate::simulation::AgentResult;
use crate::units::{Interval, Length, Time};

use log::warn;
use num_traits::{ToPrimitive, Zero};
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use serde_derive::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::iter;
use std::ops::{Index, IndexMut};
use ttf::{PwlTTF, TTFNum, TTF};

const NB_BREAKPOINTS_WARNING: usize = 10000;

#[allow(dead_code)]
pub struct RoadNodeState<'a> {
    reference: &'a RoadNode,
    node_index: NodeIndex,
}

impl<'a> RoadNodeState<'a> {
    pub fn new(reference: &'a RoadNode, node_index: NodeIndex) -> Self {
        RoadNodeState {
            reference,
            node_index,
        }
    }
}

struct RoadSegment<T> {
    current_length: Length<T>,
    timings: Vec<Time<T>>,
    history: Vec<Length<T>>,
}

impl<T: TTFNum> Default for RoadSegment<T> {
    fn default() -> Self {
        RoadSegment {
            current_length: Length::default(),
            timings: Default::default(),
            history: Default::default(),
        }
    }
}

impl<T: TTFNum> RoadSegment<T> {
    fn set_length(&mut self, length: Length<T>, time: Time<T>) {
        self.current_length = length;
        if self.timings.last() == Some(&time) {
            // Last event occured at the same time, replace the new length instead of pushing a new
            // entry.
            *self.history.last_mut().unwrap() = length;
        } else {
            self.timings.push(time);
            self.history.push(length);
        }
    }

    fn len(&self) -> usize {
        self.timings.len()
    }

    fn last_timing(&self) -> Option<&Time<T>> {
        self.timings.last()
    }

    fn iter(&self) -> impl iter::Iterator<Item = (&Length<T>, &Time<T>)> {
        self.history.iter().zip(self.timings.iter())
    }

    fn get_length_at(&self, time: Time<T>) -> Length<T> {
        // Panic if time is not between the first and last timing.
        let index = self.timings.binary_search(&time);
        match index {
            Ok(i) => self.history[i],
            Err(i) => self.history[i],
        }
    }
}

type BottleneckEntry<'a, T> = (Box<VehicleEvent<T>>, &'a Vehicle<T>, Time<T>);
type BottleneckQueue<'a, T> = VecDeque<BottleneckEntry<'a, T>>;

struct Bottleneck<'a, T> {
    is_open: bool,
    queue: BottleneckQueue<'a, T>,
    // History of when vehicles entered the bottleneck.
    entry_times: Vec<Time<T>>,
    // History of when the bottleneck opened again after the vehicles who entered.
    opening_times: Vec<Time<T>>,
}

impl<'a, T> Default for Bottleneck<'a, T> {
    fn default() -> Self {
        Bottleneck {
            is_open: true,
            queue: Default::default(),
            entry_times: Default::default(),
            opening_times: Default::default(),
        }
    }
}

impl<'a, T> Bottleneck<'a, T> {
    fn is_open(&self) -> bool {
        self.is_open
    }

    fn open(&mut self) {
        self.is_open = true;
    }

    fn close(&mut self) {
        self.is_open = false;
    }

    fn pop(&mut self) -> Option<BottleneckEntry<'a, T>> {
        self.queue.pop_front()
    }

    fn iter(&self) -> impl iter::Iterator<Item = (&Time<T>, &Time<T>)> {
        self.entry_times.iter().zip(self.opening_times.iter())
    }
}

impl<'a, T: TTFNum + 'static> Bottleneck<'a, T> {
    fn push(
        &mut self,
        event: Box<VehicleEvent<T>>,
        vehicle: &'a Vehicle<T>,
        time: Time<T>,
        edge_index: EdgeIndex,
    ) -> Option<Box<dyn Event<T>>> {
        self.queue.push_back((event, vehicle, time));
        if self.is_open() {
            // Trigger an event immediately to make the vehicle cross.
            self.close();
            let bottleneck_event = BottleneckEvent::new(time, edge_index);
            Some(Box::new(bottleneck_event))
        } else {
            None
        }
    }
}

impl<'a, T: TTFNum> Bottleneck<'a, T> {
    fn record(&mut self, entry_time: Time<T>, opening_time: Time<T>) {
        debug_assert!(
            self.opening_times.is_empty() || opening_time >= *self.opening_times.last().unwrap()
        );
        if self.entry_times.last() == Some(&entry_time) {
            // Two records with the same entry time, we keep only the last one.
            *self.opening_times.last_mut().unwrap() = opening_time;
        } else {
            self.entry_times.push(entry_time);
            self.opening_times.push(opening_time);
        }
    }

    fn get_waiting_time_at(&self, entry_time: Time<T>) -> Time<T> {
        // Panic if time is not between the first and last timing.
        let index = self.entry_times.binary_search(&entry_time);
        match index {
            Ok(i) => {
                if i == 0 {
                    // The entry time is before any recorded entry.
                    return Time::zero();
                }
                // There is a record with this exact entry time.
                // TODO: What if there are multiple records with this entry time?
                if i > 0 && self.opening_times[i - 1] > entry_time {
                    // The bottleneck was still close because of the previous vehicle, the exit
                    // time is when the bottleneck opened after the previous vehicle.
                    self.opening_times[i - 1] - entry_time
                } else {
                    // The bottleneck was open.
                    Time::zero()
                }
            }
            Err(i) => {
                if i == 0 {
                    // The entry time is before any recorded entry.
                    return Time::zero();
                }
                // The entry time is in-between record i - 1 and record i.
                if i > 0 && self.opening_times[i - 1] > entry_time {
                    // The bottleneck was still close because of the previous vehicle, the exit
                    // time is when the bottleneck opened after the previous vehicle.
                    self.opening_times[i - 1] - entry_time
                } else {
                    // The bottleneck was open.
                    Time::zero()
                }
            }
        }
    }
}

pub struct RoadEdgeState<'a, T> {
    reference: &'a RoadEdge<T>,
    edge_index: EdgeIndex,
    // TODO: Can we allow multiple RoadSegment on the same edge (e.g., a segment every 200m)?
    road: RoadSegment<T>,
    bottleneck: Bottleneck<'a, T>,
    /// Total length of vehicles which entered the road edge since the beginning of the period.
    total_length: Length<T>,
}

impl<'a, T: TTFNum> RoadEdgeState<'a, T> {
    pub fn new(reference: &'a RoadEdge<T>, edge_index: EdgeIndex) -> Self {
        RoadEdgeState {
            reference,
            edge_index,
            road: Default::default(),
            bottleneck: Default::default(),
            total_length: Default::default(),
        }
    }

    fn current_length(&self) -> Length<T> {
        self.road.current_length
    }

    pub fn total_length(&self) -> Length<T> {
        self.total_length
    }

    pub fn enters_edge(&mut self, vehicle: &Vehicle<T>, current_time: Time<T>) -> Option<Time<T>> {
        let new_length = self.current_length() + vehicle.get_length();
        self.road.set_length(new_length, current_time);
        self.total_length = self.total_length + vehicle.get_length();
        Some(self.get_travel_time(vehicle))
    }

    fn get_travel_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.reference
            .get_travel_time(self.current_length(), vehicle)
    }

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
        let mut bottleneck_iter = self.bottleneck.iter().peekable();
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
            let waiting_time = self.bottleneck.get_waiting_time_at(dt + on_road_tt);
            let mut tt = on_road_tt + waiting_time;
            if let Some(last_ta) = last_ta_opt {
                // Fix travel time so that FIFO is respected.
                if last_ta > dt + tt {
                    tt = last_ta - dt;
                }
            }
            if tt.approx_ne(&ff_tt) {
                is_constant = false;
            }
            assert!(departure_times.is_empty() || *departure_times.last().unwrap() < dt);
            assert!(last_ta_opt.is_none() || last_ta_opt.unwrap() <= dt + tt);
            departure_times.push(dt);
            travel_times.push(tt);
            last_ta_opt = Some(dt + tt);
            let next_dt = if let Some((_, &next_dt)) = length_iter.peek() {
                next_dt
            } else {
                period.end()
            };
            while let Some((&entry_time, &opening_time)) = bottleneck_iter.peek() {
                let edge_entry_time = entry_time - on_road_tt;
                if edge_entry_time <= dt {
                    bottleneck_iter.next();
                    continue;
                } else if edge_entry_time >= next_dt {
                    break;
                }
                bottleneck_iter.next();
                let mut tt = opening_time - edge_entry_time;
                if let Some(last_ta) = last_ta_opt {
                    // Fix travel time so that FIFO is respected.
                    if last_ta > edge_entry_time + tt {
                        tt = last_ta - edge_entry_time;
                    }
                }
                assert!(edge_entry_time > *departure_times.last().unwrap());
                if tt.approx_ne(&ff_tt) {
                    is_constant = false;
                }
                assert!(last_ta_opt.unwrap() <= edge_entry_time + tt);
                departure_times.push(edge_entry_time);
                travel_times.push(tt);
                last_ta_opt = Some(edge_entry_time + tt);
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
            let waiting_time = self
                .bottleneck
                .get_waiting_time_at(period.end() + on_road_tt);
            let mut tt = on_road_tt + waiting_time;
            // Fix travel time so that FIFO is respected.
            if last_ta_opt.unwrap() > period.end() + tt {
                tt = last_ta_opt.unwrap() - period.end();
            }
            if tt.approx_ne(&ff_tt) {
                is_constant = false;
            }
            assert!(*departure_times.last().unwrap() < period.end());
            assert!(last_ta_opt.unwrap() <= period.end() + tt);
            departure_times.push(period.end());
            travel_times.push(tt);
        }
        if is_constant {
            TTF::Constant(ff_tt)
        } else {
            TTF::Piecewise(PwlTTF::from_x_and_y(departure_times, travel_times, true))
        }
    }

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
    pub fn enters_bottleneck(
        &mut self,
        vehicle: &'a Vehicle<T>,
        current_time: Time<T>,
        event: Box<VehicleEvent<T>>,
    ) -> Option<Box<dyn Event<T>>> {
        // Remove the vehicle from the road part of the edge.
        let new_length = self.current_length() - vehicle.get_length();
        self.road.set_length(new_length, current_time);
        self.bottleneck
            .push(event, vehicle, current_time, self.edge_index)
    }
}

pub struct RoadNetworkState<'a, T> {
    graph: DiGraph<RoadNodeState<'a>, RoadEdgeState<'a, T>>,
    network: &'a RoadNetwork<T>,
}

impl<'a, T: TTFNum> RoadNetworkState<'a, T> {
    pub fn from_network(network: &'a RoadNetwork<T>) -> Self {
        let graph = network.get_graph().map(
            |node_id, n| RoadNodeState::new(n, node_id),
            |edge_id, e| RoadEdgeState::new(e, edge_id),
        );
        RoadNetworkState { graph, network }
    }

    pub fn get_target(&self, edge: EdgeIndex) -> Option<NodeIndex> {
        self.network.get_endpoints(edge).map(|(_, target)| target)
    }

    pub fn get_vehicle(&self, vehicle: VehicleIndex) -> &'a Vehicle<T> {
        &self.network[vehicle]
    }

    pub fn get_weights(
        &self,
        period: Interval<T>,
        simplification: WeightSimplification<T>,
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
                if ttf.complexity() > NB_BREAKPOINTS_WARNING {
                    warn!("The TTF for edge has {} breakpoints", ttf.complexity());
                }
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

impl<'a, T> IndexMut<NodeIndex> for RoadNetworkState<'a, T> {
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

impl<'a, T> IndexMut<EdgeIndex> for RoadNetworkState<'a, T> {
    fn index_mut(&mut self, index: EdgeIndex) -> &mut Self::Output {
        &mut self.graph[index]
    }
}

#[derive(Copy, Clone, Debug, Deserialize, Serialize)]
pub enum WeightSimplification<T> {
    Raw,
    Bound(Time<T>),
    Interval(Time<T>),
}

impl<T> Default for WeightSimplification<T> {
    fn default() -> Self {
        WeightSimplification::Raw
    }
}

impl<T: TTFNum> WeightSimplification<T> {
    fn simplify(self, ttf: &mut TTF<Time<T>>) {
        match self {
            Self::Raw => (),
            Self::Bound(bound) => ttf.approximate(bound),
            Self::Interval(interval) => {
                if let TTF::Piecewise(ref mut pwl_ttf) = ttf {
                    let &[start, end] = pwl_ttf.period();
                    let mut breakpoints =
                        Vec::with_capacity(((end - start) / interval).to_usize().unwrap() + 2);
                    let mut current_time = start;
                    loop {
                        breakpoints.push((current_time, pwl_ttf.eval(current_time)));
                        current_time = current_time + interval;
                        if current_time.approx_ge(&end) {
                            break;
                        }
                    }
                    breakpoints.push((end, pwl_ttf.eval(end)));
                    *pwl_ttf = PwlTTF::from_breakpoints(breakpoints, true);
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct BottleneckEvent<T> {
    at_time: Time<T>,
    edge: EdgeIndex,
}

impl<T> BottleneckEvent<T> {
    pub fn new(at_time: Time<T>, edge: EdgeIndex) -> Self {
        BottleneckEvent { at_time, edge }
    }
}

impl<T: TTFNum + 'static> Event<T> for BottleneckEvent<T> {
    fn execute(
        mut self: Box<Self>,
        _exp_skims: &NetworkSkim<T>,
        state: &mut NetworkState<T>,
        _result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<T>,
    ) -> bool {
        let road_network_state = state.get_mut_road_network().unwrap();
        let edge_state = &mut road_network_state[self.edge];
        if let Some((mut vehicle_event, vehicle, entry_time)) = edge_state.bottleneck.pop() {
            // Trigger an event to make the vehicle exits.
            vehicle_event.set_time(self.at_time);
            events.push(vehicle_event);
            // Record the next opening time of the vehicle.
            let opening_time = self.at_time
                + vehicle.get_length()
                    / (edge_state.reference.bottleneck_outflow * edge_state.reference.lanes);
            edge_state.bottleneck.record(entry_time, opening_time);
            // Trigger an event to open the bottleneck later.
            self.at_time = opening_time;
            events.push(self);
        } else {
            // The bottleneck is now open.
            edge_state.bottleneck.open();
            // Record that, at the current time, waiting time is null.
            edge_state.bottleneck.record(self.at_time, self.at_time);
        }
        false
    }
    fn get_time(&self) -> Time<T> {
        self.at_time
    }
}
