// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Event trait and event priority queue.
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt::Debug;

use anyhow::Result;
use ttf::TTFNum;

use crate::agent::Agent;
use crate::network::road_network::skim::EAAllocation;
use crate::network::road_network::RoadNetworkState;
use crate::network::{Network, NetworkSkim};
use crate::progress_bar::MetroProgressBar;
use crate::simulation::results::AgentResults;
use crate::simulation::PreprocessingData;
use crate::units::Time;

/// Variables required to execute an event.
#[derive(Debug)]
pub struct EventInput<'a, T> {
    /// Reference to the [Agent] of the simulation.
    pub(crate) agents: &'a [Agent<T>],
    /// Reference to the [Network] of the simulation.
    pub(crate) network: &'a Network<T>,
    /// Reference to the [PreprocessingData] of the simulation.
    pub(crate) preprocess_data: &'a PreprocessingData<T>,
    /// Reference to the current [NetworkSkim] of the simulation.
    pub(crate) skims: &'a NetworkSkim<T>,
    /// Mutable reference to the [AgentResults] for the current iteration.
    pub(crate) agent_results: &'a mut AgentResults<T>,
    /// ProgressBar of the within-day model.
    pub(crate) progress_bar: MetroProgressBar,
}

/// Memory allocations that can be re-used when executing events.
#[derive(Clone, Debug, Default)]
pub struct EventAlloc<T: TTFNum> {
    pub(crate) ea_alloc: EAAllocation<T>,
}

/// Trait to represent an event (e.g., from an agent, a vehicle, a network infrastructure) that can
/// be executed.
pub trait Event<T: TTFNum>: Debug {
    /// Executes the event.
    ///
    /// Returns `true` if an agent reached his / her destination during the event execution.
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim, T>,
        road_network_state: &'event mut RoadNetworkState<T>,
        alloc: &'event mut EventAlloc<T>,
        events: &'event mut EventQueue<T>,
    ) -> Result<bool>;
    /// Returns the time at which the event occurs.
    fn get_time(&self) -> Time<T>;
}

/// An entry for the [EventQueue].
//
// The timing of the events could be retrieved with [Event::get_time].
// Instead, they are cached to speed-up the queue.
#[derive(Debug)]
pub struct EventEntry<T> {
    time: Time<T>,
    event: Box<dyn Event<T>>,
}

impl<T> PartialEq for EventEntry<T> {
    fn eq(&self, _other: &Self) -> bool {
        // There is never the same entry twice in the queue.
        false
    }
}

impl<T: TTFNum> Ord for EventEntry<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // We reverse the ordering so that events are pop in chronological order.
        self.time.cmp(&other.time).reverse()
    }
}

impl<T: TTFNum> PartialOrd for EventEntry<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Eq for EventEntry<T> {}

/// A priority queue represented as a [BinaryHeap].
///
/// The `EventQueue` is used to store events that are executed in chronological order.
#[derive(Debug)]
pub struct EventQueue<T>(BinaryHeap<EventEntry<T>>);

impl<T> EventQueue<T> {
    /// Returns `true` if the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of events in the queue.
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T: TTFNum> EventQueue<T> {
    /// Pops the next event in the queue, i.e., the event with the earliest execution time.
    pub fn pop(&mut self) -> Option<Box<dyn Event<T>>> {
        self.0.pop().map(|entry| entry.event)
    }

    /// Pushes a new event in the queue.
    pub fn push(&mut self, event: Box<dyn Event<T>>) {
        self.0.push(EventEntry {
            time: event.get_time(),
            event,
        });
    }
}

impl<T: TTFNum> Default for EventQueue<T> {
    fn default() -> Self {
        EventQueue(BinaryHeap::new())
    }
}

impl<T: TTFNum> FromIterator<Box<dyn Event<T>>> for EventQueue<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Box<dyn Event<T>>>,
    {
        EventQueue(
            iter.into_iter()
                .map(|event| EventEntry {
                    time: event.get_time(),
                    event,
                })
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct DummyEvent {
        time: Time<f64>,
    }

    impl Event<f64> for DummyEvent {
        fn execute<'sim: 'event, 'event>(
            self: Box<Self>,
            _input: &'event mut EventInput<'sim, f64>,
            _road_network_state: &'event mut RoadNetworkState<f64>,
            _alloc: &'event mut EventAlloc<f64>,
            _events: &'event mut EventQueue<f64>,
        ) -> Result<bool> {
            Ok(false)
        }
        fn get_time(&self) -> Time<f64> {
            self.time
        }
    }

    #[test]
    fn event_queue_test() {
        let mut q = EventQueue(BinaryHeap::new());
        assert!(q.is_empty());
        q.push(Box::new(DummyEvent { time: Time(2.) }));
        q.push(Box::new(DummyEvent { time: Time(1.) }));
        q.push(Box::new(DummyEvent { time: Time(4.) }));
        assert_eq!(q.len(), 3);
        assert_eq!(q.pop().unwrap().get_time(), Time(1.));
        assert_eq!(q.pop().unwrap().get_time(), Time(2.));
        q.push(Box::new(DummyEvent { time: Time(3.) }));
        assert_eq!(q.pop().unwrap().get_time(), Time(3.));
        assert_eq!(q.pop().unwrap().get_time(), Time(4.));
        assert!(q.is_empty());
    }
}
