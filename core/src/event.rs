// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Event trait and event priority queue.
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt::Debug;

use anyhow::Result;

use crate::network::road_network::skim::EAAllocation;
use crate::network::road_network::RoadNetworkState;
use crate::network::NetworkSkim;
use crate::progress_bar::MetroProgressBar;
use crate::simulation::results::AgentResults;
use crate::simulation::PreprocessingData;
use crate::units::Time;

/// Variables required to execute an event.
#[derive(Debug)]
pub(crate) struct EventInput<'a> {
    /// Reference to the [PreprocessingData] of the simulation.
    pub(crate) preprocess_data: &'a PreprocessingData,
    /// Reference to the current [NetworkSkim] of the simulation.
    pub(crate) skims: &'a NetworkSkim,
    /// Mutable reference to the [AgentResults] for the current iteration.
    pub(crate) agent_results: &'a mut AgentResults,
    /// ProgressBar of the within-day model.
    pub(crate) progress_bar: MetroProgressBar,
}

/// Memory allocations that can be re-used when executing events.
#[derive(Clone, Debug, Default)]
pub(crate) struct EventAlloc {
    pub(crate) ea_alloc: EAAllocation,
}

/// Trait to represent an event (e.g., from an agent, a vehicle, a network infrastructure) that can
/// be executed.
pub(crate) trait Event: Debug {
    /// Executes the event.
    ///
    /// Returns `true` if an agent reached his / her destination during the event execution.
    fn execute<'sim: 'event, 'event>(
        self: Box<Self>,
        input: &'event mut EventInput<'sim>,
        road_network_state: &'event mut RoadNetworkState,
        alloc: &'event mut EventAlloc,
        events: &'event mut EventQueue,
    ) -> Result<bool>;
    /// Returns the time at which the event occurs.
    fn get_time(&self) -> Time;
}

/// An entry for the [EventQueue].
//
// The timing of the events could be retrieved with [Event::get_time].
// Instead, they are cached to speed-up the queue.
#[derive(Debug)]
pub(crate) struct EventEntry {
    time: Time,
    event: Box<dyn Event>,
}

impl PartialEq for EventEntry {
    fn eq(&self, _other: &Self) -> bool {
        // There is never the same entry twice in the queue.
        false
    }
}

impl Ord for EventEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // We reverse the ordering so that events are pop in chronological order.
        self.time.cmp(&other.time).reverse()
    }
}

impl PartialOrd for EventEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for EventEntry {}

/// A priority queue represented as a [BinaryHeap].
///
/// The `EventQueue` is used to store events that are executed in chronological order.
#[derive(Debug, Default)]
pub(crate) struct EventQueue(BinaryHeap<EventEntry>);

impl EventQueue {
    /// Returns the number of events in the queue.
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }
}

impl EventQueue {
    /// Pops the next event in the queue, i.e., the event with the earliest execution time.
    pub(crate) fn pop(&mut self) -> Option<Box<dyn Event>> {
        self.0.pop().map(|entry| entry.event)
    }

    /// Pushes a new event in the queue.
    pub(crate) fn push(&mut self, event: Box<dyn Event>) {
        self.0.push(EventEntry {
            time: event.get_time(),
            event,
        });
    }
}

impl FromIterator<Box<dyn Event>> for EventQueue {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Box<dyn Event>>,
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
        time: Time,
    }

    impl Event for DummyEvent {
        fn execute<'sim: 'event, 'event>(
            self: Box<Self>,
            _input: &'event mut EventInput<'sim>,
            _road_network_state: &'event mut RoadNetworkState,
            _alloc: &'event mut EventAlloc,
            _events: &'event mut EventQueue,
        ) -> Result<bool> {
            Ok(false)
        }
        fn get_time(&self) -> Time {
            self.time
        }
    }

    #[test]
    fn event_queue_test() {
        let mut q = EventQueue(BinaryHeap::new());
        assert_eq!(q.len(), 0);
        q.push(Box::new(DummyEvent { time: Time(2.) }));
        q.push(Box::new(DummyEvent { time: Time(1.) }));
        q.push(Box::new(DummyEvent { time: Time(4.) }));
        assert_eq!(q.len(), 3);
        assert_eq!(q.pop().unwrap().get_time(), Time(1.));
        assert_eq!(q.pop().unwrap().get_time(), Time(2.));
        q.push(Box::new(DummyEvent { time: Time(3.) }));
        assert_eq!(q.pop().unwrap().get_time(), Time(3.));
        assert_eq!(q.pop().unwrap().get_time(), Time(4.));
        assert_eq!(q.len(), 0);
    }
}
