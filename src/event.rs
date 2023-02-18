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

use crate::agent::AgentIndex;
use crate::network::{Network, NetworkSkim, NetworkState};
use crate::simulation::results::AgentResult;
use crate::simulation::PreprocessingData;
use crate::units::Time;

/// Trait to represent an event (e.g., from an agent, a vehicle, a network infrastructure) that can
/// be executed.
pub trait Event<'a, T>: Debug {
    /// Executes the event.
    ///
    /// - The [NetworkState] can be modified by the event execution.
    ///
    /// - If the event is associated with an agent, the [AgentResult] can be updated.
    ///
    /// - The current [EventQueue] can be modified (i.e., new events can be pushed in the queue).
    fn execute<'b: 'a>(
        self: Box<Self>,
        network: &'b Network<T>,
        skims: &NetworkSkim<T>,
        state: &mut NetworkState<'a, T>,
        preprocess_data: &PreprocessingData<T>,
        result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<'a, T>,
    ) -> Result<()>;
    /// Returns the time at which the event occurs.
    fn get_time(&self) -> Time<T>;
    /// Returns the [AgentIndex] of the associated [Agent](crate::agent::Agent), or `None` if the
    /// event is not associated with an agent.
    fn get_agent_index(&self) -> Option<AgentIndex> {
        None
    }
}

/// An entry for the [EventQueue].
//
// The timing of the events could be retrieved with [Event::get_time].
// Instead, they are cached to speed-up the queue.
#[derive(Debug)]
pub struct EventEntry<'a, T> {
    time: Time<T>,
    event: Box<dyn Event<'a, T> + 'a>,
}

impl<T> PartialEq for EventEntry<'_, T> {
    fn eq(&self, _other: &Self) -> bool {
        // There is never the same entry twice in the queue.
        false
    }
}

impl<T: TTFNum> Ord for EventEntry<'_, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // We reverse the ordering so that events are pop in chronological order.
        self.time.cmp(&other.time).reverse()
    }
}

impl<T: TTFNum> PartialOrd for EventEntry<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Eq for EventEntry<'_, T> {}

/// A priority queue represented as a [BinaryHeap].
///
/// The `EventQueue` is used to store events that are executed in chronological order.
#[derive(Debug)]
pub struct EventQueue<'a, T>(BinaryHeap<EventEntry<'a, T>>);

impl<T> EventQueue<'_, T> {
    /// Returns `true` if the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of events in the queue.
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a, T: TTFNum> EventQueue<'a, T> {
    /// Pops the next event in the queue, i.e., the event with the earliest execution time.
    pub fn pop(&mut self) -> Option<Box<dyn Event<'a, T> + 'a>> {
        self.0.pop().map(|entry| entry.event)
    }

    /// Pushes a new event in the queue.
    pub fn push(&mut self, event: Box<dyn Event<'a, T> + 'a>) {
        self.0.push(EventEntry {
            time: event.get_time(),
            event,
        });
    }
}

impl<T: TTFNum> Default for EventQueue<'_, T> {
    fn default() -> Self {
        EventQueue(BinaryHeap::new())
    }
}

impl<'a, T: TTFNum> FromIterator<Box<dyn Event<'a, T> + 'a>> for EventQueue<'a, T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Box<dyn Event<'a, T> + 'a>>,
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

    impl<'a> Event<'a, f64> for DummyEvent {
        fn execute<'b: 'a>(
            self: Box<Self>,
            _network: &'b Network<f64>,
            _exp_skims: &NetworkSkim<f64>,
            _state: &mut NetworkState<'a, f64>,
            _preprocess_data: &PreprocessingData<f64>,
            _result: Option<&mut AgentResult<f64>>,
            _events: &mut EventQueue<'a, f64>,
        ) -> Result<()> {
            Ok(())
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
