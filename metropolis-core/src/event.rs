// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

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
use crate::units::*;

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
    /// If `true`, the edges taken by the vehicles are recorded in the results, with their entry
    /// times.
    pub(crate) record_routes: bool,
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
    fn get_time(&self) -> NonNegativeSeconds;
}

/// An entry for the [EventQueue].
//
// The timing of the events could be retrieved with [Event::get_time].
// Instead, they are cached to speed-up the queue.
#[derive(Debug)]
pub(crate) struct EventEntry {
    time: NonNegativeSeconds,
    /// Sequence number of the entry, used to break ties between events with the same time.
    seq: u64,
    event: Box<dyn Event>,
}

impl PartialEq for EventEntry {
    fn eq(&self, other: &Self) -> bool {
        // The sequence numbers are unique.
        self.seq == other.seq
    }
}

impl Ord for EventEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Events are ordered chronologically, then in first-in first-out order among events with
        // the same time, so that the order of execution does not depend on the queue layout.
        // We reverse the ordering so that the earliest events are popped first.
        (self.time, self.seq)
            .cmp(&(other.time, other.seq))
            .reverse()
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
/// Events with the same time are executed in the order in which they were pushed.
#[derive(Debug)]
pub(crate) struct EventQueue {
    /// One [BinaryHeap] per second of the period: the events occurring in second `i` (counted
    /// from the start of the period) are stored in `queues[i]`, and the events occurring after the
    /// end of the period are stored in the last heap.
    queues: Vec<BinaryHeap<EventEntry>>,
    /// Index of the current heap, i.e., the first heap that is not empty.
    index: usize,
    period: Interval,
    /// Sequence number of the next pushed event.
    next_seq: u64,
}

impl EventQueue {
    /// Returns the number of events in the queue.
    pub(crate) fn len(&self) -> usize {
        self.queues.iter().map(|q| q.len()).sum()
    }

    pub(crate) fn new<I>(iter: I, period: Interval) -> Self
    where
        I: IntoIterator<Item = Box<dyn Event>>,
    {
        let mut instance = Self {
            queues: std::iter::repeat_with(BinaryHeap::new)
                .take(period.length().to_usize_unchecked() + 1)
                .collect(),
            index: 0,
            period,
            next_seq: 0,
        };
        for entry in iter {
            instance.push(entry);
        }
        instance
    }

    /// Pops the next event in the queue, i.e., the event with the earliest execution time.
    pub(crate) fn pop(&mut self) -> Option<Box<dyn Event>> {
        loop {
            if let Some(entry) = self.queues[self.index].pop() {
                return Some(entry.event);
            }
            if self.index + 1 >= self.queues.len() {
                return None;
            }
            self.index += 1;
        }
    }

    /// Pushes a new event in the queue.
    pub(crate) fn push(&mut self, event: Box<dyn Event>) {
        let time = event.get_time();
        let i = self.index_of(time);
        debug_assert!(i >= self.index);
        self.queues[i].push(EventEntry {
            time,
            seq: self.next_seq,
            event,
        });
        self.next_seq += 1;
    }

    /// Returns the index of the heap where an event occurring at the given time is stored.
    fn index_of(&self, time: NonNegativeSeconds) -> usize {
        debug_assert!(time >= self.period.start());
        let index = time.sub_unchecked(self.period.start()).to_usize_unchecked();
        index.min(self.queues.len() - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct DummyEvent {
        time: NonNegativeSeconds,
    }

    #[derive(Debug)]
    struct NamedEvent {
        time: NonNegativeSeconds,
        // Only read through the `Debug` implementation, to identify the popped events.
        #[allow(dead_code)]
        name: &'static str,
    }

    impl Event for NamedEvent {
        fn execute<'sim: 'event, 'event>(
            self: Box<Self>,
            _input: &'event mut EventInput<'sim>,
            _road_network_state: &'event mut RoadNetworkState,
            _alloc: &'event mut EventAlloc,
            _events: &'event mut EventQueue,
        ) -> Result<bool> {
            Ok(false)
        }
        fn get_time(&self) -> NonNegativeSeconds {
            self.time
        }
    }

    #[test]
    fn event_queue_tie_order_test() {
        let t = |x| NonNegativeSeconds::new_unchecked(x);
        let named = |time, name| -> Box<dyn Event> { Box::new(NamedEvent { time, name }) };
        let mut q = EventQueue::new(
            vec![named(t(5.), "a"), named(t(1.), "b"), named(t(5.), "c")],
            Interval::new_unchecked(0.0, 64.0),
        );
        q.push(named(t(5.), "d"));
        q.push(named(t(1.), "e"));
        let mut order = Vec::new();
        while let Some(event) = q.pop() {
            order.push(format!("{event:?}"));
            if order.len() == 2 {
                // Pushed after "a", "c" and "d" with the same time: popped after them.
                q.push(named(t(5.), "f"));
            }
        }
        let expected: Vec<_> = [
            (1., "b"),
            (1., "e"),
            (5., "a"),
            (5., "c"),
            (5., "d"),
            (5., "f"),
        ]
        .into_iter()
        .map(|(x, name)| format!("{:?}", NamedEvent { time: t(x), name }))
        .collect();
        assert_eq!(order, expected);
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
        fn get_time(&self) -> NonNegativeSeconds {
            self.time
        }
    }

    #[test]
    fn event_queue_test() {
        let mut q = EventQueue::new(vec![], Interval::new_unchecked(0.0, 64.0));
        assert_eq!(q.len(), 0);
        q.push(Box::new(DummyEvent {
            time: NonNegativeSeconds::new_unchecked(2.),
        }));
        q.push(Box::new(DummyEvent {
            time: NonNegativeSeconds::new_unchecked(1.),
        }));
        q.push(Box::new(DummyEvent {
            time: NonNegativeSeconds::new_unchecked(4.),
        }));
        assert_eq!(q.len(), 3);
        assert_eq!(
            q.pop().unwrap().get_time(),
            NonNegativeSeconds::new_unchecked(1.)
        );
        assert_eq!(
            q.pop().unwrap().get_time(),
            NonNegativeSeconds::new_unchecked(2.)
        );
        q.push(Box::new(DummyEvent {
            time: NonNegativeSeconds::new_unchecked(3.),
        }));
        assert_eq!(
            q.pop().unwrap().get_time(),
            NonNegativeSeconds::new_unchecked(3.)
        );
        assert_eq!(
            q.pop().unwrap().get_time(),
            NonNegativeSeconds::new_unchecked(4.)
        );
        assert_eq!(q.len(), 0);
    }
}
