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

// Number of BinaryHeap in the equent queue.
const Q: usize = 256;

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
    fn get_time(&self) -> NonNegativeSeconds;
}

/// An entry for the [EventQueue].
//
// The timing of the events could be retrieved with [Event::get_time].
// Instead, they are cached to speed-up the queue.
#[derive(Debug)]
pub(crate) struct EventEntry {
    time: NonNegativeSeconds,
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
#[derive(Debug)]
pub(crate) struct EventQueue {
    queues: [BinaryHeap<EventEntry>; Q],
    index: usize,
    period: Interval,
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
            queues: std::array::from_fn(|_| BinaryHeap::new()),
            index: 0,
            period,
        };
        for entry in iter {
            instance.push(entry);
        }
        instance
    }

    /// Pops the next event in the queue, i.e., the event with the earliest execution time.
    pub(crate) fn pop(&mut self) -> Option<Box<dyn Event>> {
        if let Some(entry) = self.queues[self.index].pop() {
            Some(entry.event)
        } else {
            self.index += 1;
            if self.index >= Q {
                return None;
            }
            self.pop()
        }
    }

    /// Pushes a new event in the queue.
    pub(crate) fn push(&mut self, event: Box<dyn Event>) {
        let time = event.get_time();
        let i = self.index_of(time);
        debug_assert!(i >= self.index);
        self.queues[i].push(EventEntry { time, event });
    }

    fn index_of(&self, time: NonNegativeSeconds) -> usize {
        debug_assert!(time >= self.period.start());
        let share = time.sub_unchecked(self.period.start()) / self.period.length();
        let index = (share * Q).to_usize_unchecked();
        index.min(Q - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct DummyEvent {
        time: NonNegativeSeconds,
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
