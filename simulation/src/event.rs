use crate::agent::AgentIndex;
use crate::network::{NetworkSkim, NetworkState};
use crate::simulation::AgentResult;
use crate::units::Time;

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt::Debug;
use ttf::TTFNum;

pub trait Event<T>: Debug {
    fn execute(
        self: Box<Self>,
        exp_skims: &NetworkSkim<T>,
        state: &mut NetworkState<T>,
        result: Option<&mut AgentResult<T>>,
        events: &mut EventQueue<T>,
    );
    fn get_time(&self) -> Time<T>;
    fn get_agent_index(&self) -> Option<AgentIndex> {
        None
    }
}

pub struct EventEntry<T> {
    time: Time<T>,
    event: Box<dyn Event<T>>,
}

impl<T> PartialEq for EventEntry<T> {
    fn eq(&self, _other: &Self) -> bool {
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

// We could store the Box<dyn Event> directly.
// Instead, we use a EventEntry so that the event times are stored in the stack.
pub struct EventQueue<T>(BinaryHeap<EventEntry<T>>);

impl<T> EventQueue<T> {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T: TTFNum> EventQueue<T> {
    pub fn pop(&mut self) -> Option<Box<dyn Event<T>>> {
        self.0.pop().map(|entry| entry.event)
    }

    pub fn push(&mut self, event: Box<dyn Event<T>>) {
        self.0.push(EventEntry {
            time: event.get_time(),
            event,
        });
    }
}

impl<T: TTFNum> std::iter::FromIterator<Box<dyn Event<T>>> for EventQueue<T> {
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
