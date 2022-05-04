use hashbrown::hash_map::DefaultHashBuilder;
use priority_queue::PriorityQueue;
use std::cmp::Reverse;
use std::hash::{BuildHasher, Hash};

/// Trait representing a priority queue of (key, value) items that are sorted in increasing order
/// of their values.
pub trait MinPriorityQueue {
    /// Type of the keys.
    type Key;
    /// Type of the values.
    type Value;
    /// Reset the priority queue.
    fn reset(&mut self);
    /// Push a new item to the priority queue.
    fn push(&mut self, key: Self::Key, value: Self::Value);
    /// Decrease the value of a key.
    fn decrease_value(&mut self, key: Self::Key, new_value: Self::Value);
    /// Pop the next item in the queue.
    fn pop(&mut self) -> Option<(Self::Key, Self::Value)>;
    /// Peek the next item in the queue.
    fn peek(&self) -> Option<(&Self::Key, &Self::Value)>;
    /// Return true if the priority queue is empty.
    fn is_empty(&self) -> bool {
        self.peek().is_some()
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd)]
pub struct ImplOrd<T>(T);

impl<T: PartialEq> Eq for ImplOrd<T> {}

#[allow(clippy::derive_ord_xor_partial_ord)]
impl<T: PartialOrd> Ord for ImplOrd<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).expect("Invalid comparison")
    }
}

pub type MinPQ<I, P> = PriorityQueue<I, Reverse<ImplOrd<P>>, DefaultHashBuilder>;

impl<I, P, H> MinPriorityQueue for PriorityQueue<I, Reverse<ImplOrd<P>>, H>
where
    I: Copy + Hash + Eq,
    P: Copy + PartialOrd,
    H: BuildHasher,
{
    type Key = I;
    type Value = P;
    fn reset(&mut self) {
        self.clear();
    }
    fn push(&mut self, key: I, value: P) {
        self.push(key, Reverse(ImplOrd(value)));
    }
    fn decrease_value(&mut self, key: I, value: P) {
        // Decreasing the value = increasing the priority.
        self.push_increase(key, Reverse(ImplOrd(value)));
    }
    fn pop(&mut self) -> Option<(I, P)> {
        self.pop().map(|(n, rev_k)| (n, rev_k.0 .0))
    }
    fn peek(&self) -> Option<(&I, &P)> {
        self.peek().map(|(n, rev_k)| (n, &rev_k.0 .0))
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn priority_queue_test() {
        let queue: &mut dyn MinPriorityQueue<Key = char, Value = u32> = &mut PriorityQueue::new();
        queue.push('a', 3);
        queue.push('b', 2);
        assert_eq!(queue.peek(), Some((&'b', &2)));
        queue.decrease_value('a', 1);
        assert_eq!(queue.pop(), Some(('a', 1)));
        assert_eq!(queue.pop(), Some(('b', 2)));
        assert_eq!(queue.pop(), None);
        queue.push('c', 5);
        assert_eq!(queue.peek(), Some((&'c', &5)));
        queue.reset();
        assert_eq!(queue.peek(), None);
    }
}
