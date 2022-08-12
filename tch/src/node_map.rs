use fixedbitset::FixedBitSet;
use petgraph::graph::IndexType;
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem::MaybeUninit;

/// Trait to represent a data structure that can be used as a map of values for nodes.
pub trait NodeMap {
    /// Type to represent the nodes that are used as keys in the map.
    type Node;
    /// Type to represent the values associated to the nodes.
    type Value;
    /// Reset the map.
    fn reset(&mut self);
    /// Return a reference to the value of the given node, or None if the node has no value.
    fn get_value(&self, node: &Self::Node) -> Option<&Self::Value>;
    /// Return a mutable reference to the value of the given node, or None if the node has no
    /// value.
    fn get_mut_value(&mut self, node: &Self::Node) -> Option<&mut Self::Value>;
    /// Insert a new value in the map, for the given node, erasing the previous value (if any).
    fn insert(&mut self, node: Self::Node, value: Self::Value);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = (Self::Node, &Self::Value)> + 'a>;
}

impl<N, V> NodeMap for hashbrown::HashMap<N, V>
where
    N: Copy + Eq + Hash,
{
    type Node = N;
    type Value = V;
    fn reset(&mut self) {
        self.clear();
    }
    fn get_value(&self, node: &N) -> Option<&V> {
        self.get(node)
    }
    fn get_mut_value(&mut self, node: &N) -> Option<&mut V> {
        self.get_mut(node)
    }
    fn insert(&mut self, node: N, value: V) {
        self.insert(node, value);
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = (N, &V)> + 'a> {
        Box::new(self.iter().map(|(n, v)| (*n, v)))
    }
}

impl<N, V> NodeMap for Vec<Option<(N, V)>>
where
    N: IndexType,
{
    type Node = N;
    type Value = V;
    fn reset(&mut self) {
        self.clear();
    }
    fn get_value(&self, node: &N) -> Option<&V> {
        self.get(node.index())
            .and_then(|opt| opt.as_ref())
            .map(|(_, v)| v)
    }
    fn get_mut_value(&mut self, node: &N) -> Option<&mut V> {
        self.get_mut(node.index())
            .and_then(|opt| opt.as_mut())
            .map(|(_, v)| v)
    }
    fn insert(&mut self, node: N, value: V) {
        if node.index() >= self.len() {
            self.resize_with(node.index() + 1, Default::default);
        }
        self[node.index()] = Some((node, value));
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn is_empty(&self) -> bool {
        self.iter().next().is_some()
    }
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = (N, &V)> + 'a> {
        Box::new(self.as_slice().iter().filter_map(|opt| {
            if let Some((n, v)) = opt {
                Some((*n, v))
            } else {
                None
            }
        }))
    }
}

pub struct VecMap<N, V> {
    vec: Vec<MaybeUninit<V>>,
    bs: FixedBitSet,
    n: PhantomData<N>,
}

impl<N, V> Default for VecMap<N, V> {
    fn default() -> Self {
        let mut vec = Vec::with_capacity(200_000);
        vec.fill_with(MaybeUninit::uninit);
        VecMap {
            vec,
            bs: FixedBitSet::with_capacity(200_000),
            n: PhantomData,
        }
    }
}

impl<N, V> VecMap<N, V> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        VecMap {
            vec: Vec::with_capacity(capacity),
            bs: FixedBitSet::with_capacity(capacity),
            n: PhantomData,
        }
    }
}

impl<N, V> NodeMap for VecMap<N, V>
where
    N: IndexType,
{
    type Node = N;
    type Value = V;
    fn reset(&mut self) {
        self.bs.clear();
    }
    fn get_value(&self, node: &N) -> Option<&V> {
        if self.bs.contains(node.index()) {
            unsafe { Some(self.vec[node.index()].assume_init_ref()) }
        } else {
            None
        }
    }
    fn get_mut_value(&mut self, node: &N) -> Option<&mut V> {
        if self.bs.contains(node.index()) {
            unsafe { Some(self.vec[node.index()].assume_init_mut()) }
        } else {
            None
        }
    }
    fn insert(&mut self, node: N, value: V) {
        if self.vec.len() <= node.index() {
            self.vec
                .resize_with(node.index() + 1 - self.vec.len(), MaybeUninit::uninit);
            unsafe {
                self.vec.set_len(node.index() + 1);
            }
        }
        if self.bs.len() <= node.index() {
            self.bs.grow(node.index() + 1);
        }
        self.vec[node.index()] = MaybeUninit::new(value);
        self.bs.insert(node.index());
    }
    fn len(&self) -> usize {
        self.bs.count_ones(..)
    }
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = (N, &V)> + 'a> {
        unsafe {
            Box::new(
                self.bs
                    .ones()
                    .map(|i| (N::new(i), self.vec[i].assume_init_ref())),
            )
        }
    }
}

impl<'a, NM: NodeMap> NodeMap for &'a mut NM {
    type Node = NM::Node;
    type Value = NM::Value;
    fn reset(&mut self) {
        (*self).reset();
    }
    fn get_value(&self, node: &Self::Node) -> Option<&Self::Value> {
        (**self).get_value(node)
    }
    fn get_mut_value(&mut self, node: &Self::Node) -> Option<&mut Self::Value> {
        (*self).get_mut_value(node)
    }
    fn insert(&mut self, node: Self::Node, value: Self::Value) {
        (*self).insert(node, value);
    }
    fn len(&self) -> usize {
        (**self).len()
    }
    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }
    fn iter<'b>(&'b self) -> Box<dyn Iterator<Item = (Self::Node, &Self::Value)> + 'b> {
        (**self).iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_map_test() {
        let mut map = HashMap::new();
        map.insert('a', 1);
        assert_eq!(map.get_value(&'a'), Some(&1));
        let value_a = map.get_mut_value(&'a').unwrap();
        assert_eq!(value_a, &mut 1);
        *value_a = 3;
        assert_eq!(map.get_value(&'a'), Some(&3));
    }

    #[test]
    fn vec_test() {
        let mut map: Vec<Option<(usize, char)>> = Vec::new();
        NodeMap::insert(&mut map, 1, 'a');
        assert_eq!(map.get_value(&1), Some(&'a'));
        let value_1 = map.get_mut_value(&1).unwrap();
        assert_eq!(value_1, &mut 'a');
        *value_1 = 'c';
        assert_eq!(map.get_value(&1), Some(&'c'));
    }
}
