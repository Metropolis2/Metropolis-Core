use hashbrown::hash_map::HashMap;
use std::cmp;
use std::hash::Hash;

/// Structure to hold a hop limit and the number of hops for each node, i.e., the minimum number of
/// edges that must be crossed to get from a source to this node.
pub struct HopLimit<'a, N> {
    /// Maximum number of hops allowed (exclusive).
    limit: u8,
    /// [NodeMap] that stores the number of hop for each node explored.
    nb_hops: &'a mut HashMap<N, u8>,
}

impl<'a, N> HopLimit<'a, N> {
    /// Initialize a new HopLimit given the maximum number of hops allowed and a [NodeMap] `Node ->
    /// u8` to store the number of hop for each node.
    pub fn new(limit: u8, nb_hops: &'a mut HashMap<N, u8>) -> Self {
        HopLimit { limit, nb_hops }
    }
}

impl<'a, N> HopLimit<'a, N>
where
    N: Eq + Hash,
{
    /// Return `true` if the number of hops for the node exceeds the hop-limit.
    pub fn exceed_limit(&self, node: N) -> bool {
        self.nb_hops
            .get(&node)
            .map(|&h| h >= self.limit)
            .unwrap_or(false)
    }
    /// Add a newly explored edge to the HopLimit.
    ///
    /// This sets the number of hops for the target node to the minimum between its current number
    /// of hops (if already set) and the number of hops of the source node + 1.
    pub fn add_edge(&mut self, source: N, target: N) {
        let nb_hop = if let Some(h) = self.nb_hops.get(&source) {
            h + 1
        } else {
            // The source node of the edge is a source node of the query.
            1
        };
        self.nb_hops
            .entry(target)
            .and_modify(|e| *e = cmp::max(*e, nb_hop))
            .or_insert(nb_hop);
    }
    /// Reset the hop counts.
    pub fn reset(&mut self) {
        self.nb_hops.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hashbrown::HashMap;

    #[test]
    fn hop_limit_test() {
        let mut map = HashMap::new();
        let mut hl = HopLimit::new(2, &mut map);
        assert!(!hl.exceed_limit(0));
        hl.add_edge(0, 1);
        hl.add_edge(1, 2);
        assert!(!hl.exceed_limit(0));
        assert!(!hl.exceed_limit(1));
        assert!(hl.exceed_limit(2));
        hl.add_edge(0, 2);
        assert!(hl.exceed_limit(2));
    }
}
