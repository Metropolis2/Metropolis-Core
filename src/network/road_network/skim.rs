// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of [RoadNetworkSkims].
use super::vehicle::VehicleIndex;
use crate::units::Time;

use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use petgraph::graph::{EdgeIndex, NodeIndex};
use rayon::prelude::*;
use std::ops::Index;
use tch::algo;
use tch::{DefaultEarliestArrivalAllocation, HierarchyOverlay, SearchSpaces};
use ttf::{TTFNum, TTFSimplification, TTF};

/// Structure to store a [RoadNetworkSkim] for each [Vehicle](super::vehicle::Vehicle) of a
/// [RoadNetwork](super::RoadNetwork).
#[derive(Clone, Default, Debug)]
pub struct RoadNetworkSkims<T>(pub Vec<Option<RoadNetworkSkim<T>>>);

impl<T> Index<VehicleIndex> for RoadNetworkSkims<T> {
    type Output = Option<RoadNetworkSkim<T>>;
    fn index(&self, index: VehicleIndex) -> &Self::Output {
        &self.0[index.index()]
    }
}

/// For a given origin node, map to each destination a travel-time function.
type CachedQueriesFromSource<T> = HashMap<NodeIndex, Option<TTF<Time<T>>>>;

/// Structure holding the data needed to compute earliest-arrival and profile queries for a graph
/// representing the road network with fixed weights.
#[derive(Clone, Default, Debug)]
pub struct RoadNetworkSkim<T> {
    hierarchy_overlay: HierarchyOverlay<Time<T>>,
    search_spaces: Option<SearchSpaces<Time<T>>>,
    profile_query_cache: HashMap<NodeIndex, CachedQueriesFromSource<T>>,
}

impl<T: TTFNum> RoadNetworkSkim<T> {
    /// Creates a new RoadNetworkSkim.
    pub fn new(hierarchy_overlay: HierarchyOverlay<Time<T>>) -> Self {
        RoadNetworkSkim {
            hierarchy_overlay,
            search_spaces: None,
            profile_query_cache: HashMap::new(),
        }
    }

    /// Compute the forward and backward search spaces for a set of origins and destinations.
    /// This will speed-up the following profile queries from one of the origins to one of the
    /// destinations.
    pub fn compute_search_spaces(
        &mut self,
        origins: &HashSet<NodeIndex>,
        destinations: &HashSet<NodeIndex>,
    ) {
        self.search_spaces = Some(
            self.hierarchy_overlay
                .get_search_spaces(origins, destinations),
        );
    }

    /// Simplify all the travel-time functions in the search spaces, using the given
    /// [TTFSimplification].
    pub fn simplify_search_spaces(&mut self, simplification: TTFSimplification<Time<T>>) {
        if let Some(search_space) = &mut self.search_spaces {
            search_space.simplify(simplification);
        }
    }

    /// Compute profile queries for a set of origin-destination pairs using the Intersect algorithm
    /// from Geisberger and Sanders (2010)[^ref].
    ///
    /// The origin-destination pairs must be given as a [HashMap] where the keys are the source
    /// nodes and the values are a [HashSet] of target nodes.
    ///
    /// For each origin-destination pair, the forward search spaces of the RoadNetworkSkim must
    /// contain the origin node and the backward search spaces must contain the destination node.
    ///
    /// The profile queries are run in parallel (one thread for each origin node) and the resulting
    /// travel-time functions are stored in a cache.
    ///
    /// [^ref]: Geisberger, R., Sanders, P. (2010).
    ///     Engineering time-dependent many-to-many shortest paths computation.
    ///     _10th Workshop on Algorithmic Approaches for Transportation Modelling, Optimization,
    ///     and Systems (ATMOS'10)_, 2010 .
    pub fn pre_compute_profile_queries(
        &mut self,
        od_pairs: &HashMap<NodeIndex, HashSet<NodeIndex>>,
    ) -> Result<()> {
        self.profile_query_cache = od_pairs
            .par_iter()
            .map(|(&source, targets)| {
                let results = targets
                    .iter()
                    .map(|&target| {
                        let ttf = algo::intersect_profile_query(
                            source,
                            target,
                            self.search_spaces.as_ref().unwrap(),
                        )?;
                        Ok((target, ttf))
                    })
                    .collect::<Result<CachedQueriesFromSource<T>>>()?;
                Ok((source, results))
            })
            .collect::<Result<HashMap<_, _>>>()?;
        Ok(())
    }

    /// Return the travel-time function resulting from the profile query between two nodes.
    ///
    /// Return an error if the result is not in the cache.
    ///
    /// Return `None` if there is no route between the two nodes.
    pub fn profile_query(&self, from: NodeIndex, to: NodeIndex) -> Result<Option<&TTF<Time<T>>>> {
        self.profile_query_cache
            .get(&from)
            .and_then(|r| r.get(&to).map(|ttf_opt| ttf_opt.as_ref()))
            .ok_or_else(|| {
                anyhow!(
                    "The profile query from {:?} to {:?} is not in the cache",
                    from,
                    to
                )
            })
    }

    /// Compute and return the arrival time and route of the fastest path between two nodes, at a
    /// given departure time.
    ///
    /// Return an error if a problem occured during the earliest arrival query.
    ///
    /// Return `None` if the destination node cannot be reached from the origin node, for the given
    /// departure time.
    pub fn earliest_arrival_query(
        &self,
        from: NodeIndex,
        to: NodeIndex,
        at_time: Time<T>,
        alloc: &mut EAAllocation<T>,
    ) -> Result<Option<(Time<T>, Vec<EdgeIndex>)>> {
        self.hierarchy_overlay.earliest_arrival_query(
            from,
            to,
            at_time,
            &mut alloc.ea_alloc,
            &mut alloc.candidate_map,
        )
    }
}

/// A memory allocation that holds the structures required during earliest arrival queries.
#[derive(Clone, Debug, Default)]
pub struct EAAllocation<T: TTFNum> {
    ea_alloc: DefaultEarliestArrivalAllocation<Time<T>>,
    candidate_map: HashMap<NodeIndex, (Time<T>, Time<T>)>,
}
