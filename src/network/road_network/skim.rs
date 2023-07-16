// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of [RoadNetworkSkims].
use std::ops::Index;

use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use indicatif::{ProgressBar, ProgressStyle};
use log::{log_enabled, Level};
use object_pool::Pool;
use petgraph::graph::{EdgeIndex, NodeIndex};
use rayon::prelude::*;
use schemars::JsonSchema;
use serde::Serialize;
use tch::{algo, DefaultTCHProfileAllocation};
use tch::{DefaultEarliestArrivalAllocation, HierarchyOverlay, SearchSpaces};
use ttf::{TTFNum, TTF};

use crate::units::Time;

/// Structure to store a [RoadNetworkSkim] for each unique vehicle of a
/// [RoadNetwork](super::RoadNetwork).
#[derive(Clone, Default, Debug, Serialize, JsonSchema)]
#[serde(bound(serialize = "T: TTFNum"))]
#[serde(into = "SerializedRoadNetworkSkims<T>")]
#[schemars(
    description = "Travel-time function for each OD pair (inner array), for each unique vehicle type (outer array)"
)]
pub struct RoadNetworkSkims<T>(
    #[schemars(with = "SerializedRoadNetworkSkims<T>")] pub Vec<Option<RoadNetworkSkim<T>>>,
);

impl<T> Index<usize> for RoadNetworkSkims<T> {
    type Output = Option<RoadNetworkSkim<T>>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

/// Structure holding the data needed to compute earliest-arrival and profile queries for a graph
/// representing the road network with fixed weights.
#[derive(Clone, Default, Debug)]
pub struct RoadNetworkSkim<T> {
    /// Hierarchy overlay of the road-network graph.
    hierarchy_overlay: HierarchyOverlay<Time<T>>,
    /// Mapping from original node id to simulation NodeIndex.
    node_map: HashMap<u64, NodeIndex>,
    /// Travel time functions for each used OD pair.
    profile_query_cache: ODTravelTimeFunctions<T>,
}

impl<T: TTFNum> RoadNetworkSkim<T> {
    /// Creates a new RoadNetworkSkim.
    pub fn new(
        hierarchy_overlay: HierarchyOverlay<Time<T>>,
        node_map: HashMap<u64, NodeIndex>,
    ) -> Self {
        RoadNetworkSkim {
            hierarchy_overlay,
            node_map,
            profile_query_cache: HashMap::new(),
        }
    }

    /// Compute the forward and backward search spaces for a set of origins and destinations.
    /// This will speed-up the following profile queries from one of the origins to one of the
    /// destinations.
    pub fn get_search_spaces(
        &mut self,
        origins: &HashSet<u64>,
        destinations: &HashSet<u64>,
    ) -> SearchSpaces<Time<T>> {
        let sources: HashSet<_> = origins.iter().map(|&o_id| self.get_node_id(o_id)).collect();
        let targets: HashSet<_> = destinations
            .iter()
            .map(|&d_id| self.get_node_id(d_id))
            .collect();
        self.hierarchy_overlay.get_search_spaces(&sources, &targets)
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
    pub fn pre_compute_profile_queries_intersect(
        &mut self,
        od_pairs: &HashMap<u64, HashSet<u64>>,
        search_spaces: &SearchSpaces<Time<T>>,
    ) -> Result<()> {
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(od_pairs.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        self.profile_query_cache = od_pairs
            .par_iter()
            .map(|(&source, targets)| {
                bp.inc(1);
                let source_id = self.get_node_id(source);
                let target_ttfs = targets
                    .iter()
                    .map(|&target| {
                        let target_id = self.get_node_id(target);
                        let ttf =
                            algo::intersect_profile_query(source_id, target_id, search_spaces)?;
                        Ok((target, ttf))
                    })
                    .collect::<Result<HashMap<u64, Option<TTF<Time<T>>>>>>()?;
                Ok((source, target_ttfs))
            })
            .collect::<Result<ODTravelTimeFunctions<T>>>()?;
        bp.finish_and_clear();
        Ok(())
    }

    /// Compute profile queries for a set of origin-destination pairs using TCH.
    ///
    /// The origin-destination pairs must be given as a [HashMap] where the keys are the source
    /// nodes and the values are a [HashSet] of target nodes.
    ///
    /// The profile queries are run in parallel (one thread for each origin node) and the resulting
    /// travel-time functions are stored in a cache.
    pub fn pre_compute_profile_queries_tch(
        &mut self,
        od_pairs: &HashMap<u64, HashSet<u64>>,
    ) -> Result<()> {
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(od_pairs.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        let pool: Pool<TCHProfileAlloc<T>> =
            Pool::new(rayon::current_num_threads(), Default::default);
        self.profile_query_cache = od_pairs
            .par_iter()
            .map_init(
                || pool.pull(Default::default),
                |alloc, (&source, targets)| {
                    let source_id = self.get_node_id(source);
                    bp.inc(1);
                    let target_ttfs = targets
                        .iter()
                        .map(|&target| {
                            let target_id = self.get_node_id(target);
                            let (profile_alloc, candidate_map) = alloc.get_mut_variables();
                            let ttf = self.hierarchy_overlay.profile_query(
                                source_id,
                                target_id,
                                &mut profile_alloc.interval_search,
                                &mut profile_alloc.profile_search,
                                candidate_map,
                            );
                            Ok((target, ttf))
                        })
                        .collect::<Result<HashMap<u64, Option<TTF<Time<T>>>>>>()?;
                    Ok((source, target_ttfs))
                },
            )
            .collect::<Result<ODTravelTimeFunctions<T>>>()?;
        bp.finish_and_clear();
        Ok(())
    }

    fn get_node_id(&self, original_id: u64) -> NodeIndex {
        *self
            .node_map
            .get(&original_id)
            .unwrap_or_else(|| panic!("No node with id {original_id} in the road-network graph"))
    }

    /// Return the travel-time function resulting from the profile query between two nodes.
    ///
    /// Return an error if the result is not in the cache.
    ///
    /// Return `None` if there is no route between the two nodes.
    pub fn profile_query(&self, from: u64, to: u64) -> Result<Option<&TTF<Time<T>>>> {
        self.profile_query_cache
            .get(&from)
            .and_then(|targets| targets.get(&to))
            .map(|opt_ttf| opt_ttf.as_ref())
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
        from: u64,
        to: u64,
        at_time: Time<T>,
        alloc: &mut EAAllocation<T>,
    ) -> Result<Option<(Time<T>, Vec<EdgeIndex>)>> {
        self.hierarchy_overlay.earliest_arrival_query(
            self.get_node_id(from),
            self.get_node_id(to),
            at_time,
            &mut alloc.ea_alloc,
            &mut alloc.candidate_map,
        )
    }
}

#[derive(Clone, Default, Debug, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
struct SerializedRoadNetworkSkims<T>(Vec<Vec<ODPairTTF<T>>>);

#[derive(Clone, Default, Debug, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
struct ODPairTTF<T> {
    /// Original id of the origin node.
    origin: u64,
    /// Original id of the destination node.
    destination: u64,
    /// Travel-time function from origin to destination.
    ///
    /// `None` if destination cannot be reached from origin.
    ttf: Option<TTF<Time<T>>>,
}

impl<T> From<RoadNetworkSkims<T>> for SerializedRoadNetworkSkims<T> {
    fn from(skims: RoadNetworkSkims<T>) -> Self {
        let mut serialized_skims = Vec::with_capacity(skims.0.len());
        for vehicle_skims in skims.0 {
            let mut serialized_vehicle_skims = Vec::new();
            if let Some(vehicle_skims) = vehicle_skims {
                for (origin, destination_ttfs) in vehicle_skims.profile_query_cache.into_iter() {
                    for (destination, ttf) in destination_ttfs.into_iter() {
                        serialized_vehicle_skims.push(ODPairTTF {
                            origin,
                            destination,
                            ttf,
                        });
                    }
                }
            }
            serialized_skims.push(serialized_vehicle_skims);
        }
        SerializedRoadNetworkSkims(serialized_skims)
    }
}

/// Map for some origin nodes, an OD-level travel-time function, for some destination nodes.
///
/// The map uses the original node ids.
type ODTravelTimeFunctions<T> = HashMap<u64, HashMap<u64, Option<TTF<Time<T>>>>>;

/// A memory allocation that holds the structures required during earliest arrival queries.
#[derive(Clone, Debug, Default)]
pub struct EAAllocation<T: TTFNum> {
    ea_alloc: DefaultEarliestArrivalAllocation<Time<T>>,
    candidate_map: HashMap<NodeIndex, (Time<T>, Time<T>)>,
}

/// A memory allocation for TCH profile queries.
#[derive(Clone, Debug, Default)]
struct TCHProfileAlloc<T: TTFNum> {
    profile_alloc: DefaultTCHProfileAllocation<Time<T>>,
    candidate_map: HashMap<NodeIndex, Time<T>>,
}

impl<T: TTFNum> TCHProfileAlloc<T> {
    fn get_mut_variables(
        &mut self,
    ) -> (
        &mut DefaultTCHProfileAllocation<Time<T>>,
        &mut HashMap<NodeIndex, Time<T>>,
    ) {
        (&mut self.profile_alloc, &mut self.candidate_map)
    }
}
