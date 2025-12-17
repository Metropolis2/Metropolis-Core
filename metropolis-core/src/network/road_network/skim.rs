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

//! Description of [RoadNetworkSkims].
use std::ops::Index;

use anyhow::{anyhow, Result};
use hashbrown::{HashMap, HashSet};
use indicatif::{ProgressBar, ProgressStyle};
use log::{log_enabled, Level};
use object_pool::Pool;
use petgraph::graph::{node_index, EdgeIndex, NodeIndex};
use rayon::prelude::*;
use rkyv::{Archive, Deserialize as Rdeser, Serialize as Rser};
use serde::{Deserialize, Serialize};
use tch::{algo, DefaultTCHProfileAllocation};
use tch::{DefaultEarliestArrivalAllocation, HierarchyOverlay, SearchSpaces};
use ttf::TTF;

use super::preprocess::UniqueVehicleIndex;
use super::OriginalNodeId;
use crate::units::AnySeconds;

/// Structure to store a [RoadNetworkSkim] for each unique vehicle of a
/// [RoadNetwork](super::RoadNetwork).
#[derive(Clone, Default, Debug, Serialize, Deserialize, Archive, Rdeser, Rser)]
#[serde(into = "SerializedRoadNetworkSkims")]
pub struct RoadNetworkSkims(pub Vec<Option<RoadNetworkSkim>>);

impl Index<UniqueVehicleIndex> for RoadNetworkSkims {
    type Output = Option<RoadNetworkSkim>;
    fn index(&self, x: UniqueVehicleIndex) -> &Self::Output {
        &self.0[x.index()]
    }
}

/// Structure holding the data needed to compute earliest-arrival and profile queries for a graph
/// representing the road network with fixed weights.
#[derive(Clone, Default, Debug, Serialize, Deserialize, Archive, Rdeser, Rser)]
pub struct RoadNetworkSkim {
    /// Hierarchy overlay of the road-network graph.
    #[rkyv(with=HierarchyOverlayDummy)]
    hierarchy_overlay: HierarchyOverlay<AnySeconds>,
    /// Mapping from original node id to simulation NodeIndex.
    node_map: HashMap<OriginalNodeId, NodeIndexDef>,
    /// Travel time functions for each used OD pair.
    profile_query_cache: ODTravelTimeFunctions,
}

#[derive(Archive, Rdeser, Rser)]
#[rkyv(remote=HierarchyOverlay<AnySeconds>)]
#[rkyv(archived=ArchivedHierarchyOverlay)]
struct HierarchyOverlayDummy;

impl From<HierarchyOverlayDummy> for HierarchyOverlay<AnySeconds> {
    fn from(_: HierarchyOverlayDummy) -> Self {
        Default::default()
    }
}

#[derive(Clone, Copy, Default, Debug, Serialize, Deserialize, Archive, Rdeser, Rser)]
struct NodeIndexDef(u32);

impl From<NodeIndexDef> for NodeIndex {
    fn from(value: NodeIndexDef) -> Self {
        node_index(value.0 as usize)
    }
}

impl From<NodeIndex> for NodeIndexDef {
    fn from(value: NodeIndex) -> Self {
        NodeIndexDef(value.index() as u32)
    }
}

impl RoadNetworkSkim {
    /// Creates a new RoadNetworkSkim.
    pub fn new(
        hierarchy_overlay: HierarchyOverlay<AnySeconds>,
        node_map: HashMap<OriginalNodeId, NodeIndex>,
    ) -> Self {
        RoadNetworkSkim {
            hierarchy_overlay,
            node_map: node_map.into_iter().map(|(a, b)| (a, b.into())).collect(),
            profile_query_cache: HashMap::new(),
        }
    }

    /// Compute the forward and backward search spaces for a set of origins and destinations.
    /// This will speed-up the following profile queries from one of the origins to one of the
    /// destinations.
    pub fn get_search_spaces(
        &mut self,
        origins: Vec<OriginalNodeId>,
        destinations: Vec<OriginalNodeId>,
    ) -> SearchSpaces<AnySeconds> {
        let sources: HashSet<_> = origins
            .into_iter()
            .map(|o_id| self.get_node_id(o_id))
            .collect();
        let targets: HashSet<_> = destinations
            .into_iter()
            .map(|d_id| self.get_node_id(d_id))
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
        (od_pairs, nb_origins): (
            impl ParallelIterator<Item = (OriginalNodeId, impl Iterator<Item = OriginalNodeId>)>,
            usize,
        ),
        search_spaces: &SearchSpaces<AnySeconds>,
    ) -> Result<()> {
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(nb_origins as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        let pool: Pool<TCHProfileAlloc> = Pool::new(rayon::current_num_threads(), Default::default);
        self.profile_query_cache = od_pairs
            .map_init(
                || pool.pull(Default::default),
                |alloc, (source, targets)| {
                    bp.inc(1);
                    let source_id = self.get_node_id(source);
                    let mut extra_targets = Vec::with_capacity(targets.size_hint().1.unwrap_or(16));
                    let mut target_ttfs = if search_spaces.has_forward_search_space(&source_id) {
                        targets
                            .filter_map(|target| {
                                let target_id = self.get_node_id(target);
                                if search_spaces.has_backward_search_space(&target_id) {
                                    Some(
                                        algo::intersect_profile_query(
                                            source_id,
                                            target_id,
                                            search_spaces,
                                        )
                                        .map(|ttf| (target, ttf)),
                                    )
                                } else {
                                    extra_targets.push(target);
                                    None
                                }
                            })
                            .collect::<Result<HashMap<OriginalNodeId, Option<TTF<AnySeconds>>>>>()?
                    } else {
                        extra_targets.extend(targets);
                        HashMap::with_capacity(extra_targets.len())
                    };
                    // Run TCH queries for the remaining pairs.
                    for target in extra_targets {
                        let target_id = self.get_node_id(target);
                        let (profile_alloc, candidate_map) = alloc.get_mut_variables();
                        let ttf = self.hierarchy_overlay.profile_query(
                            source_id,
                            target_id,
                            &mut profile_alloc.interval_search,
                            &mut profile_alloc.profile_search,
                            candidate_map,
                        );
                        target_ttfs.insert(target, ttf);
                    }
                    Ok((source, target_ttfs))
                },
            )
            .collect::<Result<ODTravelTimeFunctions>>()?;
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
        (od_pairs, nb_origins): (
            impl ParallelIterator<Item = (OriginalNodeId, impl Iterator<Item = OriginalNodeId>)>,
            usize,
        ),
    ) -> Result<()> {
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(nb_origins as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        let pool: Pool<TCHProfileAlloc> = Pool::new(rayon::current_num_threads(), Default::default);
        self.profile_query_cache = od_pairs
            .map_init(
                || pool.pull(Default::default),
                |alloc, (source, targets)| {
                    let source_id = self.get_node_id(source);
                    bp.inc(1);
                    let target_ttfs = targets
                        .map(|target| {
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
                        .collect::<Result<HashMap<OriginalNodeId, Option<TTF<AnySeconds>>>>>()?;
                    Ok((source, target_ttfs))
                },
            )
            .collect::<Result<ODTravelTimeFunctions>>()?;
        bp.finish_and_clear();
        Ok(())
    }

    fn get_node_id(&self, original_id: OriginalNodeId) -> NodeIndex {
        NodeIndex::from(
            *self.node_map.get(&original_id).unwrap_or_else(|| {
                panic!("No node with id {original_id} in the road-network graph")
            }),
        )
    }

    /// Return the travel-time function resulting from the profile query between two nodes.
    ///
    /// Return an error if the result is not in the cache.
    ///
    /// Return `None` if there is no route between the two nodes.
    pub fn profile_query(
        &self,
        from: OriginalNodeId,
        to: OriginalNodeId,
    ) -> Result<Option<&TTF<AnySeconds>>> {
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
        from: OriginalNodeId,
        to: OriginalNodeId,
        at_time: AnySeconds,
        alloc: &mut EAAllocation,
    ) -> Result<Option<(AnySeconds, Vec<EdgeIndex>)>> {
        self.hierarchy_overlay.earliest_arrival_query(
            self.get_node_id(from),
            self.get_node_id(to),
            at_time,
            &mut alloc.ea_alloc,
            &mut alloc.candidate_map,
        )
    }

    pub(crate) fn profile_query_cache_complexity(&self) -> usize {
        self.profile_query_cache
            .values()
            .map(|map| {
                map.values()
                    .filter_map(|ttf_opt| ttf_opt.as_ref().map(|ttf| ttf.complexity()))
                    .sum::<usize>()
            })
            .sum()
    }
}

#[derive(Clone, Default, Debug, Serialize)]
struct SerializedRoadNetworkSkims(Vec<Vec<ODPairTTF>>);

#[derive(Clone, Default, Debug, Serialize)]
struct ODPairTTF {
    /// Original id of the origin node.
    origin: OriginalNodeId,
    /// Original id of the destination node.
    destination: OriginalNodeId,
    /// Travel-time function from origin to destination.
    ///
    /// `None` if destination cannot be reached from origin.
    ttf: Option<TTF<AnySeconds>>,
}

impl From<RoadNetworkSkims> for SerializedRoadNetworkSkims {
    fn from(skims: RoadNetworkSkims) -> Self {
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
type ODTravelTimeFunctions =
    HashMap<OriginalNodeId, HashMap<OriginalNodeId, Option<TTF<AnySeconds>>>>;

/// A memory allocation that holds the structures required during earliest arrival queries.
#[derive(Clone, Debug, Default)]
pub struct EAAllocation {
    ea_alloc: DefaultEarliestArrivalAllocation<AnySeconds>,
    candidate_map: HashMap<NodeIndex, (AnySeconds, AnySeconds)>,
}

/// A memory allocation for TCH profile queries.
#[derive(Clone, Debug, Default)]
struct TCHProfileAlloc {
    profile_alloc: DefaultTCHProfileAllocation<AnySeconds>,
    candidate_map: HashMap<NodeIndex, AnySeconds>,
}

impl TCHProfileAlloc {
    fn get_mut_variables(
        &mut self,
    ) -> (
        &mut DefaultTCHProfileAllocation<AnySeconds>,
        &mut HashMap<NodeIndex, AnySeconds>,
    ) {
        (&mut self.profile_alloc, &mut self.candidate_map)
    }
}
