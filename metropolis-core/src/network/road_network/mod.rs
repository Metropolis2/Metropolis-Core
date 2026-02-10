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

//! The part of the network dedicated to road vehicles.
pub mod parameters;
pub mod preprocess;
pub(crate) mod skim;
pub(crate) mod state;
pub mod vehicle;
pub(crate) mod weights;

use std::ops::{Deref, Index};
use std::sync::OnceLock;

use anyhow::{anyhow, bail, Context, Result};
use hashbrown::{HashMap, HashSet};
use log::{debug, warn};
use num_traits::{ConstZero, Pow, Zero};
use petgraph::graph::{edge_index, node_index, DiGraph, EdgeIndex, NodeIndex};
use tch::HierarchyOverlay;
use ttf::{TTFNum, TTF};

use self::parameters::AlgorithmType;
pub(crate) use self::preprocess::RoadNetworkPreprocessingData;
use self::preprocess::{ODPairsStruct, UniqueVehicles};
use self::skim::RoadNetworkSkim;
pub(crate) use self::skim::RoadNetworkSkims;
pub(crate) use self::state::RoadNetworkState;
use self::vehicle::{vehicle_index, Vehicle, VehicleIndex};
pub(crate) use self::weights::RoadNetworkWeights;
use crate::network::road_network::preprocess::unique_vehicle_index;
use crate::units::*;

static mut ROAD_NETWORK: OnceLock<RoadNetwork> = OnceLock::new();

/// Tries to initialize the global value of the road network.
///
/// Returns an Err if the value is already initialized.
#[allow(static_mut_refs)]
pub fn init(value: RoadNetwork) -> Result<()> {
    unsafe {
        let res = ROAD_NETWORK.set(value);
        if res.is_err() {
            bail!("Global road network can be set only once");
        }
    }
    Ok(())
}

/// Delete the global value of the road network.
pub fn drop() {
    unsafe {
        ROAD_NETWORK = OnceLock::new();
    }
}

/// Initializes the global value of the road network.
///
/// Modifies the value if it was already initialized.
pub fn replace(value: RoadNetwork) {
    drop();
    init(value).unwrap();
}

/// Returns `true` if the global road network is defined.
#[allow(static_mut_refs)]
pub fn is_init() -> bool {
    unsafe { ROAD_NETWORK.get().is_some() }
}

#[allow(static_mut_refs)]
fn read_global() -> &'static RoadNetwork {
    unsafe { ROAD_NETWORK.get().expect("Global road network is not set") }
}

fn graph() -> &'static RoadGraph {
    &read_global().graph
}

/// Returns the number of nodes in the graph.
pub(crate) fn nb_nodes() -> usize {
    graph().node_count()
}

/// Returns the number of edges in the graph.
pub(crate) fn nb_edges() -> usize {
    graph().edge_count()
}

/// Returns the RoadEdge corresponding to the given index
pub(crate) fn edge_by_index(edge_id: EdgeIndex) -> &'static RoadEdge {
    &graph()[edge_id]
}

/// Returns the original id of an edge given its simulation id.
pub(crate) fn original_edge_id_of(edge_id: EdgeIndex) -> OriginalEdgeId {
    *graph().rev_edge_map.get(&edge_id).expect("Invalid edge id")
}

/// Returns the EdgeIndex of an edge given its original id.
pub(crate) fn edge_index_of(original_id: OriginalEdgeId) -> EdgeIndex {
    *graph()
        .edge_map
        .get(&original_id)
        .expect("Invalid original edge id")
}

/// Returns an Iterator over the [OriginalEdgeId] of the graph.
pub(crate) fn iter_original_edge_ids() -> impl Iterator<Item = OriginalEdgeId> {
    graph().edge_map.keys().copied()
}

/// Returns an Iterator over the [OriginalNodeId] of the graph.
pub(crate) fn iter_original_node_ids() -> impl Iterator<Item = OriginalNodeId> {
    graph().node_map.keys().copied()
}

/// Returns the free-flow travel time for the given edge and vehicle.
pub(crate) fn free_flow_travel_time_of_edge(
    edge_id: OriginalEdgeId,
    vehicle: &Vehicle,
) -> NonNegativeSeconds {
    let edge_idx = edge_index_of(edge_id);
    let edge = edge_by_index(edge_idx);
    edge.get_free_flow_travel_time(vehicle)
}

/// Returns the free-flow travel time of traveling through the given route, with the given
/// vehicle.
pub(crate) fn route_free_flow_travel_time(
    route: impl Iterator<Item = EdgeIndex>,
    vehicle_id: MetroId,
) -> NonNegativeSeconds {
    let vehicle = vehicle_with_id(vehicle_id);
    route
        .map(|e| {
            graph()
                .edge_weight(e)
                .expect("The route is incompatible with the road network.")
                .get_free_flow_travel_time(vehicle)
        })
        .sum()
}

/// Returns the length of the given route.
pub(crate) fn route_length(route: impl Iterator<Item = EdgeIndex>) -> NonNegativeMeters {
    route
        .map(|e| {
            graph()
                .edge_weight(e)
                .expect("The route is incompatible with the road network.")
                .length
        })
        .sum()
}

/// Returns the length of the first route that is not part of the second route.
pub(crate) fn route_length_diff(
    first: impl Iterator<Item = OriginalEdgeId>,
    second: impl Iterator<Item = OriginalEdgeId>,
) -> NonNegativeMeters {
    let second_edges: HashSet<EdgeIndex> = second.map(edge_index_of).collect();
    first
        .filter_map(|original_id| {
            let edge_id = edge_index_of(original_id);
            if second_edges.contains(&edge_id) {
                None
            } else {
                Some(
                    graph()
                        .edge_weight(edge_id)
                        .expect("The route is incompatible with the road network.")
                        .length,
                )
            }
        })
        .sum::<NonNegativeMeters>()
}

fn vehicles() -> &'static [Vehicle] {
    &read_global().vehicles
}

fn vehicle_map() -> &'static HashMap<MetroId, VehicleIndex> {
    &read_global().vehicle_map
}

/// Returns the [VehicleIndex] corresponding to the given [MetroId].
///
/// **Panics** if there is no vehicle with the corresponding [MetroId].
fn vehicle_index_of(vehicle_id: MetroId) -> VehicleIndex {
    vehicle_map()[&vehicle_id]
}

/// Returns a reference to the [Vehicle] corresponding to the given [MetroId].
///
/// **Panics** if there is no vehicle with the corresponding [MetroId].
pub(crate) fn vehicle_with_id(vehicle_id: MetroId) -> &'static Vehicle {
    let vehicle_idx = vehicle_index_of(vehicle_id).index();
    let vehicle = &vehicles()[vehicle_idx];
    debug_assert_eq!(vehicle.id, vehicle_id);
    vehicle
}

/// Identifier of the node as given by the user.
pub(crate) type OriginalNodeId = MetroId;
/// Identifier of the edge as given by the user.
pub(crate) type OriginalEdgeId = MetroId;

/// A node of a road network.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct RoadNode {}

/// Speed-density function that can be used for the running part of edges.
///
/// A speed-density function gives the speed on an edge, as a function of the density of vehicle on
/// this edge.
#[derive(Clone, Debug, Default)]
pub enum SpeedDensityFunction {
    /// Vehicles always travel at free-flow speed.
    #[default]
    FreeFlow,
    /// Vehicles travel at free-flow speed when flow is below edge capacity.
    /// Then, speed is inversely proportional to flow.
    ///
    /// The parameter represents the capacity of each lane of the edge, in length unit per time
    /// unit.
    Bottleneck(MetersPerSecond),
    /// A speed-density function with three regimes: free flow, congested and traffic jam.
    ThreeRegimes(ThreeRegimesSpeedDensityFunction),
}

impl SpeedDensityFunction {
    fn from_values(
        function_type: Option<&str>,
        capacity: Option<f64>,
        min_density: Option<f64>,
        jam_density: Option<f64>,
        jam_speed: Option<f64>,
        beta: Option<f64>,
    ) -> Result<Self> {
        match function_type {
            Some("FreeFlow") | None => Ok(SpeedDensityFunction::FreeFlow),
            Some("Bottleneck") => {
                let capacity = MetersPerSecond::try_from(capacity.ok_or_else(|| {
                    anyhow!("Value `capacity` is mandatory when `type` is `\"Bottleneck\"`")
                })?)
                .context("Value `capacity` does not satisfy the constraints")?;
                Ok(SpeedDensityFunction::Bottleneck(capacity))
            }
            Some("ThreeRegimes") => {
                let min_density = NonNegativeNum::try_from(min_density.ok_or_else(|| {
                    anyhow!("Value `min_density` is mandatory when `type` is `\"ThreeRegimes\"`")
                })?)
                .context("Value `min_density` does not satisfy the constraints")?;
                let jam_density = NonNegativeNum::try_from(jam_density.ok_or_else(|| {
                    anyhow!("Value `jam_density` is mandatory when `type` is `\"ThreeRegimes\"`")
                })?)
                .context("Value `jam_density` does not satisfy the constraints")?;
                if jam_density < min_density {
                    bail!("Value `jam_density` cannot be smaller than value `min_density`")
                }
                let jam_speed = MetersPerSecond::try_from(jam_speed.ok_or_else(|| {
                    anyhow!("Value `jam_speed` is mandatory when `type` is `\"ThreeRegimes\"`")
                })?)
                .context("Value `jam_speed` does not satisfy the constraints")?;
                let beta = PositiveNum::try_from(beta.ok_or_else(|| {
                    anyhow!("Value `beta` is mandatory when `type` is `\"ThreeRegimes\"`")
                })?)
                .context("Value `beta` does not satisfy the constraints")?;
                Ok(SpeedDensityFunction::ThreeRegimes(
                    ThreeRegimesSpeedDensityFunction {
                        min_density,
                        jam_density,
                        jam_speed,
                        beta,
                    },
                ))
            }
            Some(s) => Err(anyhow!("Unknown type: {s}")),
        }
    }

    #[inline]
    fn get_speed(
        &self,
        base_speed: MetersPerSecond,
        occupied_length: NonNegativeMeters,
        total_length: NonNegativeMeters,
    ) -> MetersPerSecond {
        match self {
            SpeedDensityFunction::FreeFlow => base_speed,
            &SpeedDensityFunction::Bottleneck(capacity) => {
                // `capacity` is expressed in MetersPerSecond.
                // WARNING: The formula below is incorrect when there are vehicles with different
                // speeds.
                if occupied_length <= capacity * (total_length / base_speed)
                    || total_length.is_zero()
                {
                    base_speed
                } else {
                    // At this point, `occupied_length` and `total_length` cannot be zero.
                    total_length.assume_positive_unchecked()
                        / occupied_length.assume_positive_unchecked()
                        * capacity
                }
            }
            SpeedDensityFunction::ThreeRegimes(func) => {
                if total_length.is_zero() {
                    base_speed
                } else {
                    let density = occupied_length / total_length.assume_positive_unchecked();
                    func.get_speed(base_speed, density)
                }
            }
        }
    }
}

/// A speed-density function with three regimes.
///
/// The three regimes are:
///
/// 1. **Free-flow regime.** If density on the edge is smaller than `min_density`, travel time is
///    equal to free-flow travel time.
///
/// 2. **Congested regime.** If density on the edge is between `min_density` and `jam_density`,
///    speed is equal to `v = v0 * (1 - c) + jam_speed * c`, where `v0` is the free-flow speed and
///    `c = ((density - min_density) / (jam_density - min_density))^beta`.
///
/// 3. **Traffic jam.** If density on the edge is larger than `jam_density`, travel time is equal
///    to `tt = distance / jam_speed`.
#[derive(Clone, Debug)]
pub struct ThreeRegimesSpeedDensityFunction {
    /// Density on the edge below which the speed is equal to free-flow speed.
    min_density: NonNegativeNum,
    /// Density on the edge above which the speed is equal to jam speed.
    ///
    /// Must not be smaller than `min_density`.
    jam_density: NonNegativeNum,
    /// Speed at which the vehicle travel in case of traffic jam.
    jam_speed: MetersPerSecond,
    /// Parameter to compute the speed in the congested regime.
    beta: PositiveNum,
}

impl ThreeRegimesSpeedDensityFunction {
    /// Return the speed as a function of the edge length, vehicle speed and density of vehicles on
    /// the edge (i.e., the share of length occupied by a vehicle).
    fn get_speed(&self, ff_speed: MetersPerSecond, density: NonNegativeNum) -> MetersPerSecond {
        if density >= self.jam_density {
            // Traffic jam: all vehicles travel at the jam speed.
            Ord::min(self.jam_speed, ff_speed)
        } else if density > self.min_density {
            // Congestion.
            // `density` is larger than `min_density` so the following is safe.
            let num = PositiveNum::try_from(density - self.min_density).unwrap();
            // `jam_density` is larger than `min_density` so the following is safe.
            let den = PositiveNum::try_from(self.jam_density - self.min_density).unwrap();
            let coef: PositiveNum = (num / den).pow(self.beta);
            // `num` is smaller than `den` so the following is safe.
            let coef = ZeroOneNum::try_from(coef).unwrap();
            let speed = ff_speed * coef.one_minus() + self.jam_speed * coef;
            Ord::min(speed, ff_speed)
        } else {
            // Vehicle can travel at full speed.
            ff_speed
        }
    }
}

#[derive(Clone, Debug)]
struct EdgeFlow {
    current_flow: Flow,
    next_time: Option<NonNegativeSeconds>,
    values: Vec<(NonNegativeSeconds, Flow)>,
}

impl From<Flow> for EdgeFlow {
    fn from(value: Flow) -> Self {
        Self {
            current_flow: value,
            next_time: None,
            values: vec![],
        }
    }
}

impl TryFrom<Vec<(NonNegativeSeconds, Flow)>> for EdgeFlow {
    type Error = anyhow::Error;
    fn try_from(value: Vec<(NonNegativeSeconds, Flow)>) -> Result<Self> {
        if value.is_empty() {
            bail!("Cannot initialize `bottleneck_flow` from an empty list")
        }
        Ok(Self {
            current_flow: value[0].1,
            next_time: value.get(1).map(|&(t, _)| t),
            values: value,
        })
    }
}

impl EdgeFlow {
    #[inline]
    fn at(&mut self, current_time: NonNegativeSeconds) -> Flow {
        if self.next_time.map(|t| current_time >= t).unwrap_or(false) {
            self.next_time = None;
            for &(t, f) in self.values.iter() {
                if t > current_time {
                    self.next_time = Some(t);
                    break;
                }
                self.current_flow = f;
            }
        }
        self.current_flow
    }
}

/// An edge of a road network.
///
/// A RoadEdge is directed and connected to two [RoadNode]s.
///
/// A RoadEdge consists in three parts:
///
/// - A running part, where vehicles are driving at a speed computed from a speed-density function.
///
/// - A bottleneck part, where the exit flow of vehicle is limited by a given capacity.
///
/// - A pending part, where vehicles waiting for downstream edges to get free are pending.
#[derive(Clone, Debug)]
pub struct RoadEdge {
    /// Original id of the edge.
    id: OriginalEdgeId,
    /// The base speed of the edge.
    base_speed: MetersPerSecond,
    /// The length of the edge, from source node to target node.
    length: NonNegativeMeters,
    /// The number of lanes on the edge.
    lanes: Lanes,
    /// Speed-density function for the running part of the edge.
    speed_density: SpeedDensityFunction,
    /// Maximum flow of vehicle entering the edge (in PCE per second).
    bottleneck_flow: Option<EdgeFlow>,
    /// Constant travel time penalty for the runnning part of the edge.
    constant_travel_time: NonNegativeSeconds,
    /// If `true`, vehicles can overtaking each other at the exit bottleneck (if they have a
    /// different outgoing edge).
    overtaking: bool,
}

impl RoadEdge {
    /// Creates a new RoadEdge.
    #[expect(clippy::too_many_arguments)]
    pub fn new(
        id: i64,
        base_speed: MetersPerSecond,
        length: NonNegativeMeters,
        lanes: Lanes,
        speed_density: SpeedDensityFunction,
        bottleneck_flow: Option<Flow>,
        constant_travel_time: NonNegativeSeconds,
        overtaking: bool,
    ) -> Self {
        RoadEdge {
            id: MetroId::Integer(id),
            base_speed,
            length,
            lanes,
            speed_density,
            bottleneck_flow: bottleneck_flow.map(EdgeFlow::from),
            constant_travel_time,
            overtaking,
        }
    }

    /// Creates a new RoadEdge from deserialied values.
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn from_values(
        id: OriginalEdgeId,
        speed: Option<f64>,
        length: Option<f64>,
        lanes: Option<f64>,
        speed_density_type: Option<&str>,
        speed_density_capacity: Option<f64>,
        speed_density_min_density: Option<f64>,
        speed_density_jam_density: Option<f64>,
        speed_density_jam_speed: Option<f64>,
        speed_density_beta: Option<f64>,
        bottleneck_flow: Option<f64>,
        bottleneck_flows: Option<Vec<f64>>,
        bottleneck_times: Option<Vec<f64>>,
        constant_travel_time: Option<f64>,
        overtaking: Option<bool>,
    ) -> Result<Self> {
        let base_speed =
            MetersPerSecond::try_from(speed.ok_or_else(|| anyhow!("Value `speed` is mandatory"))?)
                .context("Value `speed` does not satisfy the constraints")?;
        let length = NonNegativeMeters::try_from(
            length.ok_or_else(|| anyhow!("Value `length` is mandatory"))?,
        )
        .context("Value `length` does not satisfy the constraints")?;
        let lanes = Lanes::try_from(lanes.unwrap_or(1.0))
            .context("Value `lanes` does not satisfy the constraints")?;
        let speed_density = SpeedDensityFunction::from_values(
            speed_density_type,
            speed_density_capacity,
            speed_density_min_density,
            speed_density_jam_density,
            speed_density_jam_speed,
            speed_density_beta,
        )
        .context("Failed to create speed-density function")?;
        let bottleneck_flow = if let Some(v) = bottleneck_flow {
            let cst_flow = Flow::try_from(v)
                .context("Value `bottleneck_flow` does not satisfy the constraints")?;
            Some(EdgeFlow::from(cst_flow))
        } else if let (Some(times), Some(flows)) = (bottleneck_times, bottleneck_flows) {
            let values: Vec<_> = times
                .into_iter()
                .zip(flows.into_iter())
                .map(|(t, f)| -> Result<(NonNegativeSeconds, Flow)> {
                    Ok((NonNegativeSeconds::try_from(t)?, Flow::try_from(f)?))
                })
                .collect::<Result<Vec<_>>>()?;
            Some(EdgeFlow::try_from(values)?)
        } else {
            None
        };
        let constant_travel_time =
            NonNegativeSeconds::try_from(constant_travel_time.unwrap_or(0.0))
                .context("Value `constant_travel_time` does not satisfy the constraints")?;
        let overtaking = overtaking.unwrap_or(true);
        Ok(RoadEdge {
            id,
            base_speed,
            length,
            lanes,
            speed_density,
            bottleneck_flow,
            constant_travel_time,
            overtaking,
        })
    }

    /// Returns `true` if vehicles are allowed to overtake each other at the edge's  exit
    /// bottleneck.
    pub(crate) fn overtaking_is_allowed(&self) -> bool {
        self.overtaking
    }

    /// Return the travel time for the running part of the edge for a given vehicle, given the
    /// total length of the vehicles currently on the edge.
    pub(crate) fn get_travel_time(
        &self,
        occupied_length: NonNegativeMeters,
        vehicle: &Vehicle,
    ) -> NonNegativeSeconds {
        let base_vehicle_speed = vehicle.get_speed(self.base_speed);
        let effective_speed =
            self.speed_density
                .get_speed(base_vehicle_speed, occupied_length, self.total_length());
        let variable_tt = self.length() / effective_speed;
        variable_tt + self.constant_travel_time
    }

    /// Return the free-flow travel time on the road for the given vehicle.
    pub(crate) fn get_free_flow_travel_time(&self, vehicle: &Vehicle) -> NonNegativeSeconds {
        self.get_travel_time(NonNegativeMeters::ZERO, vehicle)
    }

    /// Return the length of the edge, from source to target.
    pub(crate) const fn length(&self) -> NonNegativeMeters {
        self.length
    }

    /// Return the total length of the edge that can be occupied by vehicles, i.e., the length of
    /// the edge multiplied by the number of lanes.
    pub(crate) fn total_length(&self) -> NonNegativeMeters {
        self.length * self.lanes
    }
}

/// Description of the graph of a [RoadNetwork].
#[derive(Clone, Debug)]
pub(crate) struct RoadGraph {
    /// Directed graph of [RoadNode]s and [RoadEdge]s.
    graph: DiGraph<RoadNode, RoadEdge>,
    /// Mapping from original node id to simulation NodeIndex.
    node_map: HashMap<OriginalNodeId, NodeIndex>,
    /// Mapping from original edge id to simulation EdgeIndex.
    edge_map: HashMap<OriginalEdgeId, EdgeIndex>,
    /// Mapping from simulation EdgeIndex to original edge id.
    rev_edge_map: HashMap<EdgeIndex, OriginalEdgeId>,
}

impl RoadGraph {
    /// Creates a new RoadGraph from a Vec of edges.
    pub(crate) fn from_edges(edges: Vec<(OriginalNodeId, OriginalNodeId, RoadEdge)>) -> Self {
        // Check if there is any parallel edges.
        let node_pairs: HashSet<(OriginalNodeId, OriginalNodeId)> =
            edges.iter().map(|(s, t, _)| (*s, *t)).collect();
        if node_pairs.len() < edges.len() {
            warn!(
                "Found {} parallel edges (they are not supported)",
                edges.len() - node_pairs.len()
            );
        }
        // The nodes in the DiGraph need to be ordered from 0 to n-1 so we create a map
        // OriginalNodeIndex -> NodeIndex to re-index the nodes.
        let nodes: HashSet<OriginalNodeId> = edges
            .iter()
            .map(|(s, _, _)| s)
            .chain(edges.iter().map(|(_, t, _)| t))
            .copied()
            .collect();
        let node_map: HashMap<OriginalNodeId, NodeIndex> = nodes
            .into_iter()
            .enumerate()
            .map(|(i, id)| (id, node_index(i)))
            .collect();
        let edges: Vec<_> = edges
            .into_iter()
            .map(|(s, t, e)| (node_map[&s], node_map[&t], e))
            .collect();
        let edge_map: HashMap<_, _> = edges
            .iter()
            .map(|(_, _, e)| e.id)
            .enumerate()
            .map(|(i, id)| (id, edge_index(i)))
            .collect();
        let rev_edge_map: HashMap<_, _> = edges
            .iter()
            .map(|(_, _, e)| e.id)
            .enumerate()
            .map(|(i, id)| (edge_index(i), id))
            .collect();
        assert_eq!(edge_map.len(), edges.len(), "The edge ids are not unique");
        let graph = DiGraph::from_edges(edges);
        RoadGraph {
            graph,
            node_map,
            edge_map,
            rev_edge_map,
        }
    }
}

impl Deref for RoadGraph {
    type Target = DiGraph<RoadNode, RoadEdge>;

    fn deref(&self) -> &Self::Target {
        &self.graph
    }
}

/// Description of the vehicles and the road-network graph.
///
/// A RoadNetwork is composed of
///
/// - a [RoadGraph],
/// - a Vec of [Vehicle]s that can travel on the network.
#[derive(Clone, Debug)]
pub struct RoadNetwork {
    graph: RoadGraph,
    vehicles: Vec<Vehicle>,
    vehicle_map: HashMap<MetroId, VehicleIndex>,
}

impl RoadNetwork {
    /// Creates a new RoadNetwork from a Vec of edges and a Vec of [Vehicle].
    pub fn from_edges(
        edges: Vec<(OriginalNodeId, OriginalNodeId, RoadEdge)>,
        vehicles: Vec<Vehicle>,
    ) -> Self {
        let vehicle_map = vehicles
            .iter()
            .enumerate()
            .map(|(i, v)| (v.id, vehicle_index(i)))
            .collect();
        RoadNetwork {
            graph: RoadGraph::from_edges(edges),
            vehicles,
            vehicle_map,
        }
    }
}

/// Returns an empty [RoadNetworkState].
pub(crate) fn blank_state() -> RoadNetworkState {
    RoadNetworkState::init()
}

/// Compute and return the [RoadNetworkSkims] for the RoadNetwork, with the given
/// [RoadNetworkWeights], [RoadNetworkPreprocessingData] and [RoadNetworkParameters].
pub(crate) fn compute_skims(
    weights: &RoadNetworkWeights,
    preprocess_data: &RoadNetworkPreprocessingData,
) -> Result<RoadNetworkSkims> {
    compute_skims_inner(weights, &preprocess_data.od_pairs)
}

fn compute_skims_inner(
    weights: &RoadNetworkWeights,
    all_od_pairs: &[ODPairsStruct],
) -> Result<RoadNetworkSkims> {
    let mut skims = Vec::with_capacity(all_od_pairs.len());
    assert_eq!(
        all_od_pairs.len(),
        weights.len(),
        "The road-network weights are incompatible with the number of unique vehicles"
    );
    for uvehicle_id in (0..all_od_pairs.len()).map(unique_vehicle_index) {
        let od_pairs = &all_od_pairs[uvehicle_id.index()];
        if od_pairs.is_empty() {
            // There is no OD pair for this vehicle so we can skip it.
            skims.push(Default::default());
            continue;
        }
        let nb_breakpoints = weights[uvehicle_id].complexity();
        debug!("Total number of breakpoints: {nb_breakpoints}");
        // TODO: In some cases, it might be faster to re-use the same order from one iteration
        // to another.
        let weight_fn = |edge_id| {
            let original_id = original_edge_id_of(edge_id);
            weights
                .get(uvehicle_id, original_id)
                .cloned()
                .unwrap_or(TTF::Constant(AnySeconds::INFINITY))
        };
        let hierarchy =
            HierarchyOverlay::order(graph(), weight_fn, parameters::contraction().clone());
        debug!(
            "Number of edges in the Hierarchy Overlay: {}",
            hierarchy.edge_count()
        );
        debug!(
            "Complexity of the Hierarchy Overlay: {}",
            hierarchy.complexity()
        );
        let mut skim = RoadNetworkSkim::new(hierarchy, graph().node_map.clone());
        let use_intersect = match parameters::algorithm_type() {
            AlgorithmType::Intersect => true,
            AlgorithmType::Tch => false,
            AlgorithmType::Best => {
                let nb_unique_origins = od_pairs.unique_origins().len();
                let nb_unique_destinations = od_pairs.unique_destinations().len();
                // Use Intersect if unique origins and unique destinations both represent less
                // than 10 % of the graph nodes.
                std::cmp::max(nb_unique_origins, nb_unique_destinations) * 10 <= nb_nodes()
            }
        };
        if use_intersect {
            debug!("Finding most popular origins and destinations");
            let (popular_origins, popular_destinations) =
                od_pairs.popular_origins_and_destinations();
            debug!("Computing search spaces");
            let search_spaces = skim.get_search_spaces(popular_origins, popular_destinations);
            debug!(
                "Complexity of the search spaces: {}",
                search_spaces.complexity()
            );
            debug!("Computing profile queries");
            skim.pre_compute_profile_queries_intersect(od_pairs.pairs(), &search_spaces)?;
        } else {
            debug!("Computing profile queries");
            skim.pre_compute_profile_queries_tch(od_pairs.pairs())?;
        }
        debug!(
            "Complexity of the profile-query cache: {}",
            skim.profile_query_cache_complexity()
        );
        skims.push(Some(skim));
    }
    Ok(RoadNetworkSkims(skims))
}

/// Returns the [RoadNetworkPreprocessingData] for the given set of [agents](Agent), the given
/// [RoadNetworkParameters] and the period interval.
pub(crate) fn preprocess() -> Result<RoadNetworkPreprocessingData> {
    RoadNetworkPreprocessingData::preprocess()
}

/// Returns the free-flow travel time for each edge and each unique vehicle of the RoadNetwork.
pub fn free_flow_weights(preprocess_data: &RoadNetworkPreprocessingData) -> RoadNetworkWeights {
    free_flow_weights_inner(&preprocess_data.unique_vehicles)
}

fn free_flow_weights_inner(unique_vehicles: &UniqueVehicles) -> RoadNetworkWeights {
    let mut weights_vec = RoadNetworkWeights::with_capacity(unique_vehicles, nb_edges());
    for (uvehicle_id, vehicle) in unique_vehicles.iter_uniques(vehicles()) {
        let weights = &mut weights_vec[uvehicle_id];
        for edge in graph().edge_references() {
            if vehicle.can_access(edge.weight().id) {
                let tt = edge.weight().get_free_flow_travel_time(vehicle);
                weights
                    .weights_mut()
                    .insert(edge.weight().id, TTF::Constant(AnySeconds::from(tt)));
            }
        }
        weights.weights_mut().shrink_to_fit();
    }
    weights_vec
}

impl Index<MetroId> for RoadNetwork {
    type Output = Vehicle;
    fn index(&self, id: MetroId) -> &Self::Output {
        vehicle_with_id(id)
    }
}

impl Index<VehicleIndex> for RoadNetwork {
    type Output = Vehicle;
    fn index(&self, index: VehicleIndex) -> &Self::Output {
        &self.vehicles[index.index()]
    }
}

#[cfg(test)]
mod tests {
    use hashbrown::HashSet;

    use super::parameters::RoadNetworkParameters;
    use super::vehicle::SpeedFunction;
    use super::*;
    use crate::{
        parameters::Parameters,
        units::{Interval, NonNegativeSeconds, PCE},
    };

    #[test]
    fn get_travel_time_test() {
        let mut edge = RoadEdge {
            id: MetroId::Integer(1),
            base_speed: MetersPerSecond::new_unchecked(25.), // 50 km/h
            length: NonNegativeMeters::new_unchecked(1000.), // 1 km
            lanes: Lanes::new_unchecked(2.0),
            speed_density: SpeedDensityFunction::FreeFlow,
            bottleneck_flow: None,
            constant_travel_time: NonNegativeSeconds::new_unchecked(10.),
            overtaking: false,
        };
        let vehicle = Vehicle::new(
            1,
            NonNegativeMeters::new_unchecked(10.),
            PCE::new_unchecked(1.),
            SpeedFunction::Base,
            HashSet::new(),
            HashSet::new(),
        );
        // 1 km at 50 km/h is 40s.
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(0.), &vehicle,),
            NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.)
        );
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(4000.), &vehicle,),
            NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.)
        );

        edge.speed_density = SpeedDensityFunction::Bottleneck(MetersPerSecond::new_unchecked(10.));
        // The capacity is 2 veh. / s. (there are two lanes) and each veh. can travel through the
        // edge in 40 s. so the threshold is at 80 veh. on the edge = 800 m occupied.
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(0.), &vehicle,),
            NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.)
        );
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(800.), &vehicle,),
            NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.)
        );
        assert!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(801.), &vehicle,)
                > NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.)
        );
        // Double value of the threshold -> travel time is double.
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(1600.), &vehicle,),
            NonNegativeSeconds::new_unchecked(80.) + NonNegativeSeconds::new_unchecked(10.)
        );

        edge.speed_density = SpeedDensityFunction::ThreeRegimes(ThreeRegimesSpeedDensityFunction {
            min_density: NonNegativeNum::new_unchecked(0.2),
            jam_density: NonNegativeNum::new_unchecked(0.8),
            jam_speed: MetersPerSecond::new_unchecked(5.), // 18 km/h
            beta: PositiveNum::new_unchecked(2.),
        });
        // Free-flow regime.
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(0.), &vehicle,),
            NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.)
        );
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(400.), &vehicle,),
            NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.)
        );
        // Congested regime.
        let tt = edge.get_travel_time(NonNegativeMeters::new_unchecked(401.), &vehicle);
        assert!(
            tt > NonNegativeSeconds::new_unchecked(40.) + NonNegativeSeconds::new_unchecked(10.),
            "{tt:?} <= Time(50.)"
        );
        // With occupied length 800.0, density is 0.4.
        // coef = (.2 / .6)^2 = 1/9.
        // speed = 25 * (1 - 1/9) + 5 * 1/9 ~= 22.7777.
        // tt ~= 1000 / 22.7777 ~= 43.9024.
        // + constant tt 10.0.
        let tt = edge.get_travel_time(NonNegativeMeters::new_unchecked(800.), &vehicle);
        assert!(
            (Into::<f64>::into(tt) - 53.9024) < 1e-4,
            "{tt:?} != 53.9024"
        );
        // With occupied length 1200.0, density is 0.6.
        // coef = (.4 / .6)^2 = 4/9.
        // speed = 25 * (1 - 4/9) + 5 * 4/9 ~= 16.1111.
        // tt ~= 1000 / 16.1111 ~= 62.0690.
        // + constant tt 10.0.
        let tt = edge.get_travel_time(NonNegativeMeters::new_unchecked(1200.), &vehicle);
        assert!(
            (Into::<f64>::into(tt) - 72.0690).abs() < 1e-4,
            "{tt:?} != 72.0690"
        );
        // With occupied length 1599.99, density is close to 0.8.
        let tt = edge.get_travel_time(NonNegativeMeters::new_unchecked(1599.99999999), &vehicle);
        assert!(
            (Into::<f64>::into(tt) - 210.).abs() < 1e-4,
            "{tt:?} != 210.0"
        );
        // Traffic jam.
        // 1 km at 18 km/h is 200s.
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(1600.), &vehicle,),
            NonNegativeSeconds::new_unchecked(200.) + NonNegativeSeconds::new_unchecked(10.)
        );
        assert_eq!(
            edge.get_travel_time(NonNegativeMeters::new_unchecked(3200.), &vehicle,),
            NonNegativeSeconds::new_unchecked(200.) + NonNegativeSeconds::new_unchecked(10.)
        );
    }

    #[test]
    fn restricted_edges_test() {
        let rn_parameters = RoadNetworkParameters {
            recording_interval: PositiveSeconds::new_unchecked(1.0),
            ..Default::default()
        };
        let parameters = Parameters {
            road_network: Some(rn_parameters),
            period: Interval::new_unchecked(0., 100.),
            ..Default::default()
        };
        crate::parameters::init(parameters).unwrap();
        // Check that the node ids are still valid in the contracted graph.
        // Build a graph 0 -> 1 -> 2.
        // Edge 0 (0 -> 1) is forbidden.
        let edges = vec![
            (
                MetroId::Integer(0),
                MetroId::Integer(1),
                RoadEdge::new(
                    0,
                    MetersPerSecond::new_unchecked(1.0),
                    NonNegativeMeters::new_unchecked(1.0),
                    Lanes::new_unchecked(1.0),
                    SpeedDensityFunction::FreeFlow,
                    Some(Flow::new_unchecked(1.0)),
                    NonNegativeSeconds::new_unchecked(0.0),
                    true,
                ),
            ),
            (
                MetroId::Integer(1),
                MetroId::Integer(2),
                RoadEdge::new(
                    1,
                    MetersPerSecond::new_unchecked(1.0),
                    NonNegativeMeters::new_unchecked(1.0),
                    Lanes::new_unchecked(1.0),
                    SpeedDensityFunction::FreeFlow,
                    Some(Flow::new_unchecked(1.0)),
                    NonNegativeSeconds::new_unchecked(0.0),
                    true,
                ),
            ),
        ];
        let vehicle = Vehicle::new(
            1,
            NonNegativeMeters::new_unchecked(1.0),
            PCE::new_unchecked(1.0),
            SpeedFunction::Base,
            HashSet::new(),
            [MetroId::Integer(0)].into_iter().collect(),
        );
        let road_network = RoadNetwork::from_edges(edges, vec![vehicle.clone()]);
        init(road_network).unwrap();
        let weights = free_flow_weights_inner(&UniqueVehicles::init());
        debug_assert!(weights
            .get(unique_vehicle_index(0), MetroId::Integer(0))
            .is_none());
        let all_od_pairs = vec![ODPairsStruct::from_vec(vec![(
            MetroId::Integer(1),
            MetroId::Integer(2),
            true,
        )])];
        let skims = compute_skims_inner(&weights, &all_od_pairs).unwrap();
        let skim = skims[unique_vehicle_index(0)].as_ref().unwrap();
        assert_eq!(
            skim.profile_query(MetroId::Integer(1), MetroId::Integer(2))
                .unwrap(),
            Some(&TTF::Constant(AnySeconds::new_unchecked(1.0)))
        );
    }
}
