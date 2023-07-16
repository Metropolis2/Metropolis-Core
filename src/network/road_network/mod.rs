// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! The part of the network dedicated to road vehicles.
pub mod preprocess;
pub mod skim;
pub mod state;
pub mod vehicle;
mod weights;

use std::ops::{Deref, Index};

use anyhow::Result;
use hashbrown::{HashMap, HashSet};
use log::debug;
use num_traits::{Float, Zero};
use petgraph::graph::{edge_index, node_index, DiGraph, EdgeIndex, NodeIndex};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use tch::{ContractionParameters, HierarchyOverlay};
use ttf::{TTFNum, TTF};

pub use self::preprocess::RoadNetworkPreprocessingData;
use self::preprocess::{ODPairs, UniqueVehicles};
use self::skim::RoadNetworkSkim;
pub use self::skim::RoadNetworkSkims;
pub use self::state::RoadNetworkState;
use self::vehicle::{vehicle_index, Vehicle, VehicleIndex};
pub use self::weights::RoadNetworkWeights;
use crate::agent::Agent;
use crate::parameters::Parameters;
use crate::serialization::DeserRoadGraph;
use crate::units::{Flow, Length, Speed, Time};

/// Index of the node as given by the user.
pub type OriginalNodeIndex = u64;
/// Index of the edge as given by the user.
pub type OriginalEdgeIndex = u64;

/// A node of a road network.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize, JsonSchema)]
pub struct RoadNode {}

/// Speed-density function that can be used for the running part of edges.
///
/// A speed-density function gives the speed on an edge, as a function of the density of vehicle on
/// this edge.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum SpeedDensityFunction<T> {
    /// Vehicles always travel at free-flow speed.
    FreeFlow,
    /// Vehicles travel at free-flow speed when flow is below edge capacity.
    /// Then, speed is inversely proportional to flow.
    ///
    /// The parameter represents the capacity of each lane of the edge, in length unit per time
    /// unit.
    Bottleneck(T),
    /// A speed-density function with three regimes: free flow, congested and traffic jam.
    ThreeRegimes(ThreeRegimesSpeedDensityFunction<T>),
}

impl<T> Default for SpeedDensityFunction<T> {
    fn default() -> Self {
        Self::FreeFlow
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
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub struct ThreeRegimesSpeedDensityFunction<T> {
    /// Density on the edge (between `0.0` and `1.0`) below which the speed is equal to free-flow
    /// speed.
    min_density: T,
    /// Density on the edge (between `0.0` and `1.0`) above which the speed is equal to jam speed.
    jam_density: T,
    /// Speed at which the vehicle travel in case of traffic jam.
    jam_speed: Speed<T>,
    /// Parameter to compute the speed in the congested regime.
    beta: T,
}

impl<T> ThreeRegimesSpeedDensityFunction<T> {
    /// Creates a new ThreeRegimesSpeedDensityFunction.
    pub const fn new(min_density: T, jam_density: T, jam_speed: Speed<T>, beta: T) -> Self {
        ThreeRegimesSpeedDensityFunction {
            min_density,
            jam_density,
            jam_speed,
            beta,
        }
    }
}

impl<T: TTFNum> ThreeRegimesSpeedDensityFunction<T> {
    /// Return the speed as a function of the edge length, vehicle speed and density of vehicles on
    /// the edge (i.e., the share of length occupied by a vehicle).
    fn get_speed(&self, ff_speed: Speed<T>, density: T) -> Speed<T> {
        if density >= self.jam_density {
            // Traffic jam: all vehicles travel at the jam speed.
            Float::min(self.jam_speed, ff_speed)
        } else if density >= self.min_density {
            // Congestion.
            let coef = ((density - self.min_density) / (self.jam_density - self.min_density))
                .powf(self.beta);
            let speed = Speed(ff_speed.0 * (T::one() - coef) + self.jam_speed.0 * coef);
            Float::min(speed, ff_speed)
        } else {
            // Vehicle can travel at full speed.
            ff_speed
        }
    }
}

fn default_flow<T: TTFNum>() -> Flow<T> {
    Flow::infinity()
}

fn default_flow_schema() -> String {
    "Infinity".to_owned()
}

fn default_time_schema() -> String {
    "0".to_owned()
}

const fn default_lanes() -> u8 {
    1
}

const fn default_is_true() -> bool {
    true
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
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[schemars(title = "Road Edge")]
#[schemars(description = "An edge of a road network that connects two nodes.")]
#[schemars(example = "crate::schema::example_road_edge")]
pub struct RoadEdge<T> {
    /// Original id of the edge.
    id: OriginalEdgeIndex,
    /// The base speed of the edge.
    #[validate(range(min = 0.0))]
    base_speed: Speed<T>,
    /// The length of the edge, from source node to target node.
    #[validate(range(min = 0.0))]
    length: Length<T>,
    /// The number of lanes on the edge.
    #[serde(default = "default_lanes")]
    #[validate(range(min = 1))]
    lanes: u8,
    /// Speed-density function for the running part of the edge.
    #[serde(default)]
    speed_density: SpeedDensityFunction<T>,
    /// Maximum flow of vehicle entering the edge (in PCE per second).
    #[serde(default = "default_flow")]
    #[schemars(default = "default_flow_schema")]
    #[serde(alias = "bottleneck_inflow")]
    #[serde(alias = "bottleneck_outflow")]
    bottleneck_flow: Flow<T>,
    /// Constant travel time penalty for the runnning part of the edge.
    #[serde(default = "Time::zero")]
    #[schemars(default = "default_time_schema")]
    constant_travel_time: Time<T>,
    /// If `true`, vehicles can overtaking each other at the exit bottleneck (if they have a
    /// different outgoing edge).
    #[serde(default = "default_is_true")]
    overtaking: bool,
}

impl<T: TTFNum> RoadEdge<T> {
    /// Creates a new RoadEdge.
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        id: OriginalEdgeIndex,
        base_speed: Speed<T>,
        length: Length<T>,
        lanes: u8,
        speed_density: SpeedDensityFunction<T>,
        bottleneck_flow: Flow<T>,
        constant_travel_time: Time<T>,
        overtaking: bool,
    ) -> Self {
        RoadEdge {
            id,
            base_speed,
            length,
            lanes,
            speed_density,
            bottleneck_flow,
            constant_travel_time,
            overtaking,
        }
    }

    /// Returns `true` if vehicles are allowed to overtake each other at the edge's  exit
    /// bottleneck.
    pub fn overtaking_is_allowed(&self) -> bool {
        self.overtaking
    }

    /// Return the travel time for the running part of the edge for a given vehicle, given the
    /// total length of the vehicles currently on the edge.
    pub fn get_travel_time(&self, occupied_length: Length<T>, vehicle: &Vehicle<T>) -> Time<T> {
        let vehicle_speed = vehicle.get_speed(self.base_speed);
        let variable_tt = match &self.speed_density {
            SpeedDensityFunction::FreeFlow => self.length / vehicle_speed,
            &SpeedDensityFunction::Bottleneck(capacity) => {
                // `capacity` is expressed in Length / Time.
                // WARNING: The formula below is incorrect when there are vehicles with different
                // speeds.
                if occupied_length.0 <= capacity * (self.total_length() / self.base_speed).0 {
                    self.length / vehicle_speed
                } else {
                    Time(occupied_length.0 / (capacity * T::from_u8(self.lanes).unwrap()))
                }
            }
            SpeedDensityFunction::ThreeRegimes(func) => {
                let density = (occupied_length / self.total_length()).0;
                let speed = func.get_speed(vehicle_speed, density);
                self.length / speed
            }
        };
        variable_tt + self.constant_travel_time
    }

    /// Return the free-flow travel time on the road for the given vehicle.
    #[inline]
    pub fn get_free_flow_travel_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.get_travel_time(Length::zero(), vehicle)
    }

    /// Return the length of the edge, from source to target.
    pub const fn length(&self) -> Length<T> {
        self.length
    }

    /// Return the total length of the edge that can be occupied by vehicles, i.e., the length of
    /// the edge multiplied by the number of lanes.
    pub fn total_length(&self) -> Length<T> {
        self.length * self.lanes
    }

    /// Return the effective bottleneck flow of the edge, i.e., the flow for all the lanes.
    pub fn get_effective_flow(&self) -> Flow<T> {
        self.bottleneck_flow * self.lanes
    }
}

/// Description of the graph of a [RoadNetwork].
#[derive(Clone, Debug, Serialize)]
pub struct RoadGraph<T> {
    /// Directed graph of [RoadNode]s and [RoadEdge]s.
    graph: DiGraph<RoadNode, RoadEdge<T>>,
    /// Mapping from original node id to simulation NodeIndex.
    node_map: HashMap<OriginalNodeIndex, NodeIndex>,
    /// Mapping from original edge id to simulation EdgeIndex.
    edge_map: HashMap<OriginalEdgeIndex, EdgeIndex>,
    /// Mapping from simulation EdgeIndex to original edge id.
    rev_edge_map: HashMap<EdgeIndex, OriginalEdgeIndex>,
}

impl<T> RoadGraph<T> {
    /// Creates a new RoadGraph.
    pub const fn new(
        graph: DiGraph<RoadNode, RoadEdge<T>>,
        node_map: HashMap<OriginalNodeIndex, NodeIndex>,
        edge_map: HashMap<OriginalEdgeIndex, EdgeIndex>,
        rev_edge_map: HashMap<EdgeIndex, OriginalEdgeIndex>,
    ) -> Self {
        Self {
            graph,
            node_map,
            edge_map,
            rev_edge_map,
        }
    }

    /// Creates a new RoadGraph from a Vec of edges.
    pub fn from_edges(edges: Vec<(OriginalNodeIndex, OriginalNodeIndex, RoadEdge<T>)>) -> Self {
        // The nodes in the DiGraph need to be ordered from 0 to n-1 so we create a map
        // OriginalNodeIndex -> NodeIndex to re-index the nodes.
        let node_map: HashMap<OriginalNodeIndex, NodeIndex> = edges
            .iter()
            .map(|(s, _, _)| s)
            .chain(edges.iter().map(|(_, t, _)| t))
            .enumerate()
            .map(|(i, &id)| (id, node_index(i)))
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

impl<T> Deref for RoadGraph<T> {
    type Target = DiGraph<RoadNode, RoadEdge<T>>;

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
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[schemars(title = "Road Network")]
#[schemars(description = "Description of the vehicles and the road-network graph.")]
pub struct RoadNetwork<T> {
    #[schemars(with = "DeserRoadGraph<T>")]
    graph: RoadGraph<T>,
    #[validate(length(min = 1))]
    vehicles: Vec<Vehicle<T>>,
}

impl<T> RoadNetwork<T> {
    /// Creates a new RoadNetwork.
    pub fn new(
        graph: DiGraph<RoadNode, RoadEdge<T>>,
        node_map: HashMap<OriginalNodeIndex, NodeIndex>,
        edge_map: HashMap<OriginalEdgeIndex, EdgeIndex>,
        rev_edge_map: HashMap<EdgeIndex, OriginalEdgeIndex>,
        vehicles: Vec<Vehicle<T>>,
    ) -> Self {
        RoadNetwork {
            graph: RoadGraph::new(graph, node_map, edge_map, rev_edge_map),
            vehicles,
        }
    }

    /// Creates a new RoadNetwork from a Vec of edges and a Vec of [Vehicle].
    pub fn from_edges(
        edges: Vec<(OriginalNodeIndex, OriginalNodeIndex, RoadEdge<T>)>,
        vehicles: Vec<Vehicle<T>>,
    ) -> Self {
        RoadNetwork {
            graph: RoadGraph::from_edges(edges),
            vehicles,
        }
    }

    /// Return a reference to the [DiGraph] of the [RoadNetwork].
    pub fn get_graph(&self) -> &DiGraph<RoadNode, RoadEdge<T>> {
        &self.graph
    }

    /// Return the source and target of a given edge.
    ///
    /// Return `None` if there is no edge with the given [EdgeIndex].
    pub fn get_endpoints(&self, edge: EdgeIndex) -> Option<(NodeIndex, NodeIndex)> {
        self.graph.edge_endpoints(edge)
    }

    /// Return an Iterator over the [Vehicle]s of the network, together with their
    /// [VehicleIndex].
    pub fn iter_vehicles(&self) -> impl Iterator<Item = (VehicleIndex, &Vehicle<T>)> {
        self.vehicles
            .iter()
            .enumerate()
            .map(|(i, v)| (vehicle_index(i), v))
    }

    /// Returns the EdgeIndex of an edge given its original id.
    pub fn edge_id_of(&self, original_id: OriginalEdgeIndex) -> EdgeIndex {
        *self
            .graph
            .edge_map
            .get(&original_id)
            .expect("Invalid original edge id")
    }

    /// Returns the original id of an edge given its simulation id.
    pub fn original_edge_id_of(&self, edge_id: EdgeIndex) -> OriginalEdgeIndex {
        *self
            .graph
            .rev_edge_map
            .get(&edge_id)
            .expect("Invalid edge id")
    }
}

impl<T: TTFNum> RoadNetwork<T> {
    /// Returns an empty [RoadNetworkState].
    pub fn get_blank_state(&self, parameters: &Parameters<T>) -> RoadNetworkState<T> {
        let road_network_parameters = parameters
            .network
            .road_network
            .as_ref()
            .expect("Cannot create RoadNetworkState with no RoadNetworkParameters");
        RoadNetworkState::from_network(
            self,
            parameters.period,
            road_network_parameters.recording_interval,
            road_network_parameters.spillback,
            road_network_parameters.max_pending_duration,
        )
    }

    /// Returns the [RoadNetworkPreprocessingData] for the given set of [agents](Agent), the given
    /// [RoadNetworkParameters] and the period interval.
    pub fn preprocess(
        &self,
        agents: &[Agent<T>],
        parameters: &RoadNetworkParameters<T>,
    ) -> Result<RoadNetworkPreprocessingData<T>> {
        RoadNetworkPreprocessingData::preprocess(self, agents, parameters)
    }

    /// Compute and return the [RoadNetworkSkims] for the RoadNetwork, with the given
    /// [RoadNetworkWeights], [RoadNetworkPreprocessingData] and [RoadNetworkParameters].
    pub fn compute_skims(
        &self,
        weights: &RoadNetworkWeights<T>,
        preprocess_data: &RoadNetworkPreprocessingData<T>,
        parameters: &RoadNetworkParameters<T>,
    ) -> Result<RoadNetworkSkims<T>> {
        self.compute_skims_inner(weights, &preprocess_data.od_pairs, parameters)
    }

    fn compute_skims_inner(
        &self,
        weights: &RoadNetworkWeights<T>,
        all_od_pairs: &Vec<ODPairs>,
        parameters: &RoadNetworkParameters<T>,
    ) -> Result<RoadNetworkSkims<T>> {
        let mut skims = Vec::with_capacity(all_od_pairs.len());
        assert_eq!(
            all_od_pairs.len(),
            weights.len(),
            "The road-network weights are incomatible with the numbe of unique vehicles"
        );
        for uvehicle_id in 0..all_od_pairs.len() {
            let od_pairs = &all_od_pairs[uvehicle_id];
            if od_pairs.is_empty() {
                // No one is using this vehicle so there is no need to compute the skims.
                skims.push(None);
            }
            let nb_breakpoints: usize = weights[uvehicle_id].values().map(|w| w.complexity()).sum();
            debug!("Total number of breakpoints: {nb_breakpoints}");
            // TODO: In some cases, it might be faster to re-use the same order from one iteration
            // to another.
            let weight_fn = |edge_id| {
                let original_id = self.original_edge_id_of(edge_id);
                weights[(uvehicle_id, original_id)].clone()
            };
            let hierarchy =
                HierarchyOverlay::order(&self.graph, weight_fn, parameters.contraction.clone());
            debug!(
                "Number of edges in the Hierarchy Overlay: {}",
                hierarchy.edge_count()
            );
            debug!(
                "Complexity of the Hierarchy Overlay: {}",
                hierarchy.complexity()
            );
            let mut skim = RoadNetworkSkim::new(hierarchy, self.graph.node_map.clone());
            let use_intersect = match parameters.algorithm_type {
                AlgorithmType::Intersect => true,
                AlgorithmType::Tch => false,
                AlgorithmType::Best => {
                    let nb_unique_origins = od_pairs.unique_origins().len();
                    let nb_unique_destinations = od_pairs.unique_destinations().len();
                    // Use Intersect if unique origins and unique destinations both represent less
                    // than 10 % of the graph nodes.
                    std::cmp::max(nb_unique_origins, nb_unique_destinations) * 10
                        <= self.graph.node_count()
                }
            };
            if use_intersect {
                debug!("Computing search spaces");
                let search_spaces = skim
                    .get_search_spaces(od_pairs.unique_origins(), od_pairs.unique_destinations());
                debug!("Computing profile queries");
                skim.pre_compute_profile_queries_intersect(od_pairs.pairs(), &search_spaces)?;
            } else {
                debug!("Computing profile queries");
                skim.pre_compute_profile_queries_tch(od_pairs.pairs())?;
            }
            skims.push(Some(skim));
        }
        Ok(RoadNetworkSkims(skims))
    }

    /// Returns the free-flow travel time for each edge and each unique vehicle of the RoadNetwork.
    pub fn get_free_flow_weights(
        &self,
        preprocess_data: &RoadNetworkPreprocessingData<T>,
    ) -> RoadNetworkWeights<T> {
        self.get_free_flow_weights_inner(&preprocess_data.unique_vehicles)
    }

    fn get_free_flow_weights_inner(
        &self,
        unique_vehicles: &UniqueVehicles,
    ) -> RoadNetworkWeights<T> {
        let mut weights_vec =
            RoadNetworkWeights::with_capacity(unique_vehicles.len(), self.graph.edge_count());
        for (uvehicle_id, vehicle) in unique_vehicles.iter_uniques(&self.vehicles) {
            let weights = &mut weights_vec[uvehicle_id];
            for edge in self.graph.edge_references() {
                if vehicle.can_access(edge.weight().id) {
                    let tt = edge.weight().get_free_flow_travel_time(vehicle);
                    weights.insert(edge.weight().id, TTF::Constant(tt));
                } else {
                    weights.insert(edge.weight().id, TTF::Constant(Time::infinity()));
                }
            }
        }
        weights_vec
    }

    /// Returns the free-flow travel time of traveling through the given route, with the given
    /// vehicle.
    pub fn route_free_flow_travel_time(
        &self,
        route: impl Iterator<Item = EdgeIndex>,
        vehicle_id: VehicleIndex,
    ) -> Time<T> {
        let vehicle = &self[vehicle_id];
        route
            .map(|e| {
                self.graph
                    .edge_weight(e)
                    .expect("The route is incompatible with the road network.")
                    .get_free_flow_travel_time(vehicle)
            })
            .sum()
    }

    /// Returns the length of the given route.
    pub fn route_length(&self, route: impl Iterator<Item = EdgeIndex>) -> Length<T> {
        route
            .map(|e| {
                self.graph
                    .edge_weight(e)
                    .expect("The route is incompatible with the road network.")
                    .length
            })
            .sum()
    }

    /// Returns the length of the first route that is not part of the second route.
    pub fn route_length_diff(
        &self,
        first: impl Iterator<Item = OriginalEdgeIndex>,
        second: impl Iterator<Item = OriginalEdgeIndex>,
    ) -> Length<T> {
        let second_edges: HashSet<EdgeIndex> = second
            .map(|original_id| self.edge_id_of(original_id))
            .collect();
        first
            .filter_map(|original_id| {
                let edge_id = self.edge_id_of(original_id);
                if second_edges.contains(&edge_id) {
                    None
                } else {
                    Some(
                        self.graph
                            .edge_weight(edge_id)
                            .expect("The route is incompatible with the road network.")
                            .length,
                    )
                }
            })
            .sum::<Length<T>>()
    }
}

impl<T> Index<VehicleIndex> for RoadNetwork<T> {
    type Output = Vehicle<T>;
    fn index(&self, index: VehicleIndex) -> &Self::Output {
        &self.vehicles[index.index()]
    }
}

/// Algorithm type to use for the profile queries.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub enum AlgorithmType {
    /// Try to guess which algorithm will be the fastest.
    #[default]
    Best,
    /// Time-dependent contraction hierarchies (TCH): long pre-processing time, fast queries.
    #[serde(rename = "TCH")]
    Tch,
    /// Many-to-many TCH: Longest pre-processing time, fastest queries.
    Intersect,
}

/// Set of parameters related to a [RoadNetwork].
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[schemars(title = "Road Network Parameters")]
#[schemars(description = "Set of parameters related to a road network.")]
pub struct RoadNetworkParameters<T> {
    /// [ContractionParameters] controlling how a [HierarchyOverlay] is built from a [RoadNetwork].
    #[serde(default)]
    #[schemars(
        description = "Parameters controlling how a hierarchy overlay is built from a road network graph."
    )]
    pub contraction: ContractionParameters,
    /// Time interval for which travel times are recorded at the edge level during the simulation.
    pub recording_interval: Time<T>,
    #[serde(default)]
    #[schemars(default = "default_time_schema")]
    /// Approximation bound in seconds, used to simplify the travel-time functions when the
    /// difference between the maximum and the minimum travel time is smaller than this bound.
    pub approximation_bound: Time<T>,
    /// If `true` the total headways of vehicles on each edge of the road network is limited by the
    /// total length of the edges.
    #[serde(default = "default_is_true")]
    pub spillback: bool,
    /// Maximum amount of time a vehicle can be pending to enter the next edge.
    pub max_pending_duration: Time<T>,
    /// Algorithm type to use when computing the origin-destination travel-time functions.
    /// Possible values are: "Best" (default), "Intersect" and "TCH".
    ///
    /// Intersect is recommanded when the number of unique origins and destinations represent a
    /// relatively small part of the total number of nodes in the graph.
    #[serde(default)]
    pub algorithm_type: AlgorithmType,
}

#[cfg(test)]
mod tests {
    use hashbrown::HashSet;

    use super::vehicle::SpeedFunction;
    use super::*;
    use crate::units::PCE;

    #[test]
    fn get_travel_time_test() {
        let mut edge = RoadEdge {
            id: 1,
            base_speed: Speed(25.), // 50 km/h
            length: Length(1000.),  // 1 km
            lanes: 2,
            speed_density: SpeedDensityFunction::FreeFlow,
            bottleneck_flow: Flow(f64::INFINITY),
            constant_travel_time: Time(10.),
            overtaking: false,
        };
        let vehicle = Vehicle::new(
            Length(10.),
            PCE(1.),
            SpeedFunction::Base,
            HashSet::new(),
            HashSet::new(),
        );
        // 1 km at 50 km/h is 40s.
        assert_eq!(
            edge.get_travel_time(Length(0.), &vehicle),
            Time(40.) + Time(10.)
        );
        assert_eq!(
            edge.get_travel_time(Length(4000.), &vehicle),
            Time(40.) + Time(10.)
        );

        edge.speed_density = SpeedDensityFunction::Bottleneck(10.);
        // The capacity is 2 veh. / s. (there are two lanes) and each veh. can travel through the
        // edge in 40 s. so the threshold is at 80 veh. on the edge = 800 m occupied.
        assert_eq!(
            edge.get_travel_time(Length(0.), &vehicle),
            Time(40.) + Time(10.)
        );
        assert_eq!(
            edge.get_travel_time(Length(800.), &vehicle),
            Time(40.) + Time(10.)
        );
        assert!(edge.get_travel_time(Length(801.), &vehicle) > Time(40.) + Time(10.));
        // Double value of the threshold -> travel time is double.
        assert_eq!(
            edge.get_travel_time(Length(1600.), &vehicle),
            Time(80.) + Time(10.)
        );

        edge.speed_density = SpeedDensityFunction::ThreeRegimes(ThreeRegimesSpeedDensityFunction {
            min_density: 0.2,
            jam_density: 0.8,
            jam_speed: Speed(5.), // 18 km/h
            beta: 2.,
        });
        // Free-flow regime.
        assert_eq!(
            edge.get_travel_time(Length(0.), &vehicle),
            Time(40.) + Time(10.)
        );
        assert_eq!(
            edge.get_travel_time(Length(400.), &vehicle),
            Time(40.) + Time(10.)
        );
        // Congested regime.
        let tt = edge.get_travel_time(Length(401.), &vehicle);
        assert!(tt > Time(40.) + Time(10.), "{tt:?} <= Time(50.)");
        // With occupied length 800.0, density is 0.4.
        // coef = (.2 / .6)^2 = 1/9.
        // speed = 25 * (1 - 1/9) + 5 * 1/9 ~= 22.7777.
        // tt ~= 1000 / 22.7777 ~= 43.9024.
        // + constant tt 10.0.
        let tt = edge.get_travel_time(Length(800.), &vehicle);
        assert!((tt.0 - 53.9024) < 1e-4, "{tt:?} != 53.9024");
        // With occupied length 1200.0, density is 0.6.
        // coef = (.4 / .6)^2 = 4/9.
        // speed = 25 * (1 - 4/9) + 5 * 4/9 ~= 16.1111.
        // tt ~= 1000 / 16.1111 ~= 62.0690.
        // + constant tt 10.0.
        let tt = edge.get_travel_time(Length(1200.), &vehicle);
        assert!((tt.0 - 72.0690).abs() < 1e-4, "{tt:?} != 72.0690");
        // With occupied length 1599.99, density is close to 0.8.
        let tt = edge.get_travel_time(Length(1599.99999999), &vehicle);
        assert!((tt.0 - 210.).abs() < 1e-4, "{tt:?} != 210.0");
        // Traffic jam.
        // 1 km at 18 km/h is 200s.
        assert_eq!(
            edge.get_travel_time(Length(1600.), &vehicle),
            Time(200.) + Time(10.)
        );
        assert_eq!(
            edge.get_travel_time(Length(3200.), &vehicle),
            Time(200.) + Time(10.)
        );
    }

    #[test]
    fn restricted_edges_test() {
        // Check that the node ids are still valid in the contracted graph.
        // Build a graph 0 -> 1 -> 2.
        // Edge 0 (0 -> 1) is forbidden.
        let edges = vec![
            (
                0,
                1,
                RoadEdge::new(
                    0,
                    Speed(1.0),
                    Length(1.0),
                    1,
                    SpeedDensityFunction::FreeFlow,
                    Flow(1.0),
                    Time(0.0),
                    true,
                ),
            ),
            (
                1,
                2,
                RoadEdge::new(
                    1,
                    Speed(1.0),
                    Length(1.0),
                    1,
                    SpeedDensityFunction::FreeFlow,
                    Flow(1.0),
                    Time(0.0),
                    true,
                ),
            ),
        ];
        let vehicle = Vehicle::new(
            Length(1.0),
            PCE(1.0),
            SpeedFunction::Base,
            HashSet::new(),
            [0].into_iter().collect(),
        );
        let network = RoadNetwork::from_edges(edges, vec![vehicle.clone()]);
        let weights =
            network.get_free_flow_weights_inner(&UniqueVehicles::from_vehicles(&[vehicle]));
        debug_assert!(weights[(0, 0)].get_min().is_infinite());
        let all_od_pairs = vec![ODPairs::from_vec(vec![(1, 2)])];
        let parameters = RoadNetworkParameters {
            contraction: Default::default(),
            recording_interval: Time(1.0),
            approximation_bound: Time(0.0),
            spillback: false,
            max_pending_duration: Time::zero(),
            algorithm_type: AlgorithmType::Intersect,
        };
        let skims = network
            .compute_skims_inner(&weights, &all_od_pairs, &parameters)
            .unwrap();
        let skim = skims[0].as_ref().unwrap();
        assert_eq!(
            skim.profile_query(1, 2).unwrap(),
            Some(&TTF::Constant(Time(1.0)))
        );
    }
}
