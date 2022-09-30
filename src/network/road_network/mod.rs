// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! The part of the network dedicated to road vehicles.
pub mod skim;
pub mod state;
pub mod vehicle;
pub mod weights;

use crate::agent::Agent;
use crate::mode::Mode;
use crate::serialization::DeserRoadGraph;
use crate::units::{Length, Outflow, Speed, Time};
use skim::{RoadNetworkSkim, RoadNetworkSkims};
use state::RoadNetworkState;
use vehicle::{vehicle_index, Vehicle, VehicleIndex};
use weights::RoadNetworkWeights;

use anyhow::Result;
use hashbrown::{HashMap, HashSet};
use log::debug;
use num_traits::{Float, Zero};
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use std::ops::{Deref, Index, IndexMut};
use tch::{ContractionParameters, HierarchyOverlay};
use ttf::{TTFNum, TTFSimplification, TTF};

/// A node of a road network.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize, JsonSchema)]
pub struct RoadNode {}

/// Speed-density function that can be used for the running part of edges.
///
/// A speed-density function gives the speed on an edge, as a function of the density of vehicle on
/// this edge.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "values")]
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
    pub fn new(min_density: T, jam_density: T, jam_speed: Speed<T>, beta: T) -> Self {
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
            TTFNum::min(&self.jam_speed, &ff_speed)
        } else if density >= self.min_density {
            // Congestion.
            let coef = ((density - self.min_density) / (self.jam_density - self.min_density))
                .powf(self.beta);
            let speed = Speed(ff_speed.0 * (T::one() - coef) + self.jam_speed.0 * coef);
            TTFNum::min(&speed, &ff_speed)
        } else {
            // Vehicle can travel at full speed.
            ff_speed
        }
    }
}

fn default_outflow<T: TTFNum>() -> Outflow<T> {
    Outflow::infinity()
}

fn default_outflow_schema() -> String {
    "Infinity".to_owned()
}

fn default_lanes() -> u8 {
    1
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
    /// Maximum outflow of vehicle at the end of the edge.
    #[serde(default = "default_outflow")]
    #[schemars(default = "default_outflow_schema")]
    bottleneck_outflow: Outflow<T>,
}

impl<T: TTFNum> RoadEdge<T> {
    /// Creates a new RoadEdge.
    pub fn new(
        base_speed: Speed<T>,
        length: Length<T>,
        lanes: u8,
        speed_density: SpeedDensityFunction<T>,
        bottleneck_outflow: Outflow<T>,
    ) -> Self {
        RoadEdge {
            base_speed,
            length,
            lanes,
            speed_density,
            bottleneck_outflow,
        }
    }

    /// Return the travel time for the running part of the edge for a given vehicle, given the
    /// total length of the vehicles currently on the edge.
    pub fn get_travel_time(&self, occupied_length: Length<T>, vehicle: &Vehicle<T>) -> Time<T> {
        let vehicle_speed = vehicle.get_speed(self.base_speed);
        match &self.speed_density {
            SpeedDensityFunction::FreeFlow => self.length / vehicle_speed,
            &SpeedDensityFunction::Bottleneck(outflow) => {
                // `outflow` is expressed in Length / Time.
                // WARNING: The formula below is incorrect when there are vehicles with different
                // speeds.
                if occupied_length.0 <= outflow * (self.total_length() / self.base_speed).0 {
                    self.length / vehicle_speed
                } else {
                    Time(occupied_length.0 / (outflow * T::from(self.lanes).unwrap()))
                }
            }
            SpeedDensityFunction::ThreeRegimes(func) => {
                let density = (occupied_length / self.total_length()).0;
                let speed = func.get_speed(vehicle_speed, density);
                self.length / speed
            }
        }
    }

    /// Return the free-flow travel time on the road for the given vehicle.
    #[inline]
    pub fn get_free_flow_travel_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.get_travel_time(Length::zero(), vehicle)
    }

    /// Return the length of the edge, from source to target.
    pub fn length(&self) -> Length<T> {
        self.length
    }

    /// Return the total length of the edge that can be occupied by vehicles, i.e., the length of
    /// the edge multiplied by the number of lanes.
    pub fn total_length(&self) -> Length<T> {
        self.length * self.lanes
    }

    /// Return the effective bottleneck outflow of the edge, i.e., the outflow for all the lanes.
    pub fn get_effective_outflow(&self) -> Outflow<T> {
        self.bottleneck_outflow * self.lanes
    }
}

/// Description of the graph of a [RoadNetwork].
///
/// A RoadGraph is a directed graph of [RoadNode]s and [RoadEdge]s,
/// Internally, it is represented as a [petgraph::graph::DiGraph].
#[derive(Clone, Debug, Serialize)]
pub struct RoadGraph<T>(DiGraph<RoadNode, RoadEdge<T>>);

impl<T> RoadGraph<T> {
    /// Creates a new RoadGraph.
    pub fn new(graph: DiGraph<RoadNode, RoadEdge<T>>) -> Self {
        Self(graph)
    }
}

impl<T> Deref for RoadGraph<T> {
    type Target = DiGraph<RoadNode, RoadEdge<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
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
    pub fn new(graph: DiGraph<RoadNode, RoadEdge<T>>, vehicles: Vec<Vehicle<T>>) -> Self {
        RoadNetwork {
            graph: RoadGraph(graph),
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
}

impl<T: TTFNum> RoadNetwork<T> {
    /// Return an empty [RoadNetworkState].
    pub fn get_blank_state(&self) -> RoadNetworkState<'_, T> {
        RoadNetworkState::from_network(self)
    }

    /// Return a [RoadNetworkPreprocessingData] with all the unique origin-destination pairs, for
    /// each vehicle, for the given set of [agents](Agent).
    pub fn preprocess(&self, agents: &[Agent<T>]) -> RoadNetworkPreprocessingData {
        let mut od_data = RoadNetworkPreprocessingData {
            od_pairs: vec![ODPairs::default(); self.vehicles.len()],
        };
        for agent in agents {
            for mode in agent.iter_modes() {
                if let Mode::Road(road_mode) = mode {
                    let od_pairs = &mut od_data[road_mode.vehicle_index()];
                    od_pairs.add_pair(road_mode.origin(), road_mode.destination());
                }
            }
        }
        od_data
    }

    /// Compute and return the [RoadNetworkSkims] for the RoadNetwork, with the given
    /// [RoadNetworkWeights], [RoadNetworkPreprocessingData] and [RoadNetworkParameters].
    pub fn compute_skims(
        &self,
        weights: &RoadNetworkWeights<T>,
        preprocess_data: &RoadNetworkPreprocessingData,
        parameters: &RoadNetworkParameters<T>,
    ) -> Result<RoadNetworkSkims<T>> {
        let mut skims = Vec::with_capacity(self.vehicles.len());
        for (vehicle_id, _vehicle) in self.iter_vehicles() {
            if preprocess_data[vehicle_id].is_empty() {
                // No one is using this vehicle so there is no need to compute the skims.
                skims.push(None);
            }
            let nb_breakpoints: usize = weights[vehicle_id].iter().map(|w| w.complexity()).sum();
            debug!("Total number of breakpoints: {nb_breakpoints}");
            // TODO: In some cases, it might be faster to re-use the same order from one iteration
            // to another.
            let mut hierarchy = HierarchyOverlay::order(
                &self.graph,
                |edge_id| weights[(vehicle_id, edge_id)].clone(),
                parameters.contraction.clone(),
            );
            hierarchy.simplify(parameters.edge_simplification);
            let mut skim = RoadNetworkSkim::new(hierarchy);
            let od_pairs = &preprocess_data[vehicle_id];
            skim.compute_search_spaces(&od_pairs.unique_origins, &od_pairs.unique_destinations);
            skim.simplify_search_spaces(parameters.search_space_simplification);
            skim.pre_compute_profile_queries(&od_pairs.pairs)?;
            skims.push(Some(skim));
        }
        Ok(RoadNetworkSkims(skims))
    }

    /// Return the free-flow travel time for each edge and each vehicle of the RoadNetwork.
    pub fn get_free_flow_weights(&self) -> RoadNetworkWeights<T> {
        let mut weights_vec =
            RoadNetworkWeights::with_capacity(self.vehicles.len(), self.graph.edge_count());
        for (vehicle_id, vehicle) in self.iter_vehicles() {
            let weights = &mut weights_vec[vehicle_id];
            for edge in self.graph.edge_references() {
                let tt = edge.weight().get_free_flow_travel_time(vehicle);
                weights.push(TTF::Constant(tt));
            }
        }
        weights_vec
    }
}

impl<T> Index<VehicleIndex> for RoadNetwork<T> {
    type Output = Vehicle<T>;
    fn index(&self, index: VehicleIndex) -> &Self::Output {
        &self.vehicles[index.index()]
    }
}

/// Set of parameters related to a [RoadNetwork].
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Road Network Parameters")]
#[schemars(description = "Set of parameters related to a road network.")]
pub struct RoadNetworkParameters<T> {
    /// [ContractionParameters] controlling how a [HierarchyOverlay] is built from a [RoadNetwork].
    #[serde(default)]
    #[schemars(
        description = "Parameters controlling how a hierarchy overlay is built from a road network graph."
    )]
    pub contraction: ContractionParameters,
    /// [TTFSimplification] describing how the edges' TTFs are simplified after the
    /// HierarchyOverlay is built.
    #[serde(default = "TTFSimplification::<Time<T>>::default")]
    #[schemars(
        description = "How to simplify the edges TTFs after the hierarchy overlay is built."
    )]
    pub edge_simplification: TTFSimplification<Time<T>>,
    /// [TTFSimplification] describing how the TTFs of the forward and backward search spaces
    /// are simplified.
    #[serde(default = "TTFSimplification::<Time<T>>::default")]
    #[schemars(
        description = "How to simplify the TTFs of the forward and backward search spaces."
    )]
    pub search_space_simplification: TTFSimplification<Time<T>>,
    /// [TTFSimplification] describing how the weights of the road network are simplified at the
    /// beginning of the iteration.
    #[serde(default = "TTFSimplification::<Time<T>>::default")]
    #[schemars(description = "How to simplify the edges TTFs at the beginning of the iteration.")]
    pub weight_simplification: TTFSimplification<Time<T>>,
}

impl<T> Default for RoadNetworkParameters<T> {
    fn default() -> Self {
        RoadNetworkParameters {
            contraction: Default::default(),
            edge_simplification: Default::default(),
            search_space_simplification: Default::default(),
            weight_simplification: Default::default(),
        }
    }
}

/// Structure containing, for each [Vehicle], an [ODPairs] instance representing the
/// origin-destination pairs for which at least one agent can make a trip with this vehicle.
#[derive(Clone, Debug, Default)]
pub struct RoadNetworkPreprocessingData {
    od_pairs: Vec<ODPairs>,
}

impl Index<VehicleIndex> for RoadNetworkPreprocessingData {
    type Output = ODPairs;
    fn index(&self, index: VehicleIndex) -> &Self::Output {
        &self.od_pairs[index.index()]
    }
}

impl IndexMut<VehicleIndex> for RoadNetworkPreprocessingData {
    fn index_mut(&mut self, index: VehicleIndex) -> &mut Self::Output {
        &mut self.od_pairs[index.index()]
    }
}

/// Structure representing the origin-destination pairs for which at least one agent can make a
/// trip, with a given vehicle.
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(from = "crate::serialization::DeserODPairs")]
pub struct ODPairs {
    unique_origins: HashSet<NodeIndex>,
    unique_destinations: HashSet<NodeIndex>,
    pairs: HashMap<NodeIndex, HashSet<NodeIndex>>,
}

impl ODPairs {
    /// Create a new ODPairs from a Vec of tuples `(o, d)`, where `o` is the [NodeIndex] of the
    /// origin and `d` is the [NodeIndex] of the destination.
    pub fn from_vec(raw_pairs: Vec<(NodeIndex, NodeIndex)>) -> Self {
        let mut pairs = ODPairs::default();
        for (origin, destination) in raw_pairs {
            pairs.add_pair(origin, destination);
        }
        pairs
    }

    fn is_empty(&self) -> bool {
        self.unique_origins.is_empty() && self.unique_destinations.is_empty()
    }

    /// Add an origin-destination pair to the ODPairs.
    fn add_pair(&mut self, origin: NodeIndex, destination: NodeIndex) {
        self.unique_origins.insert(origin);
        self.unique_destinations.insert(destination);
        self.pairs
            .entry(origin)
            .or_insert_with(HashSet::new)
            .insert(destination);
    }
}

#[cfg(test)]
mod tests {
    use super::vehicle::SpeedFunction;
    use super::*;
    use crate::units::PCE;

    #[test]
    fn get_travel_time_test() {
        let mut edge = RoadEdge {
            base_speed: Speed(25.), // 50 km/h
            length: Length(1000.),  // 1 km
            lanes: 2,
            speed_density: SpeedDensityFunction::FreeFlow,
            bottleneck_outflow: Outflow(f64::INFINITY),
        };
        let vehicle = Vehicle::new(Length(10.), PCE(1.), SpeedFunction::Base);
        // 1 km at 50 km/h is 40s.
        assert_eq!(edge.get_travel_time(Length(0.), &vehicle), Time(40.));
        assert_eq!(edge.get_travel_time(Length(4000.), &vehicle), Time(40.));

        edge.speed_density = SpeedDensityFunction::Bottleneck(10.);
        // The outflow is 2 veh. / s. (there are two lanes) and each veh. can travel through the
        // edge in 40 s. so the threshold is at 80 veh. on the edge = 800 m occupied.
        assert_eq!(edge.get_travel_time(Length(0.), &vehicle), Time(40.));
        assert_eq!(edge.get_travel_time(Length(800.), &vehicle), Time(40.));
        assert!(edge.get_travel_time(Length(801.), &vehicle) > Time(40.));
        // Double value of the threshold -> travel time is double.
        assert_eq!(edge.get_travel_time(Length(1600.), &vehicle), Time(80.));

        edge.speed_density = SpeedDensityFunction::ThreeRegimes(ThreeRegimesSpeedDensityFunction {
            min_density: 0.2,
            jam_density: 0.8,
            jam_speed: Speed(5.), // 18 km/h
            beta: 2.,
        });
        // Free-flow regime.
        assert_eq!(edge.get_travel_time(Length(0.), &vehicle), Time(40.));
        assert_eq!(edge.get_travel_time(Length(400.), &vehicle), Time(40.));
        // Congested regime.
        let tt = edge.get_travel_time(Length(401.), &vehicle);
        assert!(tt > Time(40.), "{tt:?} <= Time(40.)");
        // With occupied length 800.0, density is 0.4.
        // coef = (.2 / .6)^2 = 1/9.
        // speed = 25 * (1 - 1/9) + 5 * 1/9 ~= 22.7777.
        // tt ~= 1000 / 22.7777 ~= 43.9024.
        let tt = edge.get_travel_time(Length(800.), &vehicle);
        assert!(tt.approx_eq(&Time(43.9024)), "{tt:?} != 43.9024");
        // With occupied length 1200.0, density is 0.6.
        // coef = (.4 / .6)^2 = 4/9.
        // speed = 25 * (1 - 4/9) + 5 * 4/9 ~= 16.1111.
        // tt ~= 1000 / 16.1111 ~= 62.0690.
        let tt = edge.get_travel_time(Length(1200.), &vehicle);
        assert!(tt.approx_eq(&Time(62.0690)), "{tt:?} != 62.0690");
        // With occupied length 1599.99, density is close to 0.8.
        let tt = edge.get_travel_time(Length(1599.99999999), &vehicle);
        assert!(tt.approx_eq(&Time(200.)), "{tt:?} != 200.0");
        // Traffic jam.
        // 1 km at 18 km/h is 200s.
        assert_eq!(edge.get_travel_time(Length(1600.), &vehicle), Time(200.));
        assert_eq!(edge.get_travel_time(Length(3200.), &vehicle), Time(200.));
    }
}
