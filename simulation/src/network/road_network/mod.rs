pub mod skim;
pub mod state;
pub mod vehicle;
pub mod weights;

use crate::agent::Agent;
use crate::mode::Mode;
use crate::units::{Length, Outflow, Speed, Time};
use skim::{RoadNetworkSkim, RoadNetworkSkims};
use state::{RoadNetworkState, WeightSimplification};
use vehicle::{vehicle_index, Vehicle, VehicleIndex};
use weights::RoadNetworkWeights;

use anyhow::Result;
use hashbrown::{HashMap, HashSet};
use log::debug;
use num_traits::Zero;
use petgraph::graph::{DiGraph, EdgeIndex, Neighbors, NodeIndex};
use petgraph::Direction;
use serde_derive::{Deserialize, Serialize};
use std::ops::{Index, IndexMut};
use tch::{ContractionParameters, HierarchyOverlay};
use ttf::{TTFNum, TTF};

pub type NodePair = (NodeIndex, NodeIndex);

pub type NodePairs = HashSet<NodePair>;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RoadNode {
    id: usize,
}

impl RoadNode {
    pub fn new(id: usize) -> Self {
        RoadNode { id }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub enum SpeedDensityFunction<T> {
    FreeFlow,
    Bottleneck(Outflow<T>),
}

fn default_outflow<T: TTFNum>() -> T {
    T::infinity()
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct RoadEdge<T> {
    id: usize,
    base_speed: Speed<T>,
    length: Length<T>,
    lanes: u8,
    speed_density: SpeedDensityFunction<T>,
    #[serde(default = "default_outflow")]
    /// Maximum outflow of vehicle on the edge, in length of vehicle per second per lane.
    bottleneck_outflow: Outflow<T>,
}

impl<T: TTFNum> RoadEdge<T> {
    pub fn new(
        id: usize,
        base_speed: Speed<T>,
        length: Length<T>,
        lanes: u8,
        speed_density: SpeedDensityFunction<T>,
        bottleneck_outflow: Outflow<T>,
    ) -> Self {
        RoadEdge {
            id,
            base_speed,
            length,
            lanes,
            speed_density,
            bottleneck_outflow,
        }
    }

    pub fn get_travel_time(&self, occupied_length: Length<T>, vehicle: &Vehicle<T>) -> Time<T> {
        let vehicle_speed = vehicle.get_speed(self.base_speed);
        match self.speed_density {
            SpeedDensityFunction::FreeFlow => self.length / vehicle_speed,
            SpeedDensityFunction::Bottleneck(outflow) => {
                // WARNING: The formula below is incorrect when there are vehicles with different
                // speeds.
                if occupied_length <= outflow * (self.total_length() / vehicle_speed) {
                    self.length / vehicle_speed
                } else {
                    occupied_length / (outflow * self.lanes)
                }
            }
        }
    }

    /// Return the free-flow travel time on the road for the given vehicle.
    #[inline]
    pub fn get_free_flow_travel_time(&self, vehicle: &Vehicle<T>) -> Time<T> {
        self.get_travel_time(Length::zero(), vehicle)
    }

    pub fn length(&self) -> Length<T> {
        self.length
    }

    pub fn total_length(&self) -> Length<T> {
        self.length * self.lanes
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct RoadNetwork<T> {
    graph: DiGraph<RoadNode, RoadEdge<T>>,
    vehicles: Vec<Vehicle<T>>,
}

impl<T> RoadNetwork<T> {
    pub fn new(graph: DiGraph<RoadNode, RoadEdge<T>>, vehicles: Vec<Vehicle<T>>) -> Self {
        RoadNetwork { graph, vehicles }
    }

    pub fn get_graph(&self) -> &DiGraph<RoadNode, RoadEdge<T>> {
        &self.graph
    }

    pub fn get_outgoing_edges(&self, from: NodeIndex) -> Neighbors<RoadEdge<T>> {
        self.graph.neighbors_directed(from, Direction::Outgoing)
    }

    pub fn get_endpoints(&self, edge: EdgeIndex) -> Option<(NodeIndex, NodeIndex)> {
        self.graph.edge_endpoints(edge)
    }

    /// Return an Iterator over the [Vehicle] of the network, together with their
    /// [VehicleIndex].
    pub fn iter_vehicles(&self) -> impl Iterator<Item = (VehicleIndex, &Vehicle<T>)> {
        self.vehicles
            .iter()
            .enumerate()
            .map(|(i, v)| (vehicle_index(i), v))
    }
}

impl<T: TTFNum> RoadNetwork<T> {
    pub fn get_blank_state(&self) -> RoadNetworkState<T> {
        RoadNetworkState::from_network(self)
    }

    /// Return a [RoadNetworkPreprocessingData] with the unique origin-destination pairs, for each
    /// vehicle, for the given set of (agents)[Agent].
    pub fn preprocess(&self, agents: &[Agent<T>]) -> RoadNetworkPreprocessingData {
        let mut od_data =
            RoadNetworkPreprocessingData(vec![ODPairs::default(); self.vehicles.len()]);
        for agent in agents {
            for mode in agent.iter_modes() {
                if let Mode::Road(road_mode) = mode {
                    let od_pairs = &mut od_data[road_mode.vehicle_index()];
                    od_pairs.unique_origins.insert(road_mode.origin());
                    od_pairs.unique_destinations.insert(road_mode.destination());
                    od_pairs
                        .pairs
                        .entry(road_mode.origin())
                        .or_insert_with(HashSet::new)
                        .insert(road_mode.destination());
                }
            }
        }
        od_data
    }

    /// Compute and return the [RoadNetworkSkims] for the RoadNetwork, with the given [RoadNetworkWeights],
    /// [RoadNetworkPreprocessingData] and [RoadNetworkParameters].
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
            hierarchy.approximate(parameters.edge_approx_bound);
            let mut skim = RoadNetworkSkim::new(hierarchy);
            let od_pairs = &preprocess_data[vehicle_id];
            skim.compute_search_spaces(&od_pairs.unique_origins, &od_pairs.unique_destinations);
            skim.approximate_search_spaces(parameters.space_approx_bound);
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
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RoadNetworkParameters<T> {
    /// [ContractionParameters] controlling how a [HierarchyOverlay] is built from a [RoadNetwork].
    #[serde(default)]
    pub contraction: ContractionParameters,
    /// Approximation bound used to simplify the edges' TTFs after the HierarchyOverlay is built.
    pub edge_approx_bound: Time<T>,
    /// Approximation bound used to simplify the TTFs of the forward and backward search spaces.
    pub space_approx_bound: Time<T>,
    /// [WeightSimplification] describing how the weights of the road network are simplified at the
    /// beginning of the iteration.
    pub weight_simplification: WeightSimplification<T>,
}

/// Structure containing, for each [Vehicle], an [ODPairs] instance represented the
/// origin-destination pairs for which at least one agent can make a trip with this vehicle.
#[derive(Clone, Debug, Default)]
pub struct RoadNetworkPreprocessingData(Vec<ODPairs>);

impl Index<VehicleIndex> for RoadNetworkPreprocessingData {
    type Output = ODPairs;
    fn index(&self, index: VehicleIndex) -> &Self::Output {
        &self.0[index.index()]
    }
}

impl IndexMut<VehicleIndex> for RoadNetworkPreprocessingData {
    fn index_mut(&mut self, index: VehicleIndex) -> &mut Self::Output {
        &mut self.0[index.index()]
    }
}

/// Structure representing the origin-destination pairs for which at least one agent can make a
/// trip, with a given vehicle.
#[derive(Clone, Debug, Default)]
pub struct ODPairs {
    unique_origins: HashSet<NodeIndex>,
    unique_destinations: HashSet<NodeIndex>,
    pairs: HashMap<NodeIndex, HashSet<NodeIndex>>,
}

impl ODPairs {
    fn is_empty(&self) -> bool {
        self.unique_origins.is_empty() && self.unique_destinations.is_empty()
    }
}
