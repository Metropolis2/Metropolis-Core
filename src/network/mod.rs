// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of the supply side of a simulation.
use anyhow::Result;
use road_network::skim::RoadNetworkSkims;
use road_network::{
    state::RoadNetworkState, weights::RoadNetworkWeights, RoadNetwork, RoadNetworkParameters,
    RoadNetworkPreprocessingData,
};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::agent::Agent;
use crate::parameters::Parameters;

pub mod road_network;

/// Abstract representation of the physical transportation network where agents can make trips.
///
/// A network can be composed of the following parts (all of them are optional):
///
/// - a [RoadNetwork].
///
/// If some part (for example, the road network) is absent, trips might be unreachable with
/// some modes of transportation.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[schemars(title = "Network")]
#[schemars(
    description = "Abstract representation of the physical transportation network where agents can make trips."
)]
pub struct Network<T> {
    road_network: Option<RoadNetwork<T>>,
}

impl<T: TTFNum> Network<T> {
    /// Creates a new Network.
    pub fn new(road_network: Option<RoadNetwork<T>>) -> Self {
        Network { road_network }
    }

    /// Returns a reference to the road network of the network, as an option.
    ///
    /// If the network has no road network, returns `None`.
    pub fn get_road_network(&self) -> Option<&RoadNetwork<T>> {
        self.road_network.as_ref()
    }

    /// Returns a blank [NetworkState] from the network.
    pub fn get_blank_state(&self) -> NetworkState<'_, T> {
        NetworkState::new(self.road_network.as_ref().map(|rn| rn.get_blank_state()))
    }

    /// Return the [NetworkSkim] of the network given the [NetworkWeights], the
    /// [NetworkPreprocessingData] and the [NetworkParameters].
    pub fn compute_skims(
        &self,
        weights: &NetworkWeights<T>,
        preprocess_data: &NetworkPreprocessingData,
        parameters: &NetworkParameters<T>,
    ) -> Result<NetworkSkim<T>> {
        let rn_skims = self
            .road_network
            .as_ref()
            .map(|rn| {
                rn.compute_skims(
                    weights.road_network.as_ref().unwrap(),
                    preprocess_data.road_network.as_ref().unwrap(),
                    parameters.road_network.as_ref().unwrap(),
                )
            })
            .transpose()?;
        Ok(NetworkSkim {
            road_network: rn_skims,
        })
    }

    /// Return a [NetworkWeights] instance representing the weights of the Network under free-flow
    /// conditions.
    pub fn get_free_flow_weights(&self) -> NetworkWeights<T> {
        let rn_weights = self
            .road_network
            .as_ref()
            .map(|rn| rn.get_free_flow_weights());
        NetworkWeights {
            road_network: rn_weights,
        }
    }

    /// Return a [NetworkPreprocessingData] instance given the set of [agents](Agent) used for the
    /// simulation.
    pub fn preprocess(&self, agents: &[Agent<T>]) -> NetworkPreprocessingData {
        let rn_data = self.road_network.as_ref().map(|rn| rn.preprocess(agents));
        NetworkPreprocessingData {
            road_network: rn_data,
        }
    }
}

/// Simplified representation of the state of a network, as perceived by the agents.
///
/// A skim can be composed of the following parts (all of them are optional):
///
/// - a [RoadNetworkSkims].
#[derive(Clone, Default, Debug)]
pub struct NetworkSkim<T> {
    road_network: Option<RoadNetworkSkims<T>>,
}

impl<T> NetworkSkim<T> {
    /// Returns a reference to the road-network skim of the skim, as an option.
    ///
    /// If the skim has no road-network skim, returns `None`.
    pub fn get_road_network(&self) -> Option<&RoadNetworkSkims<T>> {
        self.road_network.as_ref()
    }
}

/// State of the [Network] at a given time.
///
/// The state of the network is updated in the within-day model.
/// It is used to compute congestion during the within-day modeland to get the observed
/// [NetworkWeights] at the end of the within-day model.
#[derive(Clone, Debug)]
pub struct NetworkState<'a, T> {
    road_network: Option<RoadNetworkState<'a, T>>,
}

impl<'a, T> NetworkState<'a, T> {
    fn new(road_network: Option<RoadNetworkState<'a, T>>) -> Self {
        NetworkState { road_network }
    }

    /// Return a mutable reference to the [RoadNetworkState] of the [NetworkState], as an option.
    ///
    /// If the NetworkState has no road-network state, return `None`.
    pub fn get_mut_road_network(&mut self) -> Option<&mut RoadNetworkState<'a, T>> {
        self.road_network.as_mut()
    }
}

impl<T: TTFNum> NetworkState<'_, T> {
    /// Return [NetworkWeights] that provide a simplified representation of the [NetworkState].
    pub fn get_weights(&self, parameters: &Parameters<T>) -> NetworkWeights<T> {
        let rn_weights = self.road_network.as_ref().map(|rn| {
            rn.get_weights(
                parameters.period,
                parameters
                    .network
                    .road_network
                    .as_ref()
                    .unwrap()
                    .weight_simplification,
            )
        });
        NetworkWeights {
            road_network: rn_weights,
        }
    }
}

/// Simplified representation of the state of a network during a whole day.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct NetworkWeights<T> {
    road_network: Option<RoadNetworkWeights<T>>,
}

impl<T> NetworkWeights<T> {
    /// Creates a new NetworkWeights.
    pub fn new(road_network: Option<RoadNetworkWeights<T>>) -> Self {
        NetworkWeights { road_network }
    }

    /// Return a reference to the [RoadNetworkWeights] of the [NetworkWeights], as an option.
    ///
    /// If the NetworkWeights have no road-network weights, return `None`.
    pub fn get_road_network(&self) -> Option<&RoadNetworkWeights<T>> {
        self.road_network.as_ref()
    }
}

impl<T: TTFNum> NetworkWeights<T> {
    /// Return the weighted average beteen two [NetworkWeights], where `coefficient` is the weight
    /// of `self` and `1 - coefficient` is the weight of `other`.
    #[must_use]
    pub fn average(&self, other: &NetworkWeights<T>, coefficient: T) -> NetworkWeights<T> {
        let rn_weights = if let (Some(self_rn_weights), Some(other_rn_weights)) =
            (&self.road_network, &other.road_network)
        {
            Some(self_rn_weights.average(other_rn_weights, coefficient))
        } else {
            None
        };
        NetworkWeights {
            road_network: rn_weights,
        }
    }

    /// Return the genetic average between two [NetworkWeights].
    ///
    /// The genetic average of `x` and `y` is `(x^a + y^b)^(1/(a+b))`.
    #[must_use]
    pub fn genetic_average(&self, other: &NetworkWeights<T>, a: T, b: T) -> NetworkWeights<T> {
        let rn_weights = if let (Some(self_rn_weights), Some(other_rn_weights)) =
            (&self.road_network, &other.road_network)
        {
            Some(self_rn_weights.genetic_average(other_rn_weights, a, b))
        } else {
            None
        };
        NetworkWeights {
            road_network: rn_weights,
        }
    }
}

/// Structure representing network data that is pre-computed before the first iteration of the
/// simulation.
#[derive(Clone, Debug)]
pub struct NetworkPreprocessingData {
    road_network: Option<RoadNetworkPreprocessingData>,
}

impl NetworkPreprocessingData {
    /// Return the [RoadNetworkPreprocessingData] of the [NetworkPreprocessingData].
    pub fn get_road_network(&self) -> Option<&RoadNetworkPreprocessingData> {
        self.road_network.as_ref()
    }
}

/// Parameters of the simulation that are specific to the network.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub struct NetworkParameters<T> {
    /// Parameters specific to the road network.
    road_network: Option<RoadNetworkParameters<T>>,
}

impl<T> Default for NetworkParameters<T> {
    fn default() -> Self {
        NetworkParameters {
            road_network: Some(RoadNetworkParameters::default()),
        }
    }
}
