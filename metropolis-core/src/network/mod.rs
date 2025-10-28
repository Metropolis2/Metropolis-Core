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

//! Description of the supply side of a simulation.
use anyhow::Result;
use road_network::{
    RoadNetwork, RoadNetworkPreprocessingData, RoadNetworkSkims, RoadNetworkState,
    RoadNetworkWeights,
};
use serde_derive::Serialize;

use crate::units::ZeroOneNum;

pub mod road_network;

/// Initializes the global value of the network.
pub fn init(value: Network) -> Result<()> {
    if let Some(rn) = value.road_network {
        road_network::init(rn)?;
    }
    Ok(())
}

/// Initializes the global value of the road network.
///
/// Modifies the value if it was already initialized.
pub fn replace(value: Network) {
    if let Some(rn) = value.road_network {
        road_network::replace(rn);
    } else {
        road_network::drop();
    }
}

/// Returns `true` if the global network is defined.
pub fn is_init() -> bool {
    road_network::is_init()
}

pub(crate) fn has_road_network() -> bool {
    road_network::is_init()
}

/// Abstract representation of the physical transportation network where agents can make trips.
///
/// A network can be composed of the following parts (all of them are optional):
///
/// - a [RoadNetwork].
///
/// If some part (for example, the road network) is absent, trips might be unreachable with
/// some modes of transportation.
#[derive(Clone, Debug)]
pub struct Network {
    road_network: Option<RoadNetwork>,
}

impl Network {
    /// Creates a new Network.
    pub const fn new(road_network: Option<RoadNetwork>) -> Self {
        Network { road_network }
    }
}

/// Returns a blank [NetworkState] from the network.
pub fn blank_state() -> NetworkState {
    if has_road_network() {
        NetworkState::new(Some(road_network::blank_state()))
    } else {
        NetworkState::new(None)
    }
}

/// Return the [NetworkSkim] of the network given the [NetworkWeights], the
/// [NetworkPreprocessingData] and the [RoadNetworkParameters].
pub fn compute_skims(
    weights: &NetworkWeights,
    preprocess_data: &NetworkPreprocessingData,
) -> Result<NetworkSkim> {
    let rn_skims = if has_road_network() {
        Some(road_network::compute_skims(
            weights.road_network.as_ref().unwrap(),
            preprocess_data.road_network.as_ref().unwrap(),
        )?)
    } else {
        None
    };
    Ok(NetworkSkim {
        road_network: rn_skims,
    })
}

/// Return a [NetworkPreprocessingData] instance given the set of [agents](Agent) used for the
/// simulation.
pub fn preprocess() -> Result<NetworkPreprocessingData> {
    let rn_data = if has_road_network() {
        Some(road_network::preprocess()?)
    } else {
        None
    };
    Ok(NetworkPreprocessingData {
        road_network: rn_data,
    })
}

/// Simplified representation of the state of a network, as perceived by the agents.
///
/// A skim can be composed of the following parts (all of them are optional):
///
/// - a [RoadNetworkSkims].
#[derive(Clone, Default, Debug, Serialize)]
pub struct NetworkSkim {
    road_network: Option<RoadNetworkSkims>,
}

impl NetworkSkim {
    /// Returns a reference to the road-network skim of the skim, as an option.
    ///
    /// If the skim has no road-network skim, returns `None`.
    pub const fn get_road_network(&self) -> Option<&RoadNetworkSkims> {
        self.road_network.as_ref()
    }
}

/// State of the [Network] at a given time.
///
/// The state of the network is updated in the within-day model.
/// It is used to compute congestion during the within-day modeland to get the observed
/// [NetworkWeights] at the end of the within-day model.
#[derive(Clone, Debug)]
pub struct NetworkState {
    road_network: Option<RoadNetworkState>,
}

impl NetworkState {
    const fn new(road_network: Option<RoadNetworkState>) -> Self {
        NetworkState { road_network }
    }

    /// Return a mutable reference to the [RoadNetworkState] of the [NetworkState], as an option.
    ///
    /// If the NetworkState has no road-network state, return `None`.
    pub(crate) fn get_mut_road_network(&mut self) -> Option<&mut RoadNetworkState> {
        self.road_network.as_mut()
    }
}

impl NetworkState {
    /// Return [NetworkWeights] that provide a simplified representation of the [NetworkState].
    pub fn into_weights(self, preprocess_data: &NetworkPreprocessingData) -> NetworkWeights {
        let rn_weights = self
            .road_network
            .map(|rn| rn.into_weights(preprocess_data.road_network.as_ref().unwrap()));
        NetworkWeights {
            road_network: rn_weights,
        }
    }
}

/// Simplified representation of the state of a network during a whole day.
#[derive(Clone, Debug, Default)]
pub struct NetworkWeights {
    road_network: Option<RoadNetworkWeights>,
}

impl NetworkWeights {
    /// Creates a new NetworkWeights.
    pub const fn new(road_network: Option<RoadNetworkWeights>) -> Self {
        NetworkWeights { road_network }
    }

    /// Returns a reference to the [RoadNetworkWeights] of the [NetworkWeights], as an option.
    ///
    /// If the NetworkWeights have no road-network weights, return `None`.
    pub const fn road_network(&self) -> Option<&RoadNetworkWeights> {
        self.road_network.as_ref()
    }
}

impl NetworkWeights {
    /// Returns the weighted average beteen two [NetworkWeights], where `coefficient` is the weight
    /// of `self` and `1 - coefficient` is the weight of `other`.
    #[must_use]
    pub fn average(&self, other: &NetworkWeights, coefficient: ZeroOneNum) -> NetworkWeights {
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

    /// Returns the genetic average between two [NetworkWeights].
    ///
    /// The genetic average of `x` and `y` is `(x^a + y^b)^(1/(a+b))`.
    #[must_use]
    pub fn genetic_average(&self, other: &NetworkWeights, a: f64, b: f64) -> NetworkWeights {
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
#[derive(Clone, Debug, Default)]
pub struct NetworkPreprocessingData {
    road_network: Option<RoadNetworkPreprocessingData>,
}

impl NetworkPreprocessingData {
    /// Return the [RoadNetworkPreprocessingData] of the [NetworkPreprocessingData].
    pub const fn get_road_network(&self) -> Option<&RoadNetworkPreprocessingData> {
        self.road_network.as_ref()
    }
}
