// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to modes of transportation.
use std::fmt;

use anyhow::Result;
use enum_as_inner::EnumAsInner;
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use self::trip::event::RoadEvent;
use self::trip::results::{AggregateTripResults, TripResults};
use self::trip::TravelingMode;
use crate::agent::AgentIndex;
use crate::event::Event;
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::skim::EAAllocation;
use crate::network::road_network::{RoadNetwork, RoadNetworkWeights};
use crate::network::{Network, NetworkPreprocessingData, NetworkSkim};
use crate::progress_bar::MetroProgressBar;
use crate::units::{Distribution, Time, Utility};

pub mod trip;

/// Mode identifier.
///
/// The `n` modes of an [Agent](crate::agent::Agent) are indexed from `0` to `n-1`.
#[derive(
    Copy,
    Clone,
    Debug,
    Default,
    PartialEq,
    PartialOrd,
    Eq,
    Ord,
    Hash,
    Deserialize,
    Serialize,
    JsonSchema,
)]
pub struct ModeIndex(usize);

impl ModeIndex {
    /// Creates a new ModeIndex.
    pub const fn new(x: usize) -> Self {
        ModeIndex(x)
    }

    /// Returns the index of the ModeIndex.
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Short version of `ModeIndex::new`.
pub const fn mode_index(x: usize) -> ModeIndex {
    ModeIndex::new(x)
}

/// Mode of transportation available to an agent.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema, EnumAsInner)]
#[serde(bound = "T: TTFNum")]
#[serde(tag = "type", content = "value")]
#[schemars(title = "Mode")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
pub enum Mode<T> {
    /// An activity (e.g., staying home, traveling) that always provide the same utility level.
    Constant(Utility<T>),
    /// A trip consisting in a sequence of legs (either on the road or virtual).
    Trip(TravelingMode<T>),
}

impl<T> fmt::Display for Mode<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(_) => write!(f, "Constant"),
            Self::Trip(_) => write!(f, "Trip"),
        }
    }
}

impl<T: TTFNum> Mode<T> {
    /// This method returns the results of the pre-day model (expected utility and [ModeCallback])
    /// for a given [Mode], [NetworkSkim] and [NetworkPreprocessingData].
    pub fn get_pre_day_choice<'a>(
        &'a self,
        network: &'a Network<T>,
        exp_skims: &'a NetworkSkim<T>,
        preprocess_data: &'a NetworkPreprocessingData<T>,
        progress_bar: MetroProgressBar,
    ) -> Result<(Utility<T>, ModeCallback<'a, T>)> {
        match self {
            Self::Constant(u) => Ok((*u, Box::new(|_| Ok(ModeResults::None)))),
            Self::Trip(mode) => mode.get_pre_day_choice(
                network.get_road_network(),
                exp_skims.get_road_network(),
                preprocess_data.get_road_network(),
                progress_bar,
            ),
        }
    }
}

/// Type representing the callback function that can be run to get a [ModeResults] with the choices
/// from the pre-day model for an agent.
///
/// The callback function takes no argument and returns a [ModeResults] (or an error).
///
/// For an agent with multiple modes, only the callback function of the mode chosen in the pre-day
/// model is called.
pub type ModeCallback<'a, T> =
    Box<dyn FnOnce(&'a mut EAAllocation<T>) -> Result<ModeResults<T>> + 'a>;

/// Additional mode-specific results for an agent.
#[derive(Debug, Clone, PartialEq, EnumAsInner, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
#[serde(bound(serialize = "T: TTFNum"))]
pub enum ModeResults<T> {
    /// Results for a traveling mode.
    Trip(TripResults<T>),
    /// Alternative for modes or activities that do not recquire additional results.
    None,
}

impl<T: Copy> ModeResults<T> {
    /// Returns the departure time of the trip (if any).
    pub fn departure_time(&self) -> Option<Time<T>> {
        match self {
            Self::Trip(trip_results) => Some(trip_results.departure_time),
            Self::None => None,
        }
    }
}

impl<T: TTFNum> ModeResults<T> {
    /// Clones and resets the mode results in prevision for a new day.
    pub fn reset(&self) -> Self {
        match self {
            Self::Trip(trip_results) => Self::Trip(trip_results.reset()),
            Self::None => Self::None,
        }
    }

    /// Returns `true` if the trip or activity is finished, i.e., there is nothing more to simulate
    /// in the within-day model.
    pub fn is_finished(&self) -> bool {
        match self {
            Self::Trip(trip_results) => trip_results.is_finished(),
            Self::None => true,
        }
    }
}

impl<T: TTFNum> ModeResults<T> {
    /// Returns the initial event associated with the mode (if any).
    pub fn get_event(&self, agent_id: AgentIndex, mode_id: ModeIndex) -> Option<Box<dyn Event<T>>> {
        match self {
            Self::Trip(trip_results) => trip_results.get_event(agent_id, mode_id),
            Self::None => None,
        }
    }

    /// Returns the route that the agent is expected to be taken, if any.
    pub(crate) fn get_expected_route(
        &self,
        mode: &Mode<T>,
        road_network: &RoadNetwork<T>,
        weights: &RoadNetworkWeights<T>,
        unique_vehicles: &UniqueVehicles,
    ) -> Vec<Option<Vec<RoadEvent<T>>>> {
        match self {
            Self::Trip(trip_results) => trip_results.get_expected_route(
                mode.as_trip().unwrap(),
                road_network,
                weights,
                unique_vehicles,
            ),
            Self::None => vec![],
        }
    }
}

/// Aggregate results of an iteration that are mode-specific.
#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct AggregateModeResults<T> {
    /// Results specific to traveling modes.
    pub trip_modes: Option<AggregateTripResults<T>>,
    /// Results specific to constant modes.
    pub constant: Option<AggregateConstantResults<T>>,
}

/// Aggregate results of an iteration specific to constant modes.
#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct AggregateConstantResults<T> {
    /// Number of agents who chose a constant mode.
    pub count: usize,
    /// Distribution of the utility of the agents who chose a constant mode.
    pub utility: Distribution<Utility<T>>,
}

impl<T: TTFNum> AggregateConstantResults<T> {
    /// Creates a new [AggregateConstantResults] from a vector of [Utility].
    pub fn from_utilities(utilities: Vec<Utility<T>>) -> Self {
        Self {
            count: utilities.len(),
            utility: Distribution::from_iterator(utilities.into_iter()).unwrap(),
        }
    }
}
