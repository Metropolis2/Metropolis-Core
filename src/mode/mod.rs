// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to modes of transportation.
use std::fmt;

use anyhow::{anyhow, Result};
use choice::ContinuousChoiceModel;
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use self::fixed_ttf::{AggregateFixedTTFResults, FixedTTFMode};
use self::road::{AggregateRoadResults, RoadChoiceAllocation, RoadChoices, RoadMode, RoadResults};
use crate::agent::AgentIndex;
use crate::event::Event;
use crate::network::{NetworkPreprocessingData, NetworkSkim};
use crate::simulation::results::AgentResult;
use crate::units::{Distribution, Interval, NoUnit, Time, Utility};

pub mod fixed_ttf;
pub mod road;

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
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[serde(tag = "type", content = "value")]
#[schemars(title = "Mode")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
pub enum Mode<T> {
    /// A mode of transportation that always provide the same utility level.
    Constant(Utility<T>),
    /// A mode of transportation with a fixed travel time function.
    ///
    /// This can represent modes with no congestion or with exogenous congestion (i.e., the
    /// travel-time function does not vary from iteration to iteration), but where the travel time
    /// can (optionnaly) vary according to the departure time.
    FixedTTF(FixedTTFMode<T>),
    /// A trip with a vehicle on the road network, with potential congestion.
    Road(RoadMode<T>),
}

impl<T> fmt::Display for Mode<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(_) => write!(f, "Constant"),
            Self::FixedTTF(_) => write!(f, "FixedTTF"),
            Self::Road(_) => write!(f, "Road"),
        }
    }
}

impl<T: TTFNum> Mode<T> {
    /// This method returns the results of the pre-day model (expected utility and [ModeCallback])
    /// for a given [Mode], [NetworkSkim] and [NetworkPreprocessingData].
    pub fn make_pre_day_choice<'a>(
        &'a self,
        exp_skims: &'a NetworkSkim<T>,
        preprocess_data: &NetworkPreprocessingData<T>,
    ) -> Result<(Utility<T>, ModeCallback<'a, T>)> {
        match self {
            Self::Constant(u) => Ok((*u, Box::new(|_| Ok(PreDayChoices::None)))),
            Self::FixedTTF(mode) => {
                let (u, dt) = mode.get_pre_day_choice()?;
                Ok((u, Box::new(move |_| Ok(PreDayChoices::FixedTTF(dt)))))
            }
            Self::Road(mode) => {
                let rn_skims = &exp_skims.get_road_network().ok_or_else(|| {
            anyhow!(
                "Cannot make pre-day choice for road mode when there is no skims for the road network"
            )
        })?;
                mode.make_pre_day_choice(rn_skims, preprocess_data.get_road_network().unwrap())
            }
        }
    }

    /// Return the realized utility of the trip, given the [Mode], the [ModeResults], and
    /// (optionally) the departure and arrival time.
    ///
    /// **Panics** if the [Mode] and [ModeResults] are incompatible.
    ///
    /// **Panics** if there is no departure or arrival time when it is required.
    pub fn get_utility(
        &self,
        results: &ModeResults<T>,
        departure_time: Option<Time<T>>,
        arrival_time: Option<Time<T>>,
    ) -> Utility<T> {
        match self {
            Self::Constant(u) => *u,
            Self::FixedTTF(mode) => mode
                .get_total_utility(departure_time.expect(
                    "Cannot compute utility of mode with fixed TTF with no departure time",
                )),
            Self::Road(mode) => {
                if let ModeResults::Road(road_results) = results {
                    debug_assert!(
                        road_results
                            .total_travel_time()
                            .approx_eq(&(arrival_time.unwrap() - departure_time.unwrap())),
                        "{:?} != {:?}",
                        road_results.total_travel_time(),
                        arrival_time.unwrap() - departure_time.unwrap()
                    );
                    mode.get_utility_from_results(
                        road_results,
                        departure_time.expect("Cannot compute road utility with no departure time"),
                        arrival_time.expect("Cannot compute road utility with no arrival time"),
                    )
                } else {
                    panic!("Incompatible ModeResults");
                }
            }
        }
    }
}

/// Type representing the callback function that can be run to get the [PreDayChoices] representing
/// the choice made by an agent in the pre-day model.
///
/// The callback function takes as argument a [PreDayChoiceAllocation] and returns a
/// [PreDayChoices] (or an error).
///
/// For an agent with multiple modes, only the callback function of the mode chosen in the pre-day
/// model is called.
pub type ModeCallback<'a, T> =
    Box<dyn FnOnce(&mut PreDayChoiceAllocation<T>) -> Result<PreDayChoices<T>> + 'a>;

/// Model used to compute the chosen departure time.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum DepartureTimeModel<T> {
    /// The departure time is always equal to the given value.
    Constant(Time<T>),
    /// The departure time is chosen according to a continuous choice model.
    ContinuousChoice {
        /// Interval in which the departure time is chosen.
        period: Interval<T>,
        /// Continuous choice model.
        choice_model: ContinuousChoiceModel<NoUnit<T>>,
    },
}

/// Enum representing the pre-day choices for a given mode.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum PreDayChoices<T> {
    /// Choices when a road mode is chosen.
    Road(RoadChoices<T>),
    /// Departure time chosen for a [FixedTTFMode].
    FixedTTF(Time<T>),
    /// Alternative for a mode with no pre-day choice.
    None,
}

impl<T: TTFNum + 'static> PreDayChoices<T> {
    /// This method returns (optionally) an [Event] that represents the start of the trip,
    /// corresponding to the pre-day choices.
    pub fn get_event(&self, agent: AgentIndex) -> Option<Box<dyn Event<T>>> {
        match self {
            Self::Road(choices) => choices.get_event(agent),
            Self::FixedTTF(_) => None,
            Self::None => None,
        }
    }
}

impl<T: TTFNum> PreDayChoices<T> {
    /// This method returns a [ModeResults], compatible with the pre-day choices.
    ///
    /// For modes with events during the within-day model, the [ModeResults] is filled during the
    /// within-day model (e.g., with the route and arrival time).
    pub fn init_mode_results(&self) -> ModeResults<T> {
        match self {
            Self::Road(choices) => ModeResults::Road(choices.init_mode_results()),
            Self::FixedTTF(_) => ModeResults::None,
            Self::None => ModeResults::None,
        }
    }
}

/// A memory allocation that can be used (and re-used) in the [ModeCallback] function.
#[derive(Clone, Debug, Default)]
pub struct PreDayChoiceAllocation<T: TTFNum> {
    road_alloc: RoadChoiceAllocation<T>,
}

/// Results of the within-day model specific to a mode of transportation.
#[derive(Debug, Clone, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
#[serde(bound(serialize = "T: TTFNum"))]
pub enum ModeResults<T> {
    /// Results for road modes.
    Road(RoadResults<T>),
    /// Alternative for modes with no additional results.
    None,
}

/// Aggregate results of an iteration that are mode-specific.
#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct AggregateModeResults<T> {
    /// Results specific to road modes.
    pub road: Option<AggregateRoadResults<T>>,
    /// Results specific to modes with fixed TTF.
    pub fixed_ttf: Option<AggregateFixedTTFResults<T>>,
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
    /// Compute [AggregateConstantResults] from the results of an iteration.
    pub fn from_agent_results(results: Vec<&AgentResult<T>>) -> Self {
        let msg = "Invalid within-day results";
        assert!(!results.is_empty(), "{msg}");
        let utility =
            Distribution::from_iterator(results.iter().map(|r| r.utility().expect(msg))).unwrap();
        AggregateConstantResults {
            count: results.len(),
            utility,
        }
    }
}
