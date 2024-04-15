// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to modes of transportation.
use std::fmt;

use anyhow::{Context, Result};
use enum_as_inner::EnumAsInner;

use self::trip::results::{AggregateTripResults, PreDayTripResults, TripResults};
use self::trip::{Leg, TravelingMode};
use crate::event::Event;
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::skim::EAAllocation;
use crate::network::road_network::RoadNetworkWeights;
use crate::network::{NetworkPreprocessingData, NetworkSkim, NetworkWeights};
use crate::population::AgentIndex;
use crate::progress_bar::MetroProgressBar;
use crate::units::{Distribution, NonNegativeSeconds, Utility};

pub mod trip;

/// Mode identifier.
///
/// The `n` modes of an [Agent](crate::agent::Agent) are indexed from `0` to `n-1`.
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
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
#[derive(Clone, Debug, EnumAsInner)]
pub enum Mode {
    /// An activity (e.g., staying home, traveling) that always provide the same utility level.
    Constant((usize, Utility)),
    /// A trip consisting in a sequence of legs (either on the road or virtual).
    Trip(TravelingMode),
}

impl Mode {
    /// Returns the id of the mode.
    pub fn id(&self) -> usize {
        match self {
            Self::Constant((id, _)) => *id,
            Self::Trip(mode) => mode.id,
        }
    }
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant((id, _)) => write!(f, "Constant {id}"),
            Self::Trip(mode) => write!(f, "Trip {}", mode.id),
        }
    }
}

impl Mode {
    /// Creates a `Mode` from input values.
    ///
    /// Returns an error if some values are invalid.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_values(
        id: usize,
        origin_delay: Option<f64>,
        dt_choice_type: Option<&str>,
        dt_choice_departure_time: Option<f64>,
        dt_choice_period: Option<Vec<f64>>,
        dt_choice_interval: Option<f64>,
        dt_choice_offset: Option<f64>,
        dt_choice_model_type: Option<&str>,
        dt_choice_model_u: Option<f64>,
        dt_choice_model_mu: Option<f64>,
        dt_choice_model_constants: Option<Vec<f64>>,
        constant_utility: Option<f64>,
        total_travel_utility_one: Option<f64>,
        total_travel_utility_two: Option<f64>,
        total_travel_utility_three: Option<f64>,
        total_travel_utility_four: Option<f64>,
        origin_utility_type: Option<&str>,
        origin_utility_tstar: Option<f64>,
        origin_utility_beta: Option<f64>,
        origin_utility_gamma: Option<f64>,
        origin_utility_delta: Option<f64>,
        destination_utility_type: Option<&str>,
        destination_utility_tstar: Option<f64>,
        destination_utility_beta: Option<f64>,
        destination_utility_gamma: Option<f64>,
        destination_utility_delta: Option<f64>,
        pre_compute_route: Option<bool>,
        legs: Option<Vec<Leg>>,
    ) -> Result<Self> {
        let legs = legs.unwrap_or_default();
        if legs.is_empty() {
            let constant_utility = Utility::try_from(constant_utility.unwrap_or(0.0))
                .context("Value `constant_utility` does not satisfy the constraints")?;
            Ok(Self::Constant((id, constant_utility)))
        } else {
            Ok(Self::Trip(TravelingMode::from_values(
                id,
                origin_delay,
                dt_choice_type,
                dt_choice_departure_time,
                dt_choice_period,
                dt_choice_interval,
                dt_choice_offset,
                dt_choice_model_type,
                dt_choice_model_u,
                dt_choice_model_mu,
                dt_choice_model_constants,
                constant_utility,
                total_travel_utility_one,
                total_travel_utility_two,
                total_travel_utility_three,
                total_travel_utility_four,
                origin_utility_type,
                origin_utility_tstar,
                origin_utility_beta,
                origin_utility_gamma,
                origin_utility_delta,
                destination_utility_type,
                destination_utility_tstar,
                destination_utility_beta,
                destination_utility_gamma,
                destination_utility_delta,
                pre_compute_route,
                legs,
            )?))
        }
    }

    /// This method returns the results of the pre-day model (expected utility and [ModeCallback])
    /// for a given [Mode], [NetworkSkim] and [NetworkPreprocessingData].
    pub fn get_pre_day_choice<'a>(
        &'a self,
        weights: &'a NetworkWeights,
        exp_skims: &'a NetworkSkim,
        preprocess_data: &'a NetworkPreprocessingData,
        progress_bar: MetroProgressBar,
    ) -> Result<(Utility, ModeCallback<'a>)> {
        match self {
            Self::Constant((_, u)) => Ok((*u, Box::new(|_| Ok(ModeResults::Constant(*u))))),
            Self::Trip(mode) => mode.get_pre_day_choice(
                weights.road_network(),
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
pub type ModeCallback<'a> = Box<dyn FnOnce(&'a mut EAAllocation) -> Result<ModeResults> + 'a>;

/// Additional mode-specific results for an agent.
#[derive(Debug, Clone, PartialEq, EnumAsInner)]
pub enum ModeResults {
    /// Results for a traveling mode.
    Trip(TripResults),
    /// Results for a constant-utility alternative.
    Constant(Utility),
}

impl ModeResults {
    /// Returns the departure time of the trip (if any).
    pub fn departure_time(&self) -> Option<NonNegativeSeconds> {
        match self {
            Self::Trip(trip_results) => Some(trip_results.departure_time),
            Self::Constant(_) => None,
        }
    }
}

impl ModeResults {
    /// Clones and resets the mode results in prevision for a new day.
    pub fn reset(&self) -> Self {
        match self {
            Self::Trip(trip_results) => Self::Trip(trip_results.reset()),
            Self::Constant(u) => Self::Constant(*u),
        }
    }

    /// Returns `true` if the trip or activity is finished, i.e., there is nothing more to simulate
    /// in the within-day model.
    pub fn is_finished(&self) -> bool {
        match self {
            Self::Trip(trip_results) => trip_results.is_finished(),
            Self::Constant(_) => true,
        }
    }
}

impl ModeResults {
    /// Returns the initial event associated with the mode (if any).
    pub(crate) fn get_event(
        &self,
        agent_id: AgentIndex,
        mode_id: ModeIndex,
    ) -> Option<Box<dyn Event>> {
        match self {
            Self::Trip(trip_results) => trip_results.get_event(agent_id, mode_id),
            Self::Constant(_) => None,
        }
    }

    /// Adds some informations to the [ModeResults], using the [ModeResults] of the previous
    /// iteration.
    ///
    /// This function is executed only when the same mode has been chosen for the previous
    /// iteration.
    pub(crate) fn with_previous_results(&mut self, previous_results: &Self) {
        match self {
            Self::Trip(trip_results) => {
                // The unwrap is safe as the same mode has been chosen for the two iterations.
                trip_results.with_previous_results(previous_results.as_trip().unwrap())
            }
            Self::Constant(_) => (),
        }
    }
}

/// Additional mode-specific pre-day results for an agent.
#[derive(Debug, Clone, PartialEq, EnumAsInner)]
pub enum PreDayModeResults {
    /// Results for a traveling mode.
    Trip(PreDayTripResults),
    /// Alternative for modes or activities that do not recquire additional results.
    Constant(Utility),
}

impl From<ModeResults> for PreDayModeResults {
    fn from(value: ModeResults) -> Self {
        match value {
            ModeResults::Trip(trip_results) => Self::Trip(trip_results.into()),
            ModeResults::Constant(u) => Self::Constant(u),
        }
    }
}

impl PreDayModeResults {
    pub(crate) fn add_expected_route(
        &mut self,
        mode: &Mode,
        weights: &RoadNetworkWeights,
        unique_vehicles: &UniqueVehicles,
    ) {
        match self {
            Self::Trip(trip_results) => {
                trip_results.add_expected_route(mode.as_trip().unwrap(), weights, unique_vehicles)
            }
            Self::Constant(_) => (),
        }
    }
}

/// Aggregate results of an iteration that are mode-specific.
#[derive(Debug, Clone)]
pub(crate) struct AggregateModeResults {
    /// Results specific to traveling modes.
    pub(crate) trip_modes: Option<AggregateTripResults>,
    /// Results specific to constant modes.
    pub(crate) constant: Option<AggregateConstantResults>,
}

/// Aggregate results of an iteration specific to constant modes.
#[derive(Debug, Clone)]
pub(crate) struct AggregateConstantResults {
    /// Number of agents who chose a constant mode.
    pub(crate) count: usize,
    /// Distribution of the utility of the agents who chose a constant mode.
    pub(crate) utility: Distribution<Utility>,
}

impl AggregateConstantResults {
    /// Creates a new [AggregateConstantResults] from a vector of [Utility].
    pub(crate) fn from_utilities(utilities: Vec<Utility>) -> Self {
        Self {
            count: utilities.len(),
            utility: Distribution::from_iterator(utilities.into_iter()).unwrap(),
        }
    }
}
