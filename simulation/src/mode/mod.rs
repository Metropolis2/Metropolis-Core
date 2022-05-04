use crate::agent::AgentIndex;
use crate::event::Event;
use crate::network::NetworkSkim;
use crate::schedule_utility::ScheduleUtility;
use crate::units::{Time, Utility};
use car::{AggregateCarResults, CarAlternative, CarChoiceAllocation, CarChoices, CarResults};

use anyhow::Result;
use serde_derive::{Deserialize, Serialize};
use std::fmt;
use ttf::TTFNum;

pub mod car;

#[derive(
    Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash, Deserialize, Serialize,
)]
pub struct ModeIndex(usize);

impl ModeIndex {
    pub fn new(x: usize) -> Self {
        ModeIndex(x)
    }

    pub fn index(self) -> usize {
        self.0
    }
}

pub fn mode_index(x: usize) -> ModeIndex {
    ModeIndex::new(x)
}

/// Mode of transportation available to an agent.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Mode<T> {
    Constant((ModeIndex, Utility<T>)),
    Car((ModeIndex, CarAlternative<T>)),
}

impl<T> fmt::Display for Mode<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(_) => write!(f, "Constant"),
            Self::Car(_) => write!(f, "Car"),
        }
    }
}

impl<T> Mode<T> {
    pub fn get_index(&self) -> ModeIndex {
        match self {
            Self::Constant((id, _)) => *id,
            Self::Car((id, _)) => *id,
        }
    }
}

impl<T: TTFNum> Mode<T> {
    /// This method returns the results of the pre-day model (expected utility and [ModeCallback])
    /// for `self`, given a [NetworkSkim] and a [ScheduleUtility].
    ///
    /// The lifetime of `self` must be larger than the lifetime of the [NetworkSkim].
    /// The callback borrows both the mode and the network skim but returns something than only
    /// borrows from the network skim.
    pub fn make_pre_day_choice<'a>(
        &'a self,
        exp_skims: &'a NetworkSkim<T>,
        schedule_utility: &ScheduleUtility<T>,
    ) -> Result<(Utility<T>, ModeCallback<'a, T>)> {
        match self {
            Self::Constant((_, u)) => Ok((*u, Box::new(|_| Ok(PreDayChoices::None)))),
            Self::Car((_, mode)) => mode.make_pre_day_choice(exp_skims, schedule_utility),
        }
    }

    pub fn get_utility(
        &self,
        results: &ModeResults<T>,
        schedule_utility: &ScheduleUtility<T>,
        departure_time: Option<Time<T>>,
        arrival_time: Option<Time<T>>,
    ) -> Utility<T> {
        match self {
            Self::Constant((_, u)) => *u,
            Self::Car((_, mode)) => {
                if let ModeResults::Car(car_results) = results {
                    assert!(
                        car_results
                            .total_travel_time()
                            .approx_eq(&(arrival_time.unwrap() - departure_time.unwrap())),
                        "{:?} != {:?}",
                        car_results.total_travel_time(),
                        arrival_time.unwrap() - departure_time.unwrap()
                    );
                    mode.get_utility(
                        car_results,
                        schedule_utility,
                        departure_time.unwrap(),
                        arrival_time.unwrap(),
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
/// The callback function takes no argument and returns an object that implements [PreDayChoices].
///
/// For an agent with multiple modes, only the callback function of the mode chosen in the pre-day
/// model is called.
pub type ModeCallback<'a, T> =
    Box<dyn FnOnce(&mut PreDayChoiceAllocation<T>) -> Result<PreDayChoices<T>> + 'a>;

/// Enum representing the pre-day choices for a given mode.
#[derive(Debug, Clone, Serialize)]
pub enum PreDayChoices<T> {
    Car(CarChoices<T>),
    None,
}

impl<T: TTFNum + 'static> PreDayChoices<T> {
    /// This method returns (optionally) an [Event] that represents the start of the trip,
    /// corresponding to the pre-day choices.
    pub fn get_event(&self, agent: AgentIndex) -> Option<Box<dyn Event<T>>> {
        match self {
            Self::Car(choices) => choices.get_event(agent),
            Self::None => None,
        }
    }
}

impl<T: TTFNum> PreDayChoices<T> {
    /// This method returns a [WithinDayResult], compatible with the pre-day choices.
    ///
    /// For modes with events during the within-day model, the [WithinDayResult] is filled during
    /// the within-day model (e.g., with the route and arrival time).
    pub fn init_mode_results(&self) -> ModeResults<T> {
        match self {
            Self::Car(choices) => choices.init_mode_results(),
            Self::None => ModeResults::None,
        }
    }

    pub fn get_departure_time(&self) -> Option<Time<T>> {
        match self {
            Self::Car(choices) => Some(choices.get_departure_time()),
            Self::None => None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct PreDayChoiceAllocation<T: TTFNum> {
    car_alloc: CarChoiceAllocation<T>,
}

/// Enum representing the different mode-specific results that can be stored in a
/// [WithinDayResult].
#[derive(Debug, Clone, Serialize)]
pub enum ModeResults<T> {
    Car(CarResults<T>),
    None,
}

#[derive(Debug, Clone, Serialize)]
pub enum AggregateModeResults<T> {
    // AggregateCarResults is boxed to reduce the size of the enum.
    Car(Box<AggregateCarResults<T>>),
    Constant(usize),
}
