use crate::units::{Time, Utility, ValueOfTime};

use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

/// Representation of how the travel utility of an agent is computed.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum TravelUtility<T> {
    /// Travel utility is proportional to the travel time.
    Proportional(ValueOfTime<T>),
}

impl<T: TTFNum> TravelUtility<T> {
    /// Return the travel utility given the travel time.
    pub fn get_travel_utility(&self, travel_time: Time<T>) -> Utility<T> {
        match self {
            Self::Proportional(vot) => *vot * travel_time,
        }
    }
}
