//! Everything related to travel utility models.
use crate::units::{Time, Utility, ValueOfTime};

use num_traits::{Float, Zero};
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

/// Representation of how the travel utility of an agent is computed.
///
/// **Warning**: This is used to compute the travel *utility* (not the travel *cost*), which is
/// usually negative.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "values")]
#[schemars(example = "crate::schema::example_travel_utility")]
#[schemars(example = "crate::schema::example_travel_utility2")]
pub enum TravelUtility<T> {
    /// Travel utility is always null.
    None,
    /// Travel utility is proportional to the travel time.
    Proportional(ValueOfTime<T>),
    /// Travel utility is a quadratic function of travel time: `u = a * tt + b * tt^2`.
    Quadratic {
        /// First-degree coefficient.
        a: ValueOfTime<T>,
        /// Second-degree coefficient.
        b: ValueOfTime<T>,
    },
}

impl<T> Default for TravelUtility<T> {
    fn default() -> Self {
        Self::None
    }
}

impl<T: TTFNum> TravelUtility<T> {
    /// Returns the travel utility given the travel time.
    pub fn get_travel_utility(&self, travel_time: Time<T>) -> Utility<T> {
        match *self {
            Self::None => Utility::zero(),
            Self::Proportional(vot) => vot * travel_time,
            Self::Quadratic { a, b } => a * travel_time + b * travel_time.powi(2),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_travel_utility_test() {
        let tt = Time(5.);
        let model = TravelUtility::None;
        assert_eq!(model.get_travel_utility(tt), Utility::zero());
        let model = TravelUtility::Proportional(ValueOfTime(-10.));
        assert_eq!(model.get_travel_utility(tt), Utility(-50.));
        let model = TravelUtility::Quadratic {
            a: ValueOfTime(-30.),
            b: ValueOfTime(2.),
        };
        // -30 * 5 + 2 * 5^2 = -100
        assert_eq!(model.get_travel_utility(tt), Utility(-100.));
    }
}
