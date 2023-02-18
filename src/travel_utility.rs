// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to travel utility models.
use log::warn;
use schemars::JsonSchema;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use ttf::TTFNum;

use crate::units::{Time, Utility, ValueOfTime};

/// Representation of how the travel utility of an agent is computed.
///
/// **Warning**: This is used to compute the travel *utility* (not the travel *cost*), which is
/// usually negative.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
#[serde(from = "DeserTravelUtility<T>")]
#[serde(bound = "T: TTFNum")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
#[schemars(example = "crate::schema::example_travel_utility")]
#[schemars(example = "crate::schema::example_travel_utility2")]
pub enum TravelUtility<T> {
    /// Travel utility is a polynomial function of travel time (with degree 4):
    /// `u = a + b * tt + c * tt^2 + d * tt^3 + e * tt^4`.
    ///
    /// The constant, linear, quadratic and cubic function are special cases of this function.
    Polynomial(PolynomialFunction<T>),
}

impl<T: Default> Default for TravelUtility<T> {
    fn default() -> Self {
        Self::Polynomial(Default::default())
    }
}

impl<T: TTFNum> TravelUtility<T> {
    /// Returns the travel utility given the travel time.
    pub fn get_travel_utility(&self, travel_time: Time<T>) -> Utility<T> {
        match self {
            Self::Polynomial(function) => Utility(function.get_value(travel_time.0)),
        }
    }
}

/// A polynomial function of degree 4.
///
/// Constant, linear, quadratic and cubic functions are special cases.
#[derive(Clone, Debug, Default, PartialEq, Deserialize, Serialize, JsonSchema)]
#[serde(bound(serialize = "T: TTFNum"))]
#[schemars(bound = "T: TTFNum + JsonSchema")]
pub struct PolynomialFunction<T> {
    /// Coefficient of degree 0.
    #[serde(default)]
    #[serde(skip_serializing_if = "is_zero")]
    pub a: T,
    /// Coefficient of degree 1.
    #[serde(default)]
    #[serde(skip_serializing_if = "is_zero")]
    pub b: T,
    /// Coefficient of degree 2.
    #[serde(default)]
    #[serde(skip_serializing_if = "is_zero")]
    pub c: T,
    /// Coefficient of degree 3.
    #[serde(default)]
    #[serde(skip_serializing_if = "is_zero")]
    pub d: T,
    /// Coefficient of degree 4.
    #[serde(default)]
    #[serde(skip_serializing_if = "is_zero")]
    pub e: T,
}

impl<T: TTFNum> PolynomialFunction<T> {
    fn get_value(&self, x: T) -> T {
        self.a + x * (self.b + x * (self.c + x * (self.d + x * self.e)))
    }
}

fn is_zero<T: Default + PartialEq>(x: &T) -> bool {
    x == &T::default()
}

/// Equivalent of [TravelUtility] that is used for deserializiation.
///
/// This allows backward-compatibility with deprecated fields.
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "type", content = "value")]
#[serde(bound(deserialize = "T: Default + DeserializeOwned"))]
enum DeserTravelUtility<T> {
    /// Utility is always zero.
    None,
    /// Utility is a proportional to travel time, i.e., the given value is the value of the
    /// coefficient of degree 1 in the polynomial function.
    Proportional(ValueOfTime<T>),
    /// Utility is a quadratic function of travel time (with no constant).
    Quadratic {
        /// Coefficient of degree 1.
        a: ValueOfTime<T>,
        /// Coefficient of degree 2.
        b: ValueOfTime<T>,
    },
    /// See [TravelUtility].
    Polynomial(PolynomialFunction<T>),
}

impl<T: Default> From<DeserTravelUtility<T>> for TravelUtility<T> {
    fn from(value: DeserTravelUtility<T>) -> Self {
        match value {
            DeserTravelUtility::None => {
                warn!("Type `None` is deprecated for `travel_utility` and will be removed in the future");
                Self::Polynomial(PolynomialFunction {
                    a: T::default(),
                    b: T::default(),
                    c: T::default(),
                    d: T::default(),
                    e: T::default(),
                })
            }
            DeserTravelUtility::Proportional(a) => {
                warn!("Type `Proportional` is deprecated for `travel_utility` and will be removed in the future");
                Self::Polynomial(PolynomialFunction {
                    a: T::default(),
                    b: a.0,
                    c: T::default(),
                    d: T::default(),
                    e: T::default(),
                })
            }
            DeserTravelUtility::Quadratic { a, b } => {
                warn!("Type `Quadratic` is deprecated for `travel_utility` and will be removed in the future");
                Self::Polynomial(PolynomialFunction {
                    a: T::default(),
                    b: a.0,
                    c: b.0,
                    d: T::default(),
                    e: T::default(),
                })
            }
            DeserTravelUtility::Polynomial(f) => Self::Polynomial(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;

    use super::*;

    #[test]
    fn deser_travel_utility_test() {
        let js = "{
            \"type\": \"None\"
        }";
        let u = serde_json::from_str::<TravelUtility<f64>>(js).unwrap();
        assert_eq!(u, TravelUtility::default());

        let js = "{
            \"type\": \"Proportional\",
            \"value\": 10.0
        }";
        let u = serde_json::from_str::<TravelUtility<f64>>(js).unwrap();
        assert_eq!(
            u,
            TravelUtility::Polynomial(PolynomialFunction {
                b: 10.,
                ..Default::default()
            })
        );

        let js = "{
            \"type\": \"Quadratic\",
            \"value\": {
                \"a\": 1.0,
                \"b\": 2.0
            }
        }";
        let u = serde_json::from_str::<TravelUtility<f64>>(js).unwrap();
        assert_eq!(
            u,
            TravelUtility::Polynomial(PolynomialFunction {
                b: 1.,
                c: 2.,
                ..Default::default()
            })
        );

        let js = "{
            \"type\": \"Polynomial\",
            \"value\": {
                \"a\": 1.0,
                \"b\": 2.0,
                \"c\": 3.0,
                \"d\": 4.0,
                \"e\": 5.0
            }
        }";
        let u = serde_json::from_str::<TravelUtility<f64>>(js).unwrap();
        assert_eq!(
            u,
            TravelUtility::Polynomial(PolynomialFunction {
                a: 1.,
                b: 2.,
                c: 3.,
                d: 4.,
                e: 5.,
                ..Default::default()
            })
        );

        let js = "{
            \"type\": \"Polynomial\",
            \"value\": {
            }
        }";
        let u = serde_json::from_str::<TravelUtility<f64>>(js).unwrap();
        assert_eq!(u, TravelUtility::default());
    }

    #[test]
    fn get_travel_utility_test() {
        let tt = Time(5.);

        let model = TravelUtility::default();
        assert_eq!(model.get_travel_utility(tt), Utility::zero());

        let model = TravelUtility::Polynomial(PolynomialFunction {
            b: -10.,
            ..Default::default()
        });
        assert_eq!(model.get_travel_utility(tt), Utility(-50.));

        let model = TravelUtility::Polynomial(PolynomialFunction {
            b: -30.,
            c: 2.,
            ..Default::default()
        });
        // -30 * 5 + 2 * 5^2 = -100.
        assert_eq!(model.get_travel_utility(tt), Utility(-100.));

        let model = TravelUtility::Polynomial(PolynomialFunction {
            a: 4.,
            b: 3.,
            c: 2.,
            d: 1.,
            ..Default::default()
        });
        // 4 + 3 * 5 + 2 * 5^2 + 1 * 5^3 = 194.
        assert_eq!(model.get_travel_utility(tt), Utility(194.));

        let model = TravelUtility::Polynomial(PolynomialFunction {
            a: 5.,
            b: 4.,
            c: 3.,
            d: 2.,
            e: 1.,
            ..Default::default()
        });
        // 5 + 4 * 5 + 3 * 5^2 + 2 * 5^3 + 1 * 5^4 = 975.
        assert_eq!(model.get_travel_utility(tt), Utility(975.));
    }
}
