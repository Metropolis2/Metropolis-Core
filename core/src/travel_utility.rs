// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to travel utility models.
use num_traits::{Float, Zero};

use crate::units::{Time, Utility, ValueOfTime};

/// Representation of how the travel utility of an agent is computed.
///
/// **Warning**: This is used to compute the travel *utility* (not the travel *cost*), which is
/// usually negative.
#[derive(Clone, Debug, PartialEq)]
pub enum TravelUtility {
    /// Travel utility is a polynomial function of travel time (with degree 4):
    /// `u = a + b * tt + c * tt^2 + d * tt^3 + e * tt^4`.
    ///
    /// The constant, linear, quadratic and cubic function are special cases of this function.
    Polynomial(PolynomialFunction),
}

impl Default for TravelUtility {
    fn default() -> Self {
        Self::Polynomial(Default::default())
    }
}

impl TravelUtility {
    pub(crate) fn from_values(
        a: Option<f64>,
        b: Option<f64>,
        c: Option<f64>,
        d: Option<f64>,
        e: Option<f64>,
    ) -> Self {
        Self::Polynomial(PolynomialFunction {
            a: Utility(a.unwrap_or_default()),
            b: ValueOfTime(b.unwrap_or_default()),
            c: ValueOfTime(c.unwrap_or_default()),
            d: ValueOfTime(d.unwrap_or_default()),
            e: ValueOfTime(e.unwrap_or_default()),
        })
    }

    /// Returns the travel utility given the travel time.
    pub fn get_travel_utility(&self, travel_time: Time) -> Utility {
        match self {
            Self::Polynomial(function) => function.get_value(travel_time),
        }
    }
}

/// A polynomial function of degree 4.
///
/// Constant, linear, quadratic and cubic functions are special cases.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct PolynomialFunction {
    /// Coefficient of degree 0.
    pub a: Utility,
    /// Coefficient of degree 1.
    pub b: ValueOfTime,
    /// Coefficient of degree 2.
    pub c: ValueOfTime,
    /// Coefficient of degree 3.
    pub d: ValueOfTime,
    /// Coefficient of degree 4.
    pub e: ValueOfTime,
}

impl PolynomialFunction {
    fn get_value(&self, x: Time) -> Utility {
        let mut v = self.a;
        if !self.b.is_zero() {
            v += x * self.b;
        }
        if !self.c.is_zero() {
            v += x.powi(2) * self.c;
        }
        if !self.d.is_zero() {
            v += x.powi(3) * self.d;
        }
        if !self.e.is_zero() {
            v += x.powi(4) * self.e;
        }
        v
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;

    use super::*;

    #[test]
    fn get_travel_utility_test() {
        let tt = Time(5.);

        let model = TravelUtility::default();
        assert_eq!(model.get_travel_utility(tt), Utility::zero());

        let model = TravelUtility::Polynomial(PolynomialFunction {
            b: ValueOfTime(-10.),
            ..Default::default()
        });
        assert_eq!(model.get_travel_utility(tt), Utility(-50.));

        let model = TravelUtility::Polynomial(PolynomialFunction {
            b: ValueOfTime(-30.),
            c: ValueOfTime(2.),
            ..Default::default()
        });
        // -30 * 5 + 2 * 5^2 = -100.
        assert_eq!(model.get_travel_utility(tt), Utility(-100.));

        let model = TravelUtility::Polynomial(PolynomialFunction {
            a: Utility(4.),
            b: ValueOfTime(3.),
            c: ValueOfTime(2.),
            d: ValueOfTime(1.),
            ..Default::default()
        });
        // 4 + 3 * 5 + 2 * 5^2 + 1 * 5^3 = 194.
        assert_eq!(model.get_travel_utility(tt), Utility(194.));

        let model = TravelUtility::Polynomial(PolynomialFunction {
            a: Utility(5.),
            b: ValueOfTime(4.),
            c: ValueOfTime(3.),
            d: ValueOfTime(2.),
            e: ValueOfTime(1.),
            ..Default::default()
        });
        // 5 + 4 * 5 + 3 * 5^2 + 2 * 5^3 + 1 * 5^4 = 975.
        assert_eq!(model.get_travel_utility(tt), Utility(975.));
    }
}
