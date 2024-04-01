// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Definition of types representing values expressed in a given unit.
//!
//! The types assumed the following units:
//!
//! - [Length]: in meters
//! - [Time]: in seconds
//! - [Speed]: in meter per second
//! - [ValueOfTime]: in utility per second
//! - [PCE] (Passenger Car Equivalent): in passenger car
//! - [Flow]: in PCE per second
//!
//! Other units can be assumed but the coherence between units must be kept.
//! For example, if one consider that lengths are expressed in miles, then speeds must be expressed
//! in miles per second.
use std::cmp::Ordering;
use std::fmt;
use std::iter;
use std::num::FpCategory;
use std::ops::*;

use num_traits::{Float, FromPrimitive, Num, NumCast, One, ToPrimitive, Zero};
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

// To implement TTFNum, we first have to implement `Float` and its requirements.
// When the following issue is solve we could use the crate `num-derive` instead:
// https://github.com/rust-num/num-derive/pull/37
macro_rules! impl_ttf_on_unit(
    ( $( $t:ident ),* ) => {
        $(
            impl Add for $t {
                type Output = Self;
                fn add(self, rhs: Self) -> Self::Output {
                    Self(self.0 + rhs.0)
                }
            }

            impl AddAssign for $t {
                fn add_assign(&mut self, rhs: Self) {
                    self.0 += rhs.0;
                }
            }

            impl Sub for $t {
                type Output = Self;
                fn sub(self, rhs: Self) -> Self::Output {
                    Self(self.0 - rhs.0)
                }
            }

            impl SubAssign for $t {
                fn sub_assign(&mut self, rhs: Self) {
                    self.0 -= rhs.0;
                }
            }

            impl Mul for $t {
                type Output = Self;
                fn mul(self, rhs: Self) -> Self::Output {
                    Self(self.0 * rhs.0)
                }
            }

            impl MulAssign for $t {
                fn mul_assign(&mut self, rhs: Self) {
                    self.0 *= rhs.0;
                }
            }

            impl Div for $t {
                type Output = Self;
                fn div(self, rhs: Self) -> Self::Output {
                    Self(self.0 / rhs.0)
                }
            }

            impl DivAssign for $t {
                fn div_assign(&mut self, rhs: Self) {
                    self.0 /= rhs.0;
                }
            }

            impl Rem for $t {
                type Output = Self;
                fn rem(self, rhs: Self) -> Self::Output {
                    Self(self.0 % rhs.0)
                }
            }

            impl RemAssign for $t {
                fn rem_assign(&mut self, rhs: Self) {
                    self.0 %= rhs.0;
                }
            }

            impl Neg for $t {
                type Output = Self;
                fn neg(self) -> Self::Output {
                    Self(self.0.neg())
                }
            }

            impl Zero for $t {
                fn zero() -> Self {
                    Self(0.0)
                }
                fn is_zero(&self) -> bool {
                    self.0.is_zero()
                }
            }

            impl One for $t {
                fn one() -> Self {
                    Self(1.0)
                }
            }

            impl FromPrimitive for $t {
                fn from_i64(n: i64) -> Option<Self> {
                    Some(Self(n as f64))
                }
                fn from_u64(n: u64) -> Option<Self> {
                    Some(Self(n as f64))
                }
                fn from_f32(n: f32) -> Option<Self> {
                    Some(Self(n as f64))
                }
                fn from_f64(n: f64) -> Option<Self> {
                    Some(Self(n))
                }
            }

            impl ToPrimitive for $t {
                fn to_i64(&self) -> Option<i64> {
                    self.0.to_i64()
                }
                fn to_u64(&self) -> Option<u64> {
                    self.0.to_u64()
                }
                fn to_f32(&self) -> Option<f32> {
                    self.0.to_f32()
                }
                fn to_f64(&self) -> Option<f64> {
                    self.0.to_f64()
                }
            }

            impl NumCast for $t {
                fn from<U: ToPrimitive>(n: U) -> Option<Self> {
                    n.to_f64().map(Self)
                }
            }

            impl Num for $t {
                type FromStrRadixErr = <f64 as Num>::FromStrRadixErr;
                fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                    f64::from_str_radix(str, radix).map(Self)
                }
            }

            impl Float for $t {
                fn nan() -> Self {
                    Self(f64::NAN)
                }
                fn infinity() -> Self {
                    Self(f64::INFINITY)
                }
                fn neg_infinity() -> Self {
                    Self(f64::NEG_INFINITY)
                }
                fn neg_zero() -> Self {
                    Self(f64::neg_zero())
                }
                fn min_value() -> Self {
                    Self(f64::min_value())
                }
                fn min_positive_value() -> Self {
                    Self(f64::min_positive_value())
                }
                fn max_value() -> Self {
                    Self(f64::max_value())
                }
                fn is_nan(self) -> bool {
                    self.0.is_nan()
                }
                fn is_infinite(self) -> bool {
                    self.0.is_infinite()
                }
                fn is_finite(self) -> bool {
                    self.0.is_finite()
                }
                fn is_normal(self) -> bool {
                    self.0.is_normal()
                }
                fn classify(self) -> FpCategory {
                    self.0.classify()
                }
                fn floor(self) -> Self {
                    Self(self.0.floor())
                }
                fn ceil(self) -> Self {
                    Self(self.0.ceil())
                }
                fn round(self) -> Self {
                    Self(self.0.round())
                }
                fn trunc(self) -> Self {
                    Self(self.0.trunc())
                }
                fn fract(self) -> Self {
                    Self(self.0.fract())
                }
                fn abs(self) -> Self {
                    Self(self.0.abs())
                }
                fn signum(self) -> Self {
                    Self(self.0.signum())
                }
                fn is_sign_positive(self) -> bool {
                    self.0.is_sign_positive()
                }
                fn is_sign_negative(self) -> bool {
                    self.0.is_sign_negative()
                }
                fn mul_add(self, a: Self, b: Self) -> Self {
                    Self(self.0.mul_add(a.0, b.0))
                }
                fn recip(self) -> Self {
                    Self(self.0.recip())
                }
                fn powi(self, n: i32) -> Self {
                    Self(self.0.powi(n))
                }
                fn powf(self, n: Self) -> Self {
                    Self(self.0.powf(n.0))
                }
                fn sqrt(self) -> Self {
                    Self(self.0.sqrt())
                }
                fn exp(self) -> Self {
                    Self(self.0.exp())
                }
                fn exp2(self) -> Self {
                    Self(self.0.exp2())
                }
                fn ln(self) -> Self {
                    Self(self.0.ln())
                }
                fn log(self, base: Self) -> Self {
                    Self(self.0.log(base.0))
                }
                fn log2(self) -> Self {
                    Self(self.0.log2())
                }
                fn log10(self) -> Self {
                    Self(self.0.log10())
                }
                fn max(self, other: Self) -> Self {
                    Self(self.0.max(other.0))
                }
                fn min(self, other: Self) -> Self {
                    Self(self.0.min(other.0))
                }
                fn abs_sub(self, other: Self) -> Self {
                    Self((self.0 - other.0).max(0.0))
                }
                fn cbrt(self) -> Self {
                    Self(self.0.cbrt())
                }
                fn hypot(self, other: Self) -> Self {
                    Self(self.0.hypot(other.0))
                }
                fn sin(self) -> Self {
                    Self(self.0.sin())
                }
                fn cos(self) -> Self {
                    Self(self.0.cos())
                }
                fn tan(self) -> Self {
                    Self(self.0.tan())
                }
                fn asin(self) -> Self {
                    Self(self.0.asin())
                }
                fn acos(self) -> Self {
                    Self(self.0.acos())
                }
                fn atan(self) -> Self {
                    Self(self.0.atan())
                }
                fn atan2(self, other: Self) -> Self {
                    Self(self.0.atan2(other.0))
                }
                fn sin_cos(self) -> (Self, Self) {
                    let (sin, cos) = self.0.sin_cos();
                    (Self(sin), Self(cos))
                }
                fn exp_m1(self) -> Self {
                    Self(self.0.exp_m1())
                }
                fn ln_1p(self) -> Self {
                    Self(self.0.ln_1p())
                }
                fn sinh(self) -> Self {
                    Self(self.0.sinh())
                }
                fn cosh(self) -> Self {
                    Self(self.0.cosh())
                }
                fn tanh(self) -> Self {
                    Self(self.0.tanh())
                }
                fn asinh(self) -> Self {
                    Self(self.0.asinh())
                }
                fn acosh(self) -> Self {
                    Self(self.0.acosh())
                }
                fn atanh(self) -> Self {
                    Self(self.0.atanh())
                }
                fn integer_decode(self) -> (u64, i16, i8) {
                    self.0.integer_decode()
                }
            }

            impl TTFNum for $t {
                fn approx_eq(&self, other: &Self) -> bool {
                    self.0.approx_eq(&other.0)
                }
                fn margin() -> Self {
                    Self(f64::margin())
                }
                fn average(self, other: Self) -> Self {
                    Self(self.0.average(other.0))
                }
            }

            impl Eq for $t {
            }

            #[allow(clippy::derive_ord_xor_partial_ord)]
            impl Ord for $t {
                fn cmp(&self, other: &Self) -> Ordering {
                    self.partial_cmp(other).unwrap()
                }
            }

            impl From<f64> for $t {
                fn from(value: f64) -> $t {
                    $t(value)
                }
            }

            impl iter::Sum for $t {
                fn sum<I>(iter: I) -> Self
                    where I: Iterator<Item = $t>
                {
                    iter.fold($t::zero(), |a, b| a + b)
                }
            }
        )*
    };
);

macro_rules! impl_from_into_no_unit(
    ( $( $t:ident ),* ) => {
        $(
            impl From<$t> for NoUnit {
                fn from(value: $t) -> NoUnit {
                    NoUnit(value.0)
                }
            }

            impl From<NoUnit> for $t {
                fn from(value: NoUnit) -> $t {
                    $t(value.0)
                }
            }
        )*
    };
);

/// Representation of a value with no particular unit.
///
/// This type is used to implement the conversion between any unit type and the `NoUnit` type
/// because it is not possible to implement the conversion directly between a type `Unit` and
/// `T`.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(transparent)]
pub struct NoUnit(pub f64);

impl fmt::Display for NoUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Representation of time duration or timestamp, expressed in seconds.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct Time(pub f64);

impl fmt::Display for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let seconds = self.0.round().to_u64().ok_or(fmt::Error)?;
        let hour = seconds / 3600;
        let minute = seconds % 3600 / 60;
        let second = seconds % 60;
        write!(f, "{hour:02}:{minute:02}:{second:02}")
    }
}

/// Representation of a utility (or monetary) amount.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct Utility(pub f64);

impl fmt::Display for Utility {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Representation of a value of time, i.e., a utility amount per time unit, expressed in utility
/// unit per second.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct ValueOfTime(pub f64);

impl fmt::Display for ValueOfTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} utility/s", self.0)
    }
}

/// Representation of a length, expressed in meters.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct Length(pub f64);

impl fmt::Display for Length {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} m", self.0)
    }
}

/// Representation of a number of lanes.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct Lanes(pub f64);

impl fmt::Display for Lanes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} lanes", self.0)
    }
}

/// Representation of a speed, expressed in meters per second.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct Speed(pub f64);

impl fmt::Display for Speed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} m/s", self.0)
    }
}

/// Unit type for passenger car equivalent.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct PCE(pub f64);

impl fmt::Display for PCE {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} PCE", self.0)
    }
}

/// Representation of a flow of vehicle, in PCE (passenger car equivalent) per second.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
pub struct Flow(pub f64);

impl fmt::Display for Flow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} PCE/s", self.0)
    }
}

impl_ttf_on_unit!(
    Time,
    Utility,
    ValueOfTime,
    Lanes,
    Length,
    Speed,
    PCE,
    Flow,
    NoUnit
);

impl_from_into_no_unit!(Time, Utility, ValueOfTime, Lanes, Length, Speed, PCE, Flow);

macro_rules! impl_ops(
    ( $l_type:ident * $r_type:ident = $o_type:ident ) => {
        impl Mul<$r_type> for $l_type {
            type Output = $o_type;
            fn mul(self, other: $r_type) -> Self::Output {
                $o_type(self.0 * other.0)
            }
        }
        impl Mul<$l_type> for $r_type {
            type Output = $o_type;
            fn mul(self, other: $l_type) -> Self::Output {
                $o_type(self.0 * other.0)
            }
        }
    };
    ( $l_type:ident / $r_type:ident = $o_type:ident ) => {
        impl Div<$r_type> for $l_type {
            type Output = $o_type;
            fn div(self, other: $r_type) -> Self::Output {
                $o_type(self.0 / other.0)
            }
        }
    };
);

impl_ops!(ValueOfTime * Time = Utility);
impl_ops!(Speed * Time = Length);
impl_ops!(Length / Speed = Time);
impl_ops!(Length / Time = Speed);
impl_ops!(Flow * Time = PCE);
impl_ops!(PCE / Flow = Time);
impl_ops!(PCE / Time = Flow);
impl_ops!(Length * Lanes = Length);
impl_ops!(Flow * Lanes = Flow);

/// An interval between two [Time] units.
#[derive(Default, Clone, Copy, Debug, Deserialize, Serialize)]
pub struct Interval(pub [Time; 2]);

impl Interval {
    /// Returns the start of the interval.
    pub const fn start(&self) -> Time {
        self.0[0]
    }

    /// Returns the end of the interval.
    pub const fn end(&self) -> Time {
        self.0[1]
    }

    /// Returns the interval as a vector of two [Time] values.
    pub fn to_vec(&self) -> Vec<Time> {
        self.0.to_vec()
    }
}

impl Interval {
    /// Returns `true` if `time` is included in the (closed) interval.
    pub fn contains(&self, time: Time) -> bool {
        self.start() <= time && self.end() >= time
    }
}

impl Interval {
    /// Returns the length of the interval, i.e., the time that elapses between the start and the
    /// end of the interval.
    pub fn length(&self) -> Time {
        self.0[1] - self.0[0]
    }
}

/// Struct to describe statistics on a distribution.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct Distribution<T> {
    mean: T,
    std: T,
    min: T,
    max: T,
}

impl<T: TTFNum> Distribution<T> {
    /// Returns a `Distribution` from an iterator of elements of the distribution.
    ///
    /// Returns `None` if the iterator is empty.
    pub fn from_iterator(iter: impl Iterator<Item = T>) -> Option<Distribution<T>> {
        let mut sum = T::zero();
        let mut sum_squared = T::zero();
        let mut min = T::max_value();
        let mut max = T::min_value();
        let mut count = 0;
        for value in iter {
            if value.is_nan() {
                continue;
            }
            sum += value;
            sum_squared += value.powi(2);
            if value < min {
                min = value;
            }
            if value > max {
                max = value;
            }
            count += 1;
        }
        if count == 0 {
            return None;
        }
        let count_float =
            T::from_usize(count).unwrap_or_else(|| panic!("Cannot convert {count:?} to TTFNum"));
        let mean = sum / count_float;
        let var = sum_squared / count_float - mean.powi(2);
        let std = if var > T::zero() {
            var.sqrt()
        } else {
            // All values are equal but, because of roundings, var might be negative.
            T::zero()
        };
        Some(Distribution {
            mean,
            std,
            min,
            max,
        })
    }

    /// Returns the mean of the distribution.
    pub const fn mean(&self) -> T {
        self.mean
    }

    /// Returns the standard-deviation of the distribution.
    pub const fn std(&self) -> T {
        self.std
    }

    /// Returns the minimum of the distribution.
    pub const fn min(&self) -> T {
        self.min
    }

    /// Returns the maximum of the distribution.
    pub const fn max(&self) -> T {
        self.max
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distribution_test() {
        let values = vec![1., 2., 3., 4., 5.];
        let d = Distribution::from_iterator(values.into_iter()).unwrap();
        let expected = Distribution {
            mean: 3.,
            std: 2.0f64.sqrt(),
            min: 1.,
            max: 5.,
        };
        assert_eq!(d, expected);
    }
}
