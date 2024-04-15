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
use std::ops::*;

use anyhow::{bail, Result};
use num_traits::{ConstOne, ConstZero, FromPrimitive, One, Pow, ToPrimitive, Zero};
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

const MARGIN: f64 = 1e-8;

pub(crate) trait MetroPositiveNum:
    Sized
    + Copy
    + Ord
    + TryFrom<f64>
    + TryFrom<usize>
    + Into<f64>
    + Add<Output = Self>
    + AddAssign
    + Mul<Output = Self>
    + MulAssign
    + Mul<usize, Output = Self>
    + Div<usize, Output = Self>
    + DivAssign<usize>
    + One
    + ConstOne
{
    const NAN: Self;
    fn is_nan(self) -> bool;
    /// Returns `self` divided by two.
    fn half(self) -> Self;
    fn powi(self, expo: i32) -> Self;
    fn powf(self, expo: f64) -> Self;
    fn sqrt(self) -> Self {
        self.powf(0.5)
    }
    fn from_usize_unchecked(value: usize) -> Self;
    fn to_usize_unchecked(self) -> usize;
}

pub(crate) trait MetroNonNegativeNum:
    MetroPositiveNum + Zero + ConstZero + iter::Sum
{
    fn is_positive(self) -> bool;
    /// Subtract `other` from `self` when `self` is larger than `other`.
    fn sub_unchecked(self, other: Self) -> Self;
    fn max_value() -> Self;
    fn min_value() -> Self;
}

pub(crate) trait MetroAnyNum:
    MetroNonNegativeNum + Sub<Output = Self> + SubAssign + Neg<Output = Self> + TTFNum
{
    fn is_negative(self) -> bool;
    // TODO: Return the NonNegative variant of the type instead (defined as a trait type)
    fn abs(self) -> Self;
}

/// Implements some useful traits and functions for unit types that can hold positive values.
macro_rules! impl_traits_on_positive_unit(
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

            impl Mul<usize> for $t {
                type Output = Self;
                fn mul(self, rhs: usize) -> Self::Output {
                    Self(self.0 * rhs as f64)
                }
            }

            impl Div<usize> for $t {
                type Output = Self;
                fn div(self, rhs: usize) -> Self::Output {
                    Self(self.0 / rhs as f64)
                }
            }

            impl DivAssign<usize> for $t {
                fn div_assign(&mut self, rhs: usize)  {
                    self.0 /= rhs as f64;
                }
            }

            impl One for $t {
                fn one() -> Self {
                    Self(1.0)
                }
                fn is_one(&self) -> bool {
                    self.0 == 1.0
                }
            }

            impl ConstOne for $t {
                const ONE: Self = Self(1.0);
            }

            impl Eq for $t {
            }

            #[allow(clippy::derive_ord_xor_partial_ord)]
            impl Ord for $t {
                fn cmp(&self, other: &Self) -> Ordering {
                    self.partial_cmp(other).unwrap()
                }
            }

            impl TryFrom<f64> for $t {
                type Error = anyhow::Error;
                fn try_from(value: f64) -> Result<Self> {
                    if value < $t::lower_bound().0 || value > $t::upper_bound().0 {
                        bail!("Invalid value: {value}")
                    }
                    Ok(Self(value))
                }
            }

            impl TryFrom<usize> for $t {
                type Error = anyhow::Error;
                fn try_from(value: usize) -> Result<Self> {
                    let value_as_float = value as f64;
                    if value_as_float < $t::lower_bound().0 || value_as_float > $t::upper_bound().0 {
                        bail!("Invalid value: {value}")
                    }
                    Ok(Self(value_as_float))
                }
            }

            impl From<$t> for f64 {
                fn from(value: $t) -> f64 {
                    value.0
                }
            }

            impl From<&$t> for f64 {
                fn from(value: &$t) -> f64 {
                    value.0
                }
            }

            impl TryFrom<$t> for usize {
                type Error = anyhow::Error;
                fn try_from(value: $t) -> Result<Self> {
                    if let Some(u) = value.0.to_usize() {
                        Ok(u)
                    } else {
                        bail!("Cannot convert {} to usize", value.0)
                    }
                }
            }

            impl MetroPositiveNum for $t {
                const NAN: $t = Self(f64::NAN);
                fn is_nan(self) -> bool {
                    self.0.is_nan()
                }
                fn half(self) -> Self {
                    Self(self.0 / 2.0)
                }
                fn powi(self, expo: i32) -> Self {
                    Self(self.0.powi(expo))
                }
                fn powf(self, expo: f64) -> Self {
                    Self(self.0.powf(expo))
                }
                fn sqrt(self) -> Self {
                    Self(self.0.sqrt())
                }
                fn from_usize_unchecked(value: usize) -> Self {
                    Self::new_unchecked(value as f64)
                }
                fn to_usize_unchecked(self) -> usize {
                    self.0 as usize
                }
            }
        )*
    };
);

/// Implements some useful traits on units that can take the value zero.
macro_rules! impl_traits_on_non_negative_unit(
    ( $( $t:ident ),* ) => {
        $(
            impl iter::Sum for $t {
                fn sum<I>(iter: I) -> Self
                    where I: Iterator<Item = $t>
                {
                    iter.fold($t::ZERO, |a, b| a + b)
                }
            }

            impl Zero for $t {
                fn zero() -> Self {
                    Self(0.0)
                }
                fn is_zero(&self) -> bool {
                    self.0 == 0.0
                }
            }

            impl ConstZero for $t {
                const ZERO: Self = Self(0.0);
            }

            impl MetroNonNegativeNum for $t {
                fn is_positive(self) -> bool {
                    self > Self::ZERO
                }
                fn sub_unchecked(self, other: Self) -> Self {
                    debug_assert!(self.0 + MARGIN >= other.0);
                    Self((self.0 - other.0).max(0.0))
                }
                fn max_value() -> Self {
                    Self::upper_bound()
                }
                fn min_value() -> Self {
                    Self::lower_bound()
                }
            }
        )*
    };
);

/// Implements some useful traits on units that can take any value.
macro_rules! impl_traits_on_any_unit(
    ( $( $t:ident ),* ) => {
        $(
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

            impl Neg for $t {
                type Output = Self;
                fn neg(self) -> Self::Output {
                    Self(self.0.neg())
                }
            }

            impl MetroAnyNum for $t {
                fn is_negative(self) -> bool {
                    self < Self::ZERO
                }
                fn abs(self) -> Self {
                    Self(self.0.abs())
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

            impl Pow<i32> for $t {
                type Output = Self;
                fn pow(self, rhs: i32) -> Self::Output {
                    self.powi(rhs)
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

            impl TTFNum for $t {
                const MARGIN: Self = Self(f64::MARGIN);
                const INFINITY: Self = Self(f64::INFINITY);
                fn is_nan(&self) -> bool {
                    self.0.is_nan()
                }
                fn is_finite(&self) -> bool {
                    self.0.is_finite()
                }
                fn trunc_to_usize(self) -> usize {
                    self.0 as usize
                }
                fn min(self, other: Self) -> Self {
                    Self(self.0.min(other.0))
                }
                fn max(self, other: Self) -> Self {
                    Self(self.0.max(other.0))
                }
            }
        )*
    };
);

/// Representation of a value with no particular constraint.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Serialize)]
pub struct AnyNum(f64);

impl AnyNum {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    // pub(crate) fn assume_non_negative_unchecked(self) -> NonNegativeNum {
    // debug_assert!(self.0 >= 0.0);
    // NonNegativeNum(self.0)
    // }

    pub(crate) fn assume_positive_unchecked(self) -> PositiveNum {
        debug_assert!(self.0 > 0.0);
        PositiveNum(self.0)
    }

    pub(crate) fn assume_zero_one_unchecked(self) -> ZeroOneNum {
        debug_assert!((0.0..=1.0).contains(&self.0));
        ZeroOneNum(self.0)
    }
}

impl From<NonNegativeNum> for AnyNum {
    fn from(value: NonNegativeNum) -> Self {
        Self(value.0)
    }
}

impl From<PositiveNum> for AnyNum {
    fn from(value: PositiveNum) -> Self {
        Self(value.0)
    }
}

/// Representation of a non-negative number.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Serialize)]
pub struct NonNegativeNum(f64);

impl NonNegativeNum {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value >= 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(0.0)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    pub(crate) fn assume_positive_unchecked(self) -> PositiveNum {
        debug_assert!(self.0 > 0.0);
        PositiveNum(self.0)
    }

    // pub(crate) fn assume_zero_one_unchecked(self) -> ZeroOneNum {
    // debug_assert!((0.0..=1.0).contains(&self.0));
    // ZeroOneNum(self.0)
    // }
}

impl From<ZeroOneNum> for NonNegativeNum {
    fn from(value: ZeroOneNum) -> Self {
        debug_assert!(value.0 >= 0.0);
        Self(value.0)
    }
}

impl From<PositiveNum> for NonNegativeNum {
    fn from(value: PositiveNum) -> Self {
        debug_assert!(value.0 >= 0.0);
        Self(value.0)
    }
}

impl TryFrom<AnyNum> for NonNegativeNum {
    type Error = anyhow::Error;
    fn try_from(value: AnyNum) -> Result<Self> {
        if value < AnyNum::ZERO {
            bail!("Cannot convert {value:?} to a NonNegativeNum");
        } else {
            Ok(Self(value.0))
        }
    }
}

/// Representation of a positive number.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Serialize)]
pub struct PositiveNum(f64);

impl PositiveNum {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value > 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN_POSITIVE)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    pub(crate) fn assume_zero_one_unchecked(self) -> ZeroOneNum {
        debug_assert!((0.0..=1.0).contains(&self.0));
        ZeroOneNum(self.0)
    }
}

impl TryFrom<NonNegativeNum> for PositiveNum {
    type Error = anyhow::Error;
    fn try_from(value: NonNegativeNum) -> Result<Self> {
        if value.0 == 0.0 {
            bail!("Cannot convert 0 to a PositiveNum");
        } else {
            Ok(Self::new_unchecked(value.0))
        }
    }
}

impl TryFrom<ZeroOneNum> for PositiveNum {
    type Error = anyhow::Error;
    fn try_from(value: ZeroOneNum) -> Result<Self> {
        if value.0 == 0.0 {
            bail!("Cannot convert 0 to a PositiveNum");
        } else {
            Ok(Self::new_unchecked(value.0))
        }
    }
}

impl TryFrom<AnyNum> for PositiveNum {
    type Error = anyhow::Error;
    fn try_from(value: AnyNum) -> Result<Self> {
        if value <= AnyNum::ZERO {
            bail!("Cannot convert {value:?} to a PositiveNum");
        } else {
            Ok(Self(value.0))
        }
    }
}

/// Representation of a number between 0.0 (inclusive) and 1.0 (inclusive).
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct ZeroOneNum(f64);

impl ZeroOneNum {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!((0.0..=1.0).contains(&value));
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(0.0)
    }

    const fn upper_bound() -> Self {
        Self(1.0)
    }

    /// Returns `1 - self`.
    pub(crate) fn one_minus(&self) -> Self {
        Self(1.0 - self.0)
    }
}

impl TryFrom<AnyNum> for ZeroOneNum {
    type Error = anyhow::Error;
    fn try_from(value: AnyNum) -> Result<Self> {
        value.0.try_into()
    }
}

impl TryFrom<NonNegativeNum> for ZeroOneNum {
    type Error = anyhow::Error;
    fn try_from(value: NonNegativeNum) -> Result<Self> {
        if value > NonNegativeNum::ONE {
            bail!("Cannot convert {value:?} to a ZeroOneNum");
        } else {
            Ok(Self(value.0))
        }
    }
}

impl TryFrom<PositiveNum> for ZeroOneNum {
    type Error = anyhow::Error;
    fn try_from(value: PositiveNum) -> Result<Self> {
        if value > PositiveNum::ONE {
            bail!("Cannot convert {value:?} to a ZeroOneNum");
        } else {
            Ok(Self(value.0))
        }
    }
}

/// Representation of a non-negative time duration or timestamp, expressed in seconds.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct NonNegativeSeconds(f64);

impl NonNegativeSeconds {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value >= 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(0.0)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    pub(crate) fn assume_positive_unchecked(self) -> PositiveSeconds {
        debug_assert!(self.0 > 0.0);
        PositiveSeconds(self.0)
    }
}

impl fmt::Display for NonNegativeSeconds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let seconds = self.0.round() as u64;
        let hour = seconds / 3600;
        let minute = seconds % 3600 / 60;
        let second = seconds % 60;
        write!(f, "{hour:02}:{minute:02}:{second:02}")
    }
}

impl From<PositiveSeconds> for NonNegativeSeconds {
    fn from(value: PositiveSeconds) -> Self {
        debug_assert!(value.0 >= 0.0);
        Self(value.0)
    }
}

impl TryFrom<AnySeconds> for NonNegativeSeconds {
    type Error = anyhow::Error;
    fn try_from(value: AnySeconds) -> Result<Self> {
        if value.0 < 0.0 {
            bail!("Cannot convert {value:?} to a NonNegativeSeconds");
        } else {
            Ok(Self(value.0))
        }
    }
}

/// Representation of a duration or timestamp, expressed in seconds.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct AnySeconds(f64);

impl AnySeconds {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    pub(crate) fn assume_non_negative_unchecked(self) -> NonNegativeSeconds {
        debug_assert!(
            self.0 + MARGIN >= 0.0,
            "Expected non-negative number, got: {}",
            self.0
        );
        NonNegativeSeconds(self.0.max(0.0))
    }

    pub(crate) fn assume_positive_unchecked(self) -> PositiveSeconds {
        debug_assert!(self.0 > 0.0);
        PositiveSeconds(self.0)
    }
}

impl fmt::Display for AnySeconds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let seconds = self.0.round() as u64;
        let hour = seconds / 3600;
        let minute = seconds % 3600 / 60;
        let second = seconds % 60;
        write!(f, "{hour:02}:{minute:02}:{second:02}")
    }
}

impl From<NonNegativeSeconds> for AnySeconds {
    fn from(value: NonNegativeSeconds) -> Self {
        debug_assert!(value.0.is_finite());
        Self(value.0)
    }
}

impl From<PositiveSeconds> for AnySeconds {
    fn from(value: PositiveSeconds) -> Self {
        debug_assert!(value.0.is_finite());
        Self(value.0)
    }
}

/// Representation of positive value expressed in seconds.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct PositiveSeconds(f64);

impl PositiveSeconds {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value > 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN_POSITIVE)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }
}

impl fmt::Display for PositiveSeconds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let seconds = self.0.round() as u64;
        let hour = seconds / 3600;
        let minute = seconds % 3600 / 60;
        let second = seconds % 60;
        write!(f, "{hour:02}:{minute:02}:{second:02}")
    }
}

/// Representation of a utility (or monetary) amount.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct Utility(f64);

impl Utility {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }
}

/// Representation of a value expressed in utility amount per second.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct ValueOfTime(f64);

impl ValueOfTime {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }
}

/// Representation of non-negative value expressed in meters.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct NonNegativeMeters(f64);

impl NonNegativeMeters {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value >= 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(0.0)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    pub(crate) fn assume_positive_unchecked(self) -> PositiveMeters {
        debug_assert!(self.0 > 0.0);
        PositiveMeters(self.0)
    }
}

impl From<PositiveMeters> for NonNegativeMeters {
    fn from(value: PositiveMeters) -> Self {
        Self(value.0)
    }
}

impl TryFrom<AnyMeters> for NonNegativeMeters {
    type Error = anyhow::Error;
    fn try_from(value: AnyMeters) -> Result<Self> {
        if value.0 < 0.0 {
            bail!("Cannot convert {} to a non-negative number", value.0);
        }
        Ok(Self(value.0))
    }
}

/// Representation of positive value expressed in meters.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct PositiveMeters(f64);

impl PositiveMeters {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value > 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN_POSITIVE)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }
}

impl TryFrom<NonNegativeMeters> for PositiveMeters {
    type Error = anyhow::Error;
    fn try_from(value: NonNegativeMeters) -> Result<Self> {
        if value.0 == 0.0 {
            bail!("Cannot convert 0.0 to a positive number");
        }
        debug_assert!(value.0 > 0.0);
        Ok(Self(value.0))
    }
}

/// Representation of a value expressed in meters.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct AnyMeters(f64);

impl AnyMeters {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    pub(crate) fn assume_non_negative_unchecked(self) -> NonNegativeMeters {
        debug_assert!(
            self.0 + MARGIN >= 0.0,
            "Expected non-negative number, got: {}",
            self.0
        );
        NonNegativeMeters(self.0.max(0.0))
    }
}

impl From<NonNegativeMeters> for AnyMeters {
    fn from(value: NonNegativeMeters) -> Self {
        Self(value.0)
    }
}

impl From<PositiveMeters> for AnyMeters {
    fn from(value: PositiveMeters) -> Self {
        Self(value.0)
    }
}

/// Representation of a positive value expressed in meters per second.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
#[serde(try_from = "f64")]
pub struct MetersPerSecond(f64);

impl MetersPerSecond {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value > 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN_POSITIVE)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }

    pub(crate) fn to_num(self) -> PositiveNum {
        PositiveNum::new_unchecked(self.0)
    }
}

/// Representation of a positive value representing lane number.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct Lanes(f64);

impl Lanes {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value > 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN_POSITIVE)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }
}

/// Representation of a non-negative value representing Passenger car equivalent.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct PCE(f64);

impl PCE {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value >= 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(0.0)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }
}

/// Representation of a positive value expressed in PCE per second.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Default, Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct Flow(f64);

impl Flow {
    pub(crate) fn new_unchecked(value: f64) -> Self {
        debug_assert!(value.is_finite());
        debug_assert!(value > 0.0);
        Self(value)
    }

    const fn lower_bound() -> Self {
        Self(f64::MIN_POSITIVE)
    }

    const fn upper_bound() -> Self {
        Self(f64::MAX)
    }
}

impl_traits_on_positive_unit!(
    AnySeconds,
    NonNegativeSeconds,
    PositiveSeconds,
    Utility,
    ValueOfTime,
    Lanes,
    NonNegativeMeters,
    PositiveMeters,
    AnyMeters,
    MetersPerSecond,
    PCE,
    Flow,
    AnyNum,
    PositiveNum,
    NonNegativeNum,
    ZeroOneNum
);

impl_traits_on_non_negative_unit!(
    NonNegativeMeters,
    PCE,
    NonNegativeNum,
    ZeroOneNum,
    NonNegativeSeconds,
    AnySeconds,
    Utility,
    ValueOfTime,
    AnyMeters,
    AnyNum
);

impl_traits_on_any_unit!(AnySeconds, Utility, ValueOfTime, AnyMeters, AnyNum);

macro_rules! impl_from_into_any_num(
    ( $( $t:ident ),* ) => {
        $(
            impl From<AnyNum> for $t {
                fn from(value: AnyNum) -> Self {
                    debug_assert!(value.0.is_finite());
                    Self(value.0)
                }
            }
            impl From<$t> for AnyNum {
                fn from(value: $t) -> Self {
                    debug_assert!(value.0.is_finite());
                    Self(value.0)
                }
            }
        )*
    };
);

impl_from_into_any_num!(AnySeconds, AnyMeters, Utility);

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
    ( $l_type:ident + $r_type:ident = $o_type:ident ) => {
        impl Add<$r_type> for $l_type {
            type Output = $o_type;
            fn add(self, other: $r_type) -> Self::Output {
                $o_type(self.0 + other.0)
            }
        }
        impl Add<$l_type> for $r_type {
            type Output = $o_type;
            fn add(self, other: $l_type) -> Self::Output {
                $o_type(self.0 + other.0)
            }
        }
    };
    ( $l_type:ident += $r_type:ident ) => {
        impl AddAssign<$r_type> for $l_type {
            fn add_assign(&mut self, other: $r_type) {
                self.0 += other.0;
            }
        }
    };
    ( $l_type:ident - $r_type:ident = $o_type:ident ) => {
        impl Sub<$r_type> for $l_type {
            type Output = $o_type;
            fn sub(self, other: $r_type) -> Self::Output {
                $o_type(self.0 - other.0)
            }
        }
    };
    ( $l_type:ident ^ $r_type:ident = $o_type:ident ) => {
        impl Pow<$r_type> for $l_type {
            type Output = $o_type;
            fn pow(self, other: $r_type) -> Self::Output {
                $o_type(self.0.powf(other.0))
            }
        }
    };
);

impl_ops!(ValueOfTime * NonNegativeSeconds = Utility);
impl_ops!(ValueOfTime * PositiveSeconds = Utility);
impl_ops!(MetersPerSecond * NonNegativeSeconds = NonNegativeMeters);
impl_ops!(NonNegativeMeters * Lanes = NonNegativeMeters);
impl_ops!(Flow * Lanes = Flow);
impl_ops!(Flow * NonNegativeSeconds = PCE);
impl_ops!(MetersPerSecond * PositiveSeconds = PositiveMeters);
impl_ops!(PositiveNum * MetersPerSecond = MetersPerSecond);
impl_ops!(AnySeconds * ZeroOneNum = AnySeconds);
impl_ops!(NonNegativeSeconds * ZeroOneNum = NonNegativeSeconds);
impl_ops!(NonNegativeMeters * ZeroOneNum = NonNegativeMeters);
impl_ops!(MetersPerSecond * ZeroOneNum = MetersPerSecond);

impl_ops!(NonNegativeMeters / MetersPerSecond = NonNegativeSeconds);
impl_ops!(NonNegativeMeters / NonNegativeSeconds = MetersPerSecond);
impl_ops!(PCE / Flow = NonNegativeSeconds);
impl_ops!(PCE / NonNegativeSeconds = Flow);
impl_ops!(NonNegativeSeconds / PositiveNum = NonNegativeSeconds);
impl_ops!(NonNegativeMeters / PositiveMeters = NonNegativeNum);
impl_ops!(NonNegativeMeters / PositiveNum = NonNegativeMeters);
impl_ops!(PositiveMeters / MetersPerSecond = PositiveSeconds);
impl_ops!(PositiveMeters / PositiveMeters = PositiveNum);
impl_ops!(PositiveSeconds / PositiveSeconds = PositiveNum);
impl_ops!(PositiveNum / PositiveNum = PositiveNum);
impl_ops!(NonNegativeNum / PositiveNum = NonNegativeNum);
impl_ops!(NonNegativeSeconds / PositiveSeconds = NonNegativeNum);
impl_ops!(AnySeconds / PositiveSeconds = AnyNum);
impl_ops!(ZeroOneNum / PositiveNum = ZeroOneNum);

impl_ops!(NonNegativeSeconds + PositiveSeconds = PositiveSeconds);
impl_ops!(NonNegativeSeconds += PositiveSeconds);
impl_ops!(NonNegativeNum + ZeroOneNum = NonNegativeNum);
impl_ops!(NonNegativeNum += ZeroOneNum);

impl_ops!(NonNegativeNum - NonNegativeNum = AnyNum);
impl_ops!(PositiveNum - PositiveNum = AnyNum);
impl_ops!(NonNegativeSeconds - NonNegativeSeconds = AnySeconds);
impl_ops!(AnySeconds - NonNegativeSeconds = AnySeconds);
impl_ops!(NonNegativeMeters - NonNegativeMeters = AnyMeters);

impl_ops!(PositiveNum ^ PositiveNum = PositiveNum);

/// A time interval.
#[derive(Default, Clone, Copy, Debug, PartialEq, Deserialize, Serialize)]
pub struct Interval([NonNegativeSeconds; 2]);

impl TryFrom<[f64; 2]> for Interval {
    type Error = anyhow::Error;
    fn try_from(value: [f64; 2]) -> Result<Self> {
        let start = NonNegativeSeconds::try_from(value[0])?;
        let end = NonNegativeSeconds::try_from(value[1])?;
        if start >= end {
            bail!(
                "Intervals cannot have non-positive length: [{}, {}]",
                value[0],
                value[1]
            );
        }
        Ok(Interval([start, end]))
    }
}

impl Interval {
    pub(crate) fn new(start: NonNegativeSeconds, end: NonNegativeSeconds) -> Self {
        debug_assert!(end > start);
        Self([start, end])
    }

    pub(crate) fn new_unchecked(start_value: f64, end_value: f64) -> Self {
        debug_assert!(end_value > start_value);
        let start = NonNegativeSeconds::new_unchecked(start_value);
        let end = NonNegativeSeconds::new_unchecked(end_value);
        Self([start, end])
    }

    /// Returns the start of the interval.
    pub const fn start(&self) -> NonNegativeSeconds {
        self.0[0]
    }

    /// Returns the end of the interval.
    pub const fn end(&self) -> NonNegativeSeconds {
        self.0[1]
    }

    /// Returns the interval as a vector of two [Time] values.
    pub fn to_vec(&self) -> Vec<NonNegativeSeconds> {
        self.0.to_vec()
    }

    /// Returns `true` if `time` is included in the (closed) interval.
    pub fn contains(&self, time: NonNegativeSeconds) -> bool {
        self.start() <= time && self.end() >= time
    }

    /// Returns the length of the interval, i.e., the time that elapses between the start and the
    /// end of the interval.
    pub fn length(&self) -> PositiveSeconds {
        PositiveSeconds(self.0[1].0 - self.0[0].0)
    }
}

/// Struct to describe statistics on a distribution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Distribution<T> {
    mean: T,
    std: T,
    min: T,
    max: T,
}

impl<T> Distribution<T>
where
    T: MetroNonNegativeNum,
{
    /// Returns a `Distribution` from an iterator of elements of the distribution.
    ///
    /// Returns `None` if the iterator is empty.
    pub(crate) fn from_iterator(iter: impl Iterator<Item = T>) -> Option<Distribution<T>> {
        let mut sum = T::ZERO;
        let mut sum_squared = T::ZERO;
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
        let mean = sum / count;
        let var = (sum_squared / count).sub_unchecked(mean.powi(2));
        let std = if var > T::ZERO {
            var.sqrt()
        } else {
            // All values are equal but, because of roundings, var might be negative.
            T::ZERO
        };
        Some(Distribution {
            mean,
            std,
            min,
            max,
        })
    }

    /// Returns the mean of the distribution.
    pub(crate) const fn mean(&self) -> T {
        self.mean
    }

    /// Returns the standard-deviation of the distribution.
    pub(crate) const fn std(&self) -> T {
        self.std
    }

    /// Returns the minimum of the distribution.
    pub(crate) const fn min(&self) -> T {
        self.min
    }

    /// Returns the maximum of the distribution.
    pub(crate) const fn max(&self) -> T {
        self.max
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distribution_test() {
        let values = vec![AnyNum(1.), AnyNum(2.), AnyNum(3.), AnyNum(4.), AnyNum(5.)];
        let d = Distribution::from_iterator(values.into_iter()).unwrap();
        let expected = Distribution {
            mean: AnyNum(3.),
            std: AnyNum(2.0f64.sqrt()),
            min: AnyNum(1.),
            max: AnyNum(5.),
        };
        assert_eq!(d, expected);
    }
}
