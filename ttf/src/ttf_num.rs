// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use num_traits::{Float, FromPrimitive};
use serde::de::DeserializeOwned;
use serde::Serialize;
use std::fmt;

const MARGIN32: f32 = 1e-4;
const MARGIN64: f64 = 1e-4;

/// Trait for numbers that support a wide variety of operations.
pub trait TTFNum:
    Float
    + FromPrimitive
    + Default
    + PartialOrd
    + Send
    + Sync
    + fmt::Debug
    + fmt::Display
    + Serialize
    + DeserializeOwned
{
    /// Returns a small number representing a small error margin.
    fn small_margin() -> Self;
    /// Returns a small number representing a large error margin.
    fn large_margin() -> Self;
    /// Returns the average between two numbers.
    #[must_use]
    fn average(&self, other: &Self) -> Self;
    /// Returns `true` if the two numbers are equal (allowing for a small approximation error).
    fn approx_eq(&self, other: &Self) -> bool;
    /// Returns `true` if the two number are not equal.
    fn approx_ne(&self, other: &Self) -> bool {
        !self.approx_eq(other)
    }
    /// Returns `true` if the first number is smaller than or equal to the second number (allowing
    /// for a small approximation error).
    fn approx_le(&self, other: &Self) -> bool;
    /// Returns `true` if the first number is smaller than the second number (allowing for a small
    /// approximation error).
    fn approx_lt(&self, other: &Self) -> bool;
    /// Returns `true` if the first number is greater than or equal to the second number (allowing
    /// for a small approximation error).
    fn approx_ge(&self, other: &Self) -> bool {
        // self >= other - margin  -->  other <= self + margin
        other.approx_le(self)
    }
    /// Returns `true` if the first number is greater than the second number (allowing for a small
    /// approximation error).
    fn approx_gt(&self, other: &Self) -> bool {
        other.approx_lt(self)
    }
}

impl TTFNum for f32 {
    fn small_margin() -> Self {
        MARGIN32
    }
    fn large_margin() -> Self {
        100. * MARGIN32
    }
    fn approx_eq(&self, other: &Self) -> bool {
        (self - other).abs() < MARGIN32
    }
    fn approx_le(&self, other: &Self) -> bool {
        *self <= *other + MARGIN32
    }
    fn approx_lt(&self, other: &Self) -> bool {
        *self + MARGIN32 < *other
    }
    fn average(&self, other: &Self) -> Self {
        (self + other) / 2.0
    }
}

impl TTFNum for f64 {
    fn small_margin() -> Self {
        MARGIN64
    }
    fn large_margin() -> Self {
        100. * MARGIN64
    }
    fn approx_eq(&self, other: &Self) -> bool {
        (self - other).abs() < MARGIN64
    }
    fn approx_le(&self, other: &Self) -> bool {
        *self <= *other + MARGIN64
    }
    fn approx_lt(&self, other: &Self) -> bool {
        *self + MARGIN64 < *other
    }
    fn average(&self, other: &Self) -> Self {
        (self + other) / 2.0
    }
}
