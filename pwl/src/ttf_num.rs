// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::fmt;

use num_traits::{Float, FromPrimitive, NumAssignOps};
use serde::de::DeserializeOwned;
use serde::Serialize;

/// Trait for numbers that support a wide variety of operations.
pub trait TTFNum:
    Float
    + NumAssignOps
    + FromPrimitive
    + Default
    + PartialOrd
    + Send
    + Sync
    + fmt::Debug
    + fmt::Display
    + Serialize
    + DeserializeOwned
    + 'static
{
    /// Returns true if the two number of approximately equal.
    fn approx_eq(&self, other: &Self) -> bool;
    /// Returns a margin number that can be used to consider that two values are close to each
    /// other.
    fn margin() -> Self;
    /// Returns the average between two numbers.
    #[must_use]
    fn average(self, other: Self) -> Self;
}

impl TTFNum for f32 {
    fn approx_eq(&self, other: &Self) -> bool {
        (self - other) < 1e-4
    }
    fn margin() -> Self {
        0.01
    }
    fn average(self, other: Self) -> Self {
        (self + other) / 2.0
    }
}

impl TTFNum for f64 {
    fn approx_eq(&self, other: &Self) -> bool {
        (self - other) < 1e-4
    }
    fn margin() -> Self {
        0.01
    }
    fn average(self, other: Self) -> Self {
        (self + other) / 2.0
    }
}
