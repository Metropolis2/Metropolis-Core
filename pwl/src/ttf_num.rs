// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::fmt;
use std::ops::Neg;

use num_traits::{ConstOne, ConstZero, FromPrimitive, NumAssignOps, NumOps, Pow};

/// Trait for numbers that support a wide variety of operations.
pub trait TTFNum:
    Copy
    + Default
    + PartialOrd
    + Send
    + Sync
    + fmt::Debug
    + Neg<Output = Self>
    + FromPrimitive
    + ConstOne
    + ConstZero
    + NumOps
    + NumAssignOps
    + Pow<i32, Output = Self>
{
    /// A margin number that can be used to consider that two values are close to each other.
    const MARGIN: Self;
    /// The infinity value.
    const INFINITY: Self;
    /// Returns `true` if the number is not valid.
    fn is_nan(&self) -> bool;
    /// Returns `true` if the number is finite.
    fn is_finite(&self) -> bool;
    /// Converts to a `usize`, truncating towards zero if required.
    fn trunc_to_usize(self) -> usize;
    /// Returns the minimum of self and other.
    fn min(self, other: Self) -> Self;
    /// Returns the maximum of self and other.
    fn max(self, other: Self) -> Self;
}

impl TTFNum for f32 {
    const MARGIN: f32 = 0.01;
    const INFINITY: f32 = f32::INFINITY;
    fn is_nan(&self) -> bool {
        f32::is_nan(*self)
    }
    fn is_finite(&self) -> bool {
        f32::is_finite(*self)
    }
    fn trunc_to_usize(self) -> usize {
        self as usize
    }
    fn min(self, other: Self) -> Self {
        self.min(other)
    }
    fn max(self, other: Self) -> Self {
        self.max(other)
    }
}

impl TTFNum for f64 {
    const MARGIN: f64 = 0.01;
    const INFINITY: f64 = f64::INFINITY;
    fn is_nan(&self) -> bool {
        f64::is_nan(*self)
    }
    fn is_finite(&self) -> bool {
        f64::is_finite(*self)
    }
    fn trunc_to_usize(self) -> usize {
        self as usize
    }
    fn min(self, other: Self) -> Self {
        self.min(other)
    }
    fn max(self, other: Self) -> Self {
        self.max(other)
    }
}
