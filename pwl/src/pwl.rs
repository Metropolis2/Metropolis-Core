// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::cmp::Ordering;
use std::fmt;

use anyhow::anyhow;
use either::Either;
use itertools::Itertools;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::ttf_num::TTFNum;
use crate::UndercutDescriptor;

#[derive(Clone, Default, Debug)]
struct MinMax<Y> {
    min: Option<Y>,
    max: Option<Y>,
}

impl<Y> MinMax<Y> {
    fn new() -> Self {
        Self {
            min: None,
            max: None,
        }
    }

    fn into_min_max(self) -> (Y, Y) {
        debug_assert!(self.min.is_some());
        debug_assert!(self.max.is_some());
        (self.min.unwrap(), self.max.unwrap())
    }
}

impl<Y: PartialOrd + Copy> MinMax<Y> {
    fn update(&mut self, y: Y) {
        if self.min.is_none() {
            debug_assert!(self.max.is_none());
            self.min = Some(y);
            self.max = Some(y);
        }
        if y < self.min.unwrap() {
            self.min = Some(y);
        } else if y > self.max.unwrap() {
            self.max = Some(y);
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct DeserPwlXYF<X, Y> {
    points: Vec<Option<Y>>,
    start_x: X,
    interval_x: X,
}

impl<X: TTFNum + DeserializeOwned, Y: TTFNum + DeserializeOwned, T> TryFrom<DeserPwlXYF<X, Y>>
    for PwlXYF<X, Y, T>
{
    type Error = anyhow::Error;
    fn try_from(value: DeserPwlXYF<X, Y>) -> Result<Self, Self::Error> {
        if value.start_x < X::ZERO {
            return Err(anyhow!(
                "`start_x` value must be non-negative, got {:?}",
                value.start_x
            ));
        }
        if value.interval_x < X::ZERO {
            return Err(anyhow!(
                "`interval_x` value must be non-negative, got {:?}",
                value.interval_x
            ));
        }
        // Deserialize `None` as infinity.
        let points: Vec<_> = value
            .points
            .into_iter()
            .map(|opt_y| opt_y.unwrap_or(Y::INFINITY))
            .collect();
        let (&min, &max) = points.iter().minmax().into_option().unwrap();
        let pwl_xyf = PwlXYF {
            points,
            min,
            max,
            start_x: value.start_x,
            interval_x: value.interval_x,
            convert_type: std::marker::PhantomData,
        };
        Ok(pwl_xyf)
    }
}

/// A piecewise-linear function represented by a Vec of points `y`.
///
/// The `x` points are evenly spaced, starting at `start_x`, with interval given by `interval_x`.
///
/// The `x` values are of type `X`, the `y` values are of type `Y`.
/// The `T` generic type is used to convert from `X` to `Y`.
#[derive(PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(serialize = "X: Serialize, Y: Serialize"))]
#[serde(bound(deserialize = "X: TTFNum + DeserializeOwned, Y: TTFNum + DeserializeOwned"))]
#[serde(try_from = "DeserPwlXYF<X, Y>")]
pub struct PwlXYF<X, Y, T> {
    /// `y` values of the function.
    points: Vec<Y>,
    /// Minimum `y` value of the function.
    #[serde(skip)]
    min: Y,
    /// Maximum `y` value of the function.
    #[serde(skip)]
    max: Y,
    /// Starting `x` value.
    start_x: X,
    /// Interval between two `x` values.
    interval_x: X,
    #[serde(skip)]
    convert_type: std::marker::PhantomData<T>,
}

/// A piecewise-linear function where the `x` and `y` values have the same type, `T`.
pub type PwlTTF<T> = PwlXYF<T, T, T>;

// Implement Debug manually so that we do not care if `T` and `S` implement Debug themself.
impl<X: fmt::Debug, Y: fmt::Debug, T> fmt::Debug for PwlXYF<X, Y, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PwlXYF")
            .field("points", &self.points)
            .field("min", &self.min)
            .field("max", &self.max)
            .field("start_x", &self.start_x)
            .field("interval_x", &self.interval_x)
            .finish()
    }
}

// Implement Clone manually so that we do not care if `T` and `S` implement Clone themself.
impl<X: Clone, Y: Clone, T> Clone for PwlXYF<X, Y, T> {
    fn clone(&self) -> Self {
        Self {
            points: self.points.clone(),
            min: self.min.clone(),
            max: self.max.clone(),
            start_x: self.start_x.clone(),
            interval_x: self.interval_x.clone(),
            convert_type: std::marker::PhantomData,
        }
    }
}

impl<X, Y, T> PwlXYF<X, Y, T> {
    /// Consumes the [PwlXYF] and returns a vector of `y` values.
    pub fn into_points(self) -> Vec<Y> {
        self.points
    }
}

impl<X, Y, T> PwlXYF<X, Y, T>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    /// Iterates over the `(x, y)` values of the function.
    pub fn iter(&'_ self) -> impl Iterator<Item = (X, Y)> + '_ {
        let x_iter = std::iter::successors(Some(self.start_x), |x| Some(*x + self.interval_x));
        x_iter.zip(self.points.iter().copied())
    }

    /// Iterates over the `x` values of the function.
    pub fn iter_x(&'_ self) -> impl Iterator<Item = X> + '_ {
        let x_iter = std::iter::successors(Some(self.start_x), |x| Some(*x + self.interval_x));
        x_iter.take(self.points.len())
    }

    /// Iterates over the `y` values of the function.
    pub fn iter_y(&'_ self) -> impl Iterator<Item = Y> + '_ {
        self.points.iter().copied()
    }

    /// Iterates over values `((x_i, y_i), (x_i+1, y_i+1))`.
    pub fn double_iter(&'_ self) -> impl Iterator<Item = ((X, Y), (X, Y))> + '_ {
        self.iter().zip(self.iter().skip(1))
    }

    /// Returns `true` if the function is empty (there is no breakpoint).
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// Returns the number of breakpoints of the function.
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Returns the `x` value at the given index.
    pub fn x_at_index(&self, index: usize) -> X {
        self.start_x + self.interval_x * X::from_usize(index).unwrap()
    }

    /// Returns the `y` value at the given index.
    ///
    /// *Panics* if the index is out of bounds.
    pub fn y_at_index(&self, index: usize) -> Y {
        self.points[index]
    }

    /// Returns the period of the function (the minimum and maximum `x` values).
    pub fn period(&self) -> (X, X) {
        (self.start_x, self.x_at_index(self.points.len() - 1))
    }

    /// Returns the length of the period of the function.
    pub fn period_length(&self) -> X {
        X::from_usize(self.points.len() - 1).unwrap() * self.interval_x
    }

    /// Returns the middle `x` value.
    pub fn middle_x(&self) -> X {
        self.x_at_index(self.points.len() / 2)
    }

    /// Returns the minimum `y` value.
    pub fn min(&self) -> Y {
        debug_assert!(
            self.min
                == self
                    .iter_y()
                    .min_by(|a, b| a.partial_cmp(b).unwrap())
                    .unwrap()
        );
        self.min
    }

    /// Returns the maximum `y` value.
    pub fn max(&self) -> Y {
        debug_assert!(
            self.max
                == self
                    .iter_y()
                    .max_by(|a, b| a.partial_cmp(b).unwrap())
                    .unwrap()
        );
        self.max
    }

    /// Returns `true` if the function is constant.
    pub fn is_cst(&self) -> bool {
        self.min() == self.max()
    }

    /// Returns `true` if the function is practically constant, i.e., all values are contained
    /// within a given bound.
    pub fn is_practically_cst(&self, bound: Y) -> bool {
        (self.max() - self.min()) <= bound
    }

    /// Returns the last `y` value.
    fn last_y(&self) -> Y {
        self.points[self.points.len() - 1]
    }

    /// Evaluates the value of the function at the given `x` value.
    pub fn eval(&self, x: X) -> Y {
        debug_assert!(!self.is_empty());
        // `i` is the position of `x` in the vector of `y` values.
        // For example, if `i = 11.3`, it means that the `y` value we are looking for is 70% of the
        // 11th `y` value and 30% of the 12th `y` value.
        let i = (x - self.start_x) / self.interval_x;
        debug_assert!(i >= X::ZERO, "{:?} < {:?}", x, self.start_x);
        let index = i.trunc_to_usize();
        if index >= self.points.len() - 1 {
            // Last known `x` is `start_x + interval_x * (n - 1)`, where `n` is the number of
            // points.
            // If `i >= n - 1`, it means that `(x - start_x) / interval_x >= n - 1` and thus
            // `x >= start_x + interval_x * (n - 1)`.
            // When `x` is larger than the last `x` value, we return the last `y` value.
            return self.last_y();
        }
        // `index` is such that `x[index] <= x < x[index + 1]`.
        // At this point, we know that `0 <= index < n - 1`.
        // `share` is the coefficient of `y[index + 1]` in the linear interpolation and `1 - share`
        // is the coefficient of `y[index]`.
        let share = i % X::ONE;
        debug_assert!(share >= X::ZERO);
        debug_assert!(share < X::ONE);
        if share.is_zero() {
            // The `y` value for this exact `x` value is known.
            return self.points[index];
        }
        ((self.points[index]).into() * (X::ONE - share).into()
            + (self.points[index + 1]).into() * (share).into())
        .into()
    }

    /// Returns a new PwlXYF equal to the input PwlXYF plus a constant value.
    #[must_use]
    pub fn add(&self, c: Y) -> Self {
        self.map(|y| y + c)
    }

    /// Returns a new PwlXYF by applying a given function on the `y` values of the two input
    /// PwlXYFs.
    #[must_use]
    pub fn map<F, W>(&self, func: F) -> PwlXYF<X, W, T>
    where
        F: Fn(Y) -> W,
        W: TTFNum + Into<T> + From<T>,
    {
        debug_assert!(!self.is_empty());
        let points = self.points.iter().map(|&y| func(y)).collect();
        PwlXYF {
            points,
            min: func(self.min()),
            max: func(self.max()),
            start_x: self.start_x,
            interval_x: self.interval_x,
            convert_type: self.convert_type,
        }
    }

    /// Consumes the [PwlXYF] and returns a vector of `x` values and a vector of `y` values.
    pub fn into_xs_and_ys(self) -> (Vec<X>, Vec<Y>) {
        let xs = self.iter_x().collect();
        (xs, self.points)
    }
}

impl<X, Y, T> PwlXYF<X, Y, T>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    /// Creates a new PwlXYF from a Vec of `y` values.
    pub fn from_values(y: Vec<Y>, start_x: X, interval_x: X) -> Self {
        assert!(!y.is_empty(), "Cannot create a `PwlXYF` from empty values");
        debug_assert!(y.iter().all(|v| !v.is_nan()));
        let (&min, &max) = y.iter().minmax().into_option().unwrap();
        PwlXYF {
            points: y,
            min,
            max,
            start_x,
            interval_x,
            convert_type: std::marker::PhantomData,
        }
    }
}

impl<T, U> PwlXYF<T, T, U> {
    /// Convenient way to convert a `PwlXYF<T, T, U>` into a `PwlTTF<T>`.
    pub fn to_ttf(self) -> PwlTTF<T> {
        PwlTTF {
            points: self.points,
            min: self.min,
            max: self.max,
            start_x: self.start_x,
            interval_x: self.interval_x,
            convert_type: std::marker::PhantomData,
        }
    }
}

impl<T: TTFNum> PwlTTF<T> {
    fn is_fifo(&self) -> bool {
        for ((x0, y0), (x1, y1)) in self.double_iter() {
            if x0 + y0 > x1 + y1 {
                println!("{:?} + {:?} > {:?} + {:?}", x0, y0, x1, y1);
                return false;
            }
        }
        true
    }

    /// Modifies `self` inplace to ensure that it is a FIFO function (with some margin).
    pub fn ensure_fifo(&mut self) {
        for i in 1..self.points.len() {
            let diff =
                self.x_at_index(i) + self.points[i] - self.x_at_index(i - 1) - self.points[i - 1];
            if diff < T::MARGIN {
                self.points[i] += T::MARGIN - diff;
            }
        }
        debug_assert!(self.is_fifo());
    }
}

pub(crate) fn link<T: TTFNum>(f: &PwlTTF<T>, g: &PwlTTF<T>) -> PwlTTF<T> {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert!(f.is_fifo(), "{f:?}");
    debug_assert!(g.is_fifo(), "{g:?}");
    debug_assert_eq!(f.start_x, g.start_x);
    debug_assert_eq!(f.interval_x, g.interval_x);

    let mut points = Vec::with_capacity(f.points.len());
    let mut min_max = MinMax::new();

    for (f_x, f_y) in f.iter() {
        let g_y = g.eval(f_x + f_y);
        let h_y = f_y + g_y;
        points.push(h_y);
        min_max.update(h_y);
    }

    let (min, max) = min_max.into_min_max();

    let h = PwlTTF {
        points,
        min,
        max,
        start_x: f.start_x,
        interval_x: f.interval_x,
        convert_type: std::marker::PhantomData,
    };
    debug_assert!(h.is_fifo(), "{h:?}");
    h
}

pub(crate) fn link_cst_before<T: TTFNum>(g: &PwlTTF<T>, c: T) -> PwlTTF<T> {
    debug_assert!(!g.is_empty());
    debug_assert!(g.is_fifo(), "{g:?}");

    let mut points = Vec::with_capacity(g.points.len());
    let mut min_max = MinMax::new();

    for x in g.iter_x() {
        let g_y = g.eval(x + c);
        let h_y = c + g_y;
        points.push(h_y);
        min_max.update(h_y);
    }

    let (min, max) = min_max.into_min_max();

    let h = PwlTTF {
        points,
        min,
        max,
        start_x: g.start_x,
        interval_x: g.interval_x,
        convert_type: std::marker::PhantomData,
    };
    debug_assert!(h.is_fifo(), "{h:?}");
    h
}

pub(crate) fn merge<T: TTFNum>(f: &PwlTTF<T>, g: &PwlTTF<T>) -> (PwlTTF<T>, UndercutDescriptor) {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert!(f.is_fifo(), "{f:?}");
    debug_assert!(g.is_fifo(), "{g:?}");
    debug_assert_eq!(f.start_x, g.start_x);
    debug_assert_eq!(f.interval_x, g.interval_x);

    let mut descr = UndercutDescriptor::default();

    if f.max() < g.min() {
        descr.f_undercuts_strictly = true;
        return (f.clone(), descr);
    } else if g.max() < f.min() {
        descr.g_undercuts_strictly = true;
        return (g.clone(), descr);
    }

    let mut points = Vec::with_capacity(f.points.len());
    // Lower bound for the maximum `y` value of `h`.
    let mut max = f.min().max(g.min());

    for (f_y, g_y) in f.iter_y().zip(g.iter_y()) {
        let y = match f_y.partial_cmp(&g_y) {
            Some(Ordering::Equal) => f_y,
            Some(Ordering::Less) => {
                descr.f_undercuts_strictly = true;
                f_y
            }
            Some(Ordering::Greater) => {
                descr.g_undercuts_strictly = true;
                g_y
            }
            None => panic!("Cannot compare {:?} with {:?}", f_y, g_y),
        };
        if y > max {
            max = y;
        }
        points.push(y);
    }

    let h = PwlTTF {
        points,
        min: f.min().min(g.min()),
        max,
        start_x: f.start_x,
        interval_x: f.interval_x,
        convert_type: std::marker::PhantomData,
    };
    debug_assert!(h.is_fifo(), "{h:?}");
    (h, descr)
}

pub(crate) fn merge_cst<T: TTFNum>(f: &PwlTTF<T>, c: T) -> (PwlTTF<T>, UndercutDescriptor) {
    debug_assert!(!f.is_empty());
    debug_assert!(f.is_fifo(), "{f:?}");

    let mut descr = UndercutDescriptor::default();

    if c < f.max() {
        descr.g_undercuts_strictly = true;
    }
    if f.min() < c {
        descr.f_undercuts_strictly = true;
    }

    if c < f.min() {
        let h = f.clone().map(|_| c);
        return (h, descr);
    }
    if f.max() < c {
        return (f.clone(), descr);
    }

    let mut points = Vec::with_capacity(f.points.len());

    for f_y in f.iter_y() {
        points.push(f_y.min(c));
    }

    let h = PwlTTF {
        points,
        min: f.min(),
        max: c,
        start_x: f.start_x,
        interval_x: f.interval_x,
        convert_type: std::marker::PhantomData,
    };
    debug_assert!(h.is_fifo(), "{h:?}");
    (h, descr)
}

/// Returns the integral of the squared difference between function `f` and function `g`, divided
/// by the length of the period.
pub(crate) fn squared_difference<T: TTFNum>(f: &PwlTTF<T>, g: &PwlTTF<T>) -> T {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert_eq!(f.len(), g.len());
    debug_assert_eq!(f.start_x, g.start_x);
    debug_assert_eq!(f.interval_x, g.interval_x);
    let mut diff = T::ZERO;
    for (((x0, f_y0), (x1, f_y1)), ((_, g_y0), (_, g_y1))) in f.double_iter().zip(g.double_iter()) {
        // Two possible cases.
        if ((f_y0 >= g_y0) && (f_y1 <= g_y1)) || ((f_y0 <= g_y0) && (f_y1 >= g_y1)) {
            // Case 1: the `f` segment intersects the `g` segment somewhere between `x0` and `x1`.
            // The two segments intersects at point `(x, y)`.
            let x = get_x_intersection(x0, f_y0, g_y0, x1, f_y1, g_y1);
            let y = f_y1 + (f_y1 - f_y0) * (x - x0) / (x1 - x0);
            // There are two triangles:
            // - `(x0, f_y0), (x0, g_y0), (x, y)`,
            // - `(x, y) (x1, f_y1), (x1, g_y1)`.
            diff += triangle_squared_area((x0, x), (f_y0, y), (g_y0, y));
            diff += triangle_squared_area((x, x1), (y, f_y1), (y, g_y1));
        } else {
            // Case 2: either f is always below g or g is always below f on the interval.
            diff += trapezoid_squared_area((x0, x1), (f_y0, f_y1), (g_y0, g_y1));
        }
    }
    diff /= f.period_length();
    debug_assert!(diff.is_finite());
    diff
}

/// Returns the integral of the squared difference between function `f` and constant value `y`,
/// divided by the length of the period.
pub(crate) fn squared_difference_cst<T: TTFNum>(f: &PwlTTF<T>, y: T) -> T {
    debug_assert!(!f.is_empty());
    let mut diff = T::ZERO;
    for ((x0, f_y0), (x1, f_y1)) in f.double_iter() {
        // Two possible cases.
        if ((f_y0 >= y) && (f_y1 <= y)) || ((f_y0 <= y) && (f_y1 >= y)) {
            // Case 1: the `f` segment intersects the constant segment somewhere between `x0` and
            // `x1`.
            // The two segments intersects at point `(x, y)`.
            let x = get_x_intersection(x0, f_y0, y, x1, f_y1, y);
            // There are two triangles:
            // - `(x0, f_y0), (x0, y), (x, y)`,
            // - `(x, y) (x1, f_y1), (x1, y)`.
            diff += triangle_squared_area((x0, x), (f_y0, y), (y, y));
            diff += triangle_squared_area((x, x1), (y, f_y1), (y, y));
        } else {
            // Case 2: either f is always below y or y is always below f on the interval.
            diff += trapezoid_squared_area((x0, x1), (f_y0, f_y1), (y, y));
        }
    }
    diff /= f.period_length();
    debug_assert!(diff.is_finite());
    diff
}

/// Returns the integral of `[f(x) - g(x)]^2` from `x0` to `x1`, where
/// - `f` is a linear function with `f(x0) = f_y0` and `f(x1) = f_y1`,
/// - `g` is a linear function with `g(x0) = g_y0` and `g(x1) = g_y1`.
///
/// The following must be true: `f(x0) = g(x0)` or `f(x1) = g(x1)`.
/// This implies that there is a triangle defined by the points `f(x0), f(x1), g(x1)` or
/// `f(x0), g(x0), g(x1)`.
fn triangle_squared_area<T: TTFNum>(
    (x0, x1): (T, T),
    (f_y0, f_y1): (T, T),
    (g_y0, g_y1): (T, T),
) -> T {
    debug_assert!(f_y0 == g_y0 || f_y1 == g_y1);
    if f_y0 == g_y0 {
        (x1 - x0) * (f_y1 - g_y1).pow(2) / T::from_f64(3.0).unwrap()
    } else {
        (x1 - x0) * (f_y0 - g_y0).pow(2) / T::from_f64(3.0).unwrap()
    }
}

/// Returns the integral of `[f(x) - g(x)]^2` from `x0` to `x1`, where
/// - `f` is a linear function with `f(x0) = f_y0` and `f(x1) = f_y1`,
/// - `g` is a linear function with `g(x0) = g_y0` and `g(x1) = g_y1`.
///
/// The following must be true: `f` is either always below `g` or above `g` between `x0` and `x1`,
/// i.e., `f_y0 >= g_y0` XOR `f_y1 >= g_y1` must be `false`.
/// This implies that there is a trapezoid defined by the points `f(x0), g(x0), g(x1), f(x1)`.
fn trapezoid_squared_area<T: TTFNum>(
    (x0, x1): (T, T),
    (f_y0, f_y1): (T, T),
    (g_y0, g_y1): (T, T),
) -> T {
    debug_assert!(
        ((f_y0 >= g_y0) && (f_y1 >= g_y1)) || ((f_y0 <= g_y0) && (f_y1 <= g_y1)),
        "f_y0: {f_y0:?}, f_y1: {f_y1:?}, g_y0: {g_y0:?}, g_y1: {g_y1:?}"
    );
    ((x1 - x0) / T::from_f64(3.0).unwrap())
        * ((f_y0 - g_y0).pow(2) + (f_y1 - g_y1).pow(2) + (f_y0 - g_y0) * (f_y1 - g_y1))
}

pub(crate) fn apply<T: TTFNum, F: Fn(T, T) -> T>(
    f: &PwlTTF<T>,
    g: &PwlTTF<T>,
    func: F,
) -> PwlTTF<T> {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert!(f.is_fifo(), "{f:?}");
    debug_assert!(g.is_fifo(), "{g:?}");
    debug_assert_eq!(f.start_x, g.start_x);
    debug_assert_eq!(f.interval_x, g.interval_x);

    let mut points = Vec::with_capacity(f.points.len());
    let mut min_max = MinMax::new();

    for (f_y, g_y) in f.iter_y().zip(g.iter_y()) {
        let h_y = func(f_y, g_y);
        min_max.update(h_y);
        points.push(h_y);
    }

    let (min, max) = min_max.into_min_max();

    let h = PwlTTF {
        points,
        min,
        max,
        start_x: f.start_x,
        interval_x: f.interval_x,
        convert_type: std::marker::PhantomData,
    };
    debug_assert!(h.is_fifo(), "{h:?}");
    h
}

pub(crate) fn analyze_relative_position<T: TTFNum>(
    f: &PwlTTF<T>,
    g: &PwlTTF<T>,
) -> Either<Ordering, Vec<(T, Ordering)>> {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert!(f.is_fifo(), "{f:?}");
    debug_assert!(g.is_fifo(), "{g:?}");
    debug_assert_eq!(f.start_x, g.start_x);
    debug_assert_eq!(f.interval_x, g.interval_x);

    if f.max <= g.min {
        return Either::Left(Ordering::Less);
    }
    if g.max <= f.min {
        return Either::Left(Ordering::Greater);
    }

    let mut results = Vec::with_capacity(f.points.len());
    let mut rel_pos = Ordering::Equal;

    for i in 0..f.points.len() {
        let old_rel_pos = rel_pos;
        rel_pos = match f.points[i].partial_cmp(&g.points[i]) {
            Some(Ordering::Less) => Ordering::Less,
            Some(Ordering::Greater) => Ordering::Greater,
            Some(Ordering::Equal) => old_rel_pos,
            None => panic!("Cannot compare {:?} with {:?}", f.points[i], g.points[i]),
        };
        if old_rel_pos != rel_pos {
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.start_x, rel_pos));
            } else {
                debug_assert!(i > 0);
                let x = get_x_intersection(
                    f.x_at_index(i - 1),
                    f.points[i - 1],
                    g.points[i - 1],
                    f.x_at_index(i),
                    f.points[i],
                    g.points[i],
                );
                results.push((x, rel_pos));
            }
        }
    }

    if results.is_empty() {
        results.push((f.start_x, Ordering::Less));
    }

    debug_assert_eq!(results[0].0, f.start_x);
    if cfg!(debug_assertions) {
        check_analyze_relative_position(f, g, &results);
    }

    Either::Right(results)
}

fn check_analyze_relative_position<T: TTFNum>(
    f: &PwlTTF<T>,
    g: &PwlTTF<T>,
    results: &[(T, Ordering)],
) {
    for ((x, f_y), g_y) in f.iter().zip(g.iter_y()) {
        let i = match results.binary_search_by(|(t, _)| t.partial_cmp(&x).unwrap()) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let pos = results[i].1;
        match f_y.partial_cmp(&g_y) {
            Some(Ordering::Less) => assert_eq!(pos, Ordering::Less),
            Some(Ordering::Greater) => assert_eq!(pos, Ordering::Greater),
            _ => (),
        }
    }
}

/// Find `x` where the relative positioning switched.
fn get_x_intersection<T: TTFNum>(x0: T, f_y0: T, g_y0: T, x1: T, f_y1: T, g_y1: T) -> T {
    let dy0 = f_y0 - g_y0;
    let dy1 = f_y1 - g_y1;
    debug_assert!(dy0 <= T::ZERO && T::ZERO <= dy1 || dy1 <= T::ZERO && T::ZERO <= dy0);
    if dy0.is_zero() {
        x0
    } else if dy1.is_zero() {
        x1
    } else if dy0 > T::ZERO {
        debug_assert!(dy1 < T::ZERO);
        let alpha = dy0 / (dy0 - dy1);
        x0 * (T::ONE - alpha) + x1 * alpha
    } else {
        debug_assert!(dy1 > T::ZERO);
        let alpha = -dy0 / (-dy0 + dy1);
        x0 * (T::ONE - alpha) + x1 * alpha
    }
}

pub(crate) fn analyze_relative_position_to_cst<T: TTFNum>(
    f: &PwlTTF<T>,
    c: T,
) -> Either<Ordering, Vec<(T, Ordering)>> {
    debug_assert!(!f.is_empty());
    debug_assert!(f.is_fifo(), "{f:?}");

    if f.max <= c {
        return Either::Left(Ordering::Less);
    }
    if c <= f.min {
        return Either::Left(Ordering::Greater);
    }

    let mut results = Vec::with_capacity(f.points.len());
    let mut rel_pos = Ordering::Equal;

    for i in 0..f.points.len() {
        let old_rel_pos = rel_pos;
        rel_pos = match f.points[i].partial_cmp(&c) {
            Some(Ordering::Less) => Ordering::Less,
            Some(Ordering::Greater) => Ordering::Greater,
            Some(Ordering::Equal) => old_rel_pos,
            None => panic!("Cannot compare {:?} with {:?}", f.points[i], c),
        };
        if old_rel_pos != rel_pos {
            if results.is_empty() {
                // f and c were equal at the beginning of the period.
                results.push((f.start_x, rel_pos));
            } else {
                debug_assert!(i > 0);
                let x = get_x_intersection(
                    f.x_at_index(i - 1),
                    f.points[i - 1],
                    c,
                    f.x_at_index(i),
                    f.points[i],
                    c,
                );
                results.push((x, rel_pos));
            }
        }
    }

    if results.is_empty() {
        results.push((f.start_x, Ordering::Greater));
    }

    debug_assert_eq!(results[0].0, f.start_x);

    Either::Right(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn squared_difference_test() {
        let f = PwlTTF::from_values(vec![0., 0., 0.], 0., 1.);
        let g = PwlTTF::from_values(vec![2., 2., 2.], 0., 1.);
        assert_eq!(squared_difference(&f, &g), 4.);
        let f = PwlTTF::from_values(vec![0., 1., 2.], 0., 1.);
        let g = PwlTTF::from_values(vec![1., 0., 0.], 0., 1.);
        let expected_res: f64 = (1. / 6. + 1. / 6. + 7. / 3.) / 2.;
        assert!((squared_difference(&f, &g) - expected_res).abs() < 1.0e-8);
    }

    #[test]
    fn squared_difference_cst_test() {
        let f = PwlTTF::from_values(vec![0., 0., 0.], 0., 1.);
        assert_eq!(squared_difference_cst(&f, 2.0), 4.);
        let f = PwlTTF::from_values(vec![0., 2., 3., 1., 0.], 0., 1.);
        assert_eq!(
            squared_difference_cst(&f, 1.0),
            (1. / 6. + 1. / 6. + 7. / 3. + 4. / 3. + 1. / 3.) / 4.
        );
    }
}
