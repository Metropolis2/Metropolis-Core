// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::cmp::Ordering;
use std::fmt;
use std::ops;

use either::Either;
use itertools::Itertools;
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize};

use crate::point::*;
use crate::ttf_num::TTFNum;
use crate::NoSimplification;
use crate::{Simplification, Simplify, UndercutDescriptor};

const BUCKET_SIZE: usize = 8;

/// A piecewise-linear function represented by a Vec of points `(x, y)`.
///
/// The `x` values are of type `X`, the `y` values are of type `Y`.
/// The `T` generic type is used to convert from `X` to `Y`.
#[derive(PartialEq, Eq, Serialize, JsonSchema)]
#[serde(bound(serialize = "X: Clone + Serialize, Y: Clone + Serialize"))]
pub struct PwlXYF<X, Y, T, S = Simplification> {
    /// Breakpoints representing the function.
    #[schemars(with = "Vec<RawPoint<X, Y>>")]
    points: Vec<Point<X, Y>>,
    /// Minimum `y` value of the function.
    #[schemars(skip_deserializing)]
    min: Option<Y>,
    /// Maximum `y` value of the function.
    #[schemars(skip_deserializing)]
    max: Option<Y>,
    /// Array `[x0, x1]` representing the domain of the function.
    period: [X; 2],
    #[serde(skip_serializing)]
    #[schemars(skip)]
    buckets: Vec<usize>,
    #[serde(skip_serializing)]
    #[schemars(skip)]
    bucket_shift: usize,
    #[serde(skip)]
    #[schemars(skip)]
    convert_type: std::marker::PhantomData<T>,
    #[serde(skip)]
    #[schemars(skip)]
    simplification: std::marker::PhantomData<S>,
}

/// A piecewise-linear function represented by a Vec of points `(x, y)`, where the `x` and `y`
/// values have the same type.
pub type PwlTTF<T, S = Simplification> = PwlXYF<T, T, T, S>;

// Implement Debug manually so that we do not care if `T` and `S` implement Debug themself.
impl<X: fmt::Debug, Y: fmt::Debug, T, S> fmt::Debug for PwlXYF<X, Y, T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PwlXYF")
            .field("points", &self.points)
            .field("min", &self.min)
            .field("max", &self.max)
            .field("period", &self.period)
            .field("buckets", &self.buckets)
            .field("bucket_shift", &self.bucket_shift)
            .finish()
    }
}

// Implement Clone manually so that we do not care if `T` and `S` implement Clone themself.
impl<X: Clone, Y: Clone, T, S> Clone for PwlXYF<X, Y, T, S> {
    fn clone(&self) -> Self {
        Self {
            points: self.points.clone(),
            min: self.min.clone(),
            max: self.max.clone(),
            period: self.period.clone(),
            buckets: self.buckets.clone(),
            bucket_shift: self.bucket_shift,
            convert_type: std::marker::PhantomData,
            simplification: std::marker::PhantomData,
        }
    }
}

impl<'de, X, Y, T, S> Deserialize<'de> for PwlXYF<X, Y, T, S>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self::from_deserialized(DeserPwlXYF::deserialize(
            deserializer,
        )?))
    }
}

#[derive(Deserialize)]
#[serde(rename = "PwlXYF")]
pub(crate) struct DeserPwlXYF<X, Y> {
    points: Vec<Point<X, Y>>,
    period: [X; 2],
}

impl<X, Y, T, S> PwlXYF<X, Y, T, S> {
    /// Consumes the [PwlXYF] and returns a vector of values `(x, y)`.
    pub fn into_points(self) -> Vec<(X, Y)> {
        self.points.into_iter().map(|p| (p.x, p.y)).collect()
    }

    /// Consumes the [PwlXYF] and returns two vector of values `x` and `y`.
    pub fn into_xs_and_ys(self) -> (Vec<X>, Vec<Y>) {
        self.points.into_iter().map(|p| (p.x, p.y)).unzip()
    }

    /// Converts a `PwlXYF<X, Y, T, S>` to `PwlXYF<X, Y, T, Simplification>`.
    pub fn with_simplification(self) -> PwlXYF<X, Y, T, Simplification> {
        PwlXYF {
            points: self.points,
            min: self.min,
            max: self.max,
            period: self.period,
            buckets: self.buckets,
            bucket_shift: self.bucket_shift,
            convert_type: self.convert_type,
            simplification: std::marker::PhantomData,
        }
    }

    /// Converts a `PwlXYF<X, Y, T, S>` to `PwlXYF<X, Y, T, NoSimplification>`.
    pub fn without_simplification(self) -> PwlXYF<X, Y, T, NoSimplification> {
        PwlXYF {
            points: self.points,
            min: self.min,
            max: self.max,
            period: self.period,
            buckets: self.buckets,
            bucket_shift: self.bucket_shift,
            convert_type: self.convert_type,
            simplification: std::marker::PhantomData,
        }
    }
}

impl<X, Y, T, S> PwlXYF<X, Y, T, S>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    fn from_deserialized(input: DeserPwlXYF<X, Y>) -> Self {
        if input.points.is_empty() {
            panic!("Cannot deserialize a PwlXYF with no point");
        }
        let (min_y, max_y) = input
            .points
            .iter()
            .map(|p| p.y)
            .minmax()
            .into_option()
            .unwrap();
        let f: PwlXYFBuilder<X, Y, T, S> = PwlXYFBuilder {
            points: input.points,
            min: Some(min_y),
            max: Some(max_y),
            period: input.period,
            convert_type: std::marker::PhantomData,
            simplification: std::marker::PhantomData,
        };
        f.finish()
    }
}

impl<X, Y, T, S> PwlXYF<X, Y, T, S>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    fn with_capacity(period: [X; 2], capacity: usize) -> Self {
        PwlXYF {
            points: Vec::with_capacity(capacity),
            min: None,
            max: None,
            period,
            buckets: Vec::with_capacity(BUCKET_SIZE),
            bucket_shift: 0,
            convert_type: std::marker::PhantomData,
            simplification: std::marker::PhantomData,
        }
    }

    /// Returns the period of the function (first and last `x` value).
    pub fn period(&self) -> &[X; 2] {
        &self.period
    }

    /// Iterates over the `(x, y)` values of the function.
    pub fn iter(&self) -> impl Iterator<Item = &Point<X, Y>> {
        self.points.iter()
    }

    /// Iterates over the `x` values of the function.
    pub fn iter_x(&self) -> impl Iterator<Item = &X> {
        self.iter().map(|p| &p.x)
    }

    /// Iterates over the `y` values of the function.
    pub fn iter_y(&self) -> impl Iterator<Item = &Y> {
        self.iter().map(|p| &p.y)
    }

    /// Iterates over values `((x_i, y_i), (x_i+1, y_i+1))`.
    pub fn double_iter(&self) -> impl Iterator<Item = (&Point<X, Y>, &Point<X, Y>)> {
        self.points.iter().zip(self.points[1..].iter())
    }

    fn update_min_max(&mut self, y: Y) {
        if self.min.is_none() {
            assert!(self.max.is_none());
            self.min = Some(y);
            self.max = Some(y);
        }
        if y < self.min.unwrap() {
            self.min = Some(y);
        } else if y > self.max.unwrap() {
            self.max = Some(y);
        }
    }

    /// Returns `true` if the function is empty (there is no breakpoint).
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// Returns the number of breakpoints of the function.
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Returns the middle `x` value.
    pub fn middle_x(&self) -> X {
        self.period[0].average(self.period[1])
    }

    /// Returns the minimum `y` value.
    pub fn get_min(&self) -> Y {
        debug_assert!(self.min.is_some());
        debug_assert!(self.min.unwrap().approx_eq(
            self.iter_y()
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap()
        ));
        self.min.unwrap()
    }

    /// Returns the maximum `y` value.
    pub fn get_max(&self) -> Y {
        debug_assert!(self.max.is_some());
        debug_assert!(
            self.max.unwrap().is_infinite()
                || self.max.unwrap().approx_eq(
                    self.iter_y()
                        .max_by(|a, b| a.partial_cmp(b).unwrap())
                        .unwrap()
                )
        );
        self.max.unwrap()
    }

    /// Returns `true` if the function is constant.
    pub fn is_cst(&self) -> bool {
        self.get_min().approx_eq(&self.get_max())
    }

    fn get_bucket(&self, x: X) -> usize {
        debug_assert!(x >= self.period[0]);
        let bucket = (x - self.period[0]).to_usize().unwrap_or_else(|| {
            panic!(
                "Value cannot be represented as usize: {:?} - {:?} = {:?}",
                x,
                self.period[0],
                x - self.period[0]
            )
        }) >> self.bucket_shift;
        if bucket > 0 {
            bucket - 1
        } else {
            debug_assert!(bucket < self.buckets.len());
            bucket
        }
    }

    /// Evaluates the value of the function at the given `x` value.
    pub fn eval(&self, x: X) -> Y {
        debug_assert!(!self.is_empty());
        debug_assert!(x >= self.period[0], "{:?} < {:?}", x, self.period[0]);
        if x.approx_ge(&self.period[1]) {
            return self[self.len() - 1].y;
        }
        let bucket = self.get_bucket(x);
        debug_assert!(self.buckets[bucket] < self.len());
        debug_assert!(self.buckets[bucket] == 0 || self[self.buckets[bucket] - 1].x.approx_le(&x));
        for i in self.buckets[bucket]..self.len() {
            if x.approx_le(&self[i].x) {
                if x.approx_eq(&self[i].x) {
                    return self[i].y;
                }
                debug_assert!(i > 0);
                debug_assert!(self[i - 1].x.approx_le(&x));
                debug_assert!(x.approx_le(&self[i].x));
                return linear_interp(self[i - 1], self[i], x);
            }
        }
        debug_assert!(self.points.last().unwrap().x.approx_le(&x));
        // We assume that travel time stays constant after the last breakpoint.
        self.points.last().unwrap().y
    }

    /// Takes an iterator of `x` values that needs to be evaluated and returns an iterator of the
    /// computed `y` values.
    ///
    /// The `x` values need to be in increasing order and within the PwlXYF's period.
    pub fn iter_eval<'a>(
        &'a self,
        iter: impl Iterator<Item = X> + 'a,
    ) -> impl Iterator<Item = Y> + 'a {
        // Minimum index of x.
        let mut min_index = 0;
        iter.map(move |x| {
            let bucket = self.get_bucket(x);
            min_index = std::cmp::min(min_index, self.buckets[bucket]);
            debug_assert!(self[min_index].x.approx_le(&x));
            for i in min_index..self.len() {
                if x.approx_le(&self[i].x) {
                    if x.approx_eq(&self[i].x) {
                        return self[i].y;
                    }
                    debug_assert!(i > 0);
                    debug_assert!(self[i - 1].x.approx_le(&x));
                    debug_assert!(x.approx_le(&self[i].x));
                    return linear_interp(self[i - 1], self[i], x);
                }
            }
            assert!(x.approx_le(&self.period[1]));
            Y::default()
        })
    }

    fn first_index_with_x_ge(&self, x: X) -> usize {
        debug_assert!(!self.is_empty());
        debug_assert!(x >= self.period[0], "{:?} < {:?}", x, self.period[0]);
        debug_assert!(x <= self.period[1], "{:?} > {:?}", x, self.period[1]);
        let bucket = self.get_bucket(x);
        let index = self.buckets[bucket];
        debug_assert!(index < self.len());
        debug_assert!(index == 0 || self[index - 1].x.approx_le(&x));
        for i in index..self.len() {
            if self[i].x >= x {
                debug_assert!(i == 0 || self[i - 1].x < x);
                return i;
            }
        }
        debug_assert!(self[self.len() - 1].x < x);
        self.len()
    }

    fn setup_buckets(&mut self) {
        let period_len = (self.period[1] - self.period[0])
            .to_usize()
            .unwrap_or_else(|| {
                panic!(
                    "Value cannot be represented as usize: {:?}",
                    self.period[1] - self.period[0]
                )
            });
        self.bucket_shift = std::mem::size_of::<usize>() * 8 - 1;
        let n = period_len * BUCKET_SIZE / self.len();
        // Compute the position of the most significant bit of n.
        while n & (1 << self.bucket_shift) == 0 {
            self.bucket_shift -= 1;
        }

        let n_buckets = std::cmp::max(1, period_len >> self.bucket_shift);
        self.buckets = vec![0; n_buckets];

        let mut bucket = 0;
        for (i, x) in self.points.iter().map(|p| p.x).enumerate() {
            while self.get_bucket(x) >= bucket {
                debug_assert!(bucket < n_buckets);
                self.buckets[bucket] = i;
                bucket += 1;
            }
        }
        while bucket < n_buckets {
            self.buckets[bucket] = self.len() - 1;
            bucket += 1;
        }
    }

    /// Returns a new PwlXYF equal to the input PwlXYF plus a constant value.
    #[must_use]
    pub fn add(&self, c: Y) -> Self {
        self.map(|y| y + c)
    }

    /// Returns a new PwlXYF by applying a given function on the `y` values of the two input PwlXYFs.
    #[must_use]
    pub fn map<F: Fn(Y) -> W, W>(&self, func: F) -> PwlXYF<X, W, T, S>
    where
        F: Fn(Y) -> W,
        W: TTFNum + Into<T> + From<T>,
    {
        debug_assert!(!self.is_empty());
        let mut xyf = PwlXYF::<X, W, T, S>::with_capacity(self.period, self.len());
        xyf.min = Some(func(self.get_min()));
        xyf.max = Some(func(self.get_max()));
        xyf.points = self
            .points
            .iter()
            .map(|p| Point {
                x: p.x,
                y: func(p.y),
            })
            .collect();
        // We do not need to update the buckets because the `x` values did not change.
        xyf.buckets = self.buckets.clone();
        xyf.bucket_shift = self.bucket_shift;
        xyf
    }

    /// Adds new `x` breakpoints to a [PwlTTF].
    ///
    /// The new breakpoints must be sorted in increasing order.
    pub fn add_x_breakpoints(&mut self, xs: Vec<X>) {
        if xs.is_empty() {
            return;
        }
        // Find the breakpoints that really need to be added (i.e., there are not already in the
        // function).
        // Also count the number of Copy operations that would be required to insert all
        // breakpoints with `Vec::insert`.
        let mut points_to_add = Vec::with_capacity(xs.len());
        let mut nb_copy = 0;
        for x in xs
            .into_iter()
            .skip_while(|&x| x <= self.period[0])
            .take_while(|&x| x <= self.period[1])
        {
            let i = self.first_index_with_x_ge(x);
            if x.approx_ne(&self[i].x) {
                let y = linear_interp(self[i - 1], self[i], x);
                points_to_add.push((i, Point { x, y }));
                nb_copy += self.len() - i;
            }
        }
        if points_to_add.is_empty() {
            return;
        }
        if nb_copy <= self.len() {
            // It is faster to insert all new breakpoints with `Vec::insert`.
            // We insert the elements in decreasing order so that the indices stay valid.
            for (i, p) in points_to_add.into_iter().rev() {
                self.points.insert(i, p);
            }
        } else {
            let old_points = std::mem::take(&mut self.points);
            let mut new_points = Vec::with_capacity(old_points.len() + points_to_add.len());
            let mut iter = old_points.into_iter().peekable();
            for (_, new_p) in points_to_add.into_iter() {
                while let Some(p) = iter.peek() {
                    debug_assert!(p.x.approx_ne(&new_p.x));
                    if p.x > new_p.x {
                        break;
                    }
                    new_points.push(*p);
                    iter.next();
                }
                new_points.push(new_p);
            }
            // Add the remaining points.
            for p in iter {
                new_points.push(p);
            }
            self.points = new_points;
        }
        self.setup_buckets();
    }

    /// Constrains the [PwlXYF] to a given `x`-domain.
    ///
    /// *Panics* if the given domain and the current domain of the PwlXYF do not overlap.
    ///
    /// *Panics* if the given domain has a non-positive length.
    pub fn constrain_to_domain(&mut self, domain: [X; 2]) {
        assert!(
            domain[0].approx_lt(&self.period[1]),
            "The given and current domain must overlap"
        );
        assert!(
            domain[1].approx_gt(&self.period[0]),
            "The given and current domain must overlap"
        );
        assert!(domain[0].approx_lt(&domain[1]));
        if self.period[0].approx_ge(&domain[0]) && self.period[1].approx_le(&domain[1]) {
            debug_assert!(self.points[0].x.approx_ge(&domain[0]));
            debug_assert!(self.points[self.len() - 1].x.approx_le(&domain[1]));
            return;
        }
        // `min_idx` is the minimum index to keep.
        let min_idx = if self.period[0].approx_lt(&domain[0]) {
            let min_idx = self.first_index_with_x_ge(domain[0]);
            debug_assert!(min_idx >= 1 && min_idx < self.len());
            if self[min_idx].x.approx_ne(&domain[0]) {
                // Update the point at id `min_idx - 1` so that it becomes the new starting point of
                // the PwlXYF.
                debug_assert!(self[min_idx - 1].x.approx_lt(&domain[0]));
                debug_assert!(self[min_idx].x.approx_gt(&domain[0]));
                self[min_idx - 1] = Point {
                    x: domain[0],
                    y: self.eval(domain[0]),
                };
                min_idx - 1
            } else {
                min_idx
            }
        } else {
            // The first `x` value does not change.
            0
        };
        // `max_idx` is the maximum index to keep.
        let max_idx = if self.period[1].approx_gt(&domain[1]) {
            let max_idx = self.first_index_with_x_ge(domain[1]);
            debug_assert!(max_idx >= std::cmp::max(min_idx, 1));
            debug_assert!(max_idx < self.len());
            if self[max_idx].x.approx_ne(&domain[1]) {
                // Update the point at id `max_idx` so that it becomes the new ending point of
                // the PwlXYF.
                debug_assert!(self[max_idx - 1].x.approx_lt(&domain[1]));
                debug_assert!(self[max_idx].x.approx_gt(&domain[1]));
                self[max_idx] = Point {
                    x: domain[1],
                    y: self.eval(domain[1]),
                };
            }
            max_idx
        } else {
            // The last `x` value does not change.
            self.len() - 1
        };
        // Keep only the valid indices.
        debug_assert!(min_idx < max_idx);
        debug_assert!(max_idx < self.len());
        self.points.drain(max_idx + 1..);
        self.points.drain(..min_idx);
        self.period = [self[0].x, self[self.len() - 1].x];
        let (min_y, max_y) = self
            .points
            .iter()
            .map(|p| p.y)
            .minmax()
            .into_option()
            .unwrap();
        self.min = Some(min_y);
        self.max = Some(max_y);
        self.setup_buckets();
    }
}

impl<X, Y, T, S> PwlXYF<X, Y, T, S>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
    S: Simplify,
{
    /// Creates a new PwlXYF from a Vec of `x` values and a Vec of `y` values.
    pub fn from_x_and_y(x: Vec<X>, y: Vec<Y>) -> Self {
        assert_eq!(x.len(), y.len());
        let period = [x[0], x[x.len() - 1]];
        Self::from_iterator(x.into_iter().zip(y.into_iter()), period)
    }

    /// Creates a new PwlXYF from a Vec of `(x, y)` values.
    pub fn from_breakpoints(points: Vec<(X, Y)>) -> Self {
        let period = [points[0].0, points[points.len() - 1].0];
        Self::from_iterator(points.into_iter(), period)
    }

    /// Creates a new PwlXYF from an Iterator over both `x` and `y` values.
    pub fn from_iterator(iter: impl Iterator<Item = (X, Y)>, period: [X; 2]) -> Self {
        let mut xyf_builder = if let (_, Some(capacity)) = iter.size_hint() {
            PwlXYFBuilder::with_capacity(period, capacity)
        } else {
            PwlXYFBuilder::new(period)
        };
        for (x, y) in iter {
            xyf_builder.push(x, y);
        }
        xyf_builder.finish()
    }
}

impl<T, U, S> PwlXYF<T, T, U, S> {
    /// Convenient way to convert a `PwlXYF<T, T, U>` into a `PwlTTF<T>`.
    pub fn to_ttf(self) -> PwlTTF<T, S> {
        PwlTTF {
            points: self.points,
            min: self.min,
            max: self.max,
            period: self.period,
            buckets: self.buckets,
            bucket_shift: self.bucket_shift,
            convert_type: std::marker::PhantomData,
            simplification: std::marker::PhantomData,
        }
    }
}

impl<T: TTFNum, S> PwlTTF<T, S> {
    /// Modifies the `y` values to force the PwlTTF to be FIFO (first-in, first-out).
    ///
    /// A PwlTTF is FIFO if its `z = x + y` values are non-decreasing.
    pub fn ensure_fifo(&mut self) {
        for i in 1..self.len() {
            if self[i].x + self[i].y < self[i - 1].x + self[i - 1].y {
                self[i].y = self[i - 1].x + self[i - 1].y - self[i].x;
            }
        }
    }

    fn is_fifo(&self) -> bool {
        for (p, q) in self.double_iter() {
            if (q.x + q.y).approx_lt(&(p.x + p.y)) {
                println!("{:?}", self);
                return false;
            }
        }
        true
    }

    /// Returns the index `i` such that `z_i = x_i + y_i >= z` and `z_i-1 = x_i-1 + y_i-1 < z`.
    ///
    /// Returns `None` if such an index does not exist.
    fn first_index_with_z_ge(&self, z: T) -> Option<usize> {
        debug_assert!(!self.is_empty());
        if z < self.period[0] + self.points[0].y {
            return None;
        }
        if z > self.period[1] + self.points[self.len() - 1].y {
            return None;
        }
        // `x_min` is such that `x_min <= x*` where `x* + f(x*) = z`.
        let x_min = z - self.get_max();
        // `index` is a lower bound to the index that we search.
        let index = if x_min >= self.period[0] {
            let bucket = self.get_bucket(x_min);
            self.buckets[bucket]
        } else {
            0
        };
        debug_assert!(index < self.len());
        debug_assert!(index == 0 || (self[index - 1].x + self[index - 1].y).approx_le(&z));
        for i in index..self.len() {
            if self[i].x + self[i].y >= z {
                debug_assert!(i == 0 || self[i - 1].x + self[i - 1].y < z);
                return Some(i);
            }
        }
        debug_assert!(self[self.len() - 1].x + self[self.len() - 1].y < z);
        Some(self.len())
    }

    /// Returns the `x` value of the function such that `x + f(x) = z`.
    ///
    /// Returns `None` if `z` is smaller than the smallest `x + y` or if `z` is larger than the
    /// largest `x + y`.
    pub fn x_at_z(&self, z: T) -> Option<T> {
        let i = self.first_index_with_z_ge(z)?;
        let x = if i == 0 {
            self[0].x
        } else if i == self.len() {
            // Maximum possible z is the value of z when x is equal to the end of the period.
            let max_z = self.period[1] + self[self.len() - 1].y;
            if z <= max_z {
                // After the last x breakpoint, the y is constant and equal to the last value of y.
                z - self[self.len() - 1].y
            } else {
                panic!(
                    "Value {:?} is greater than last arrival time ({:?})",
                    z, max_z
                );
            }
        } else {
            inv_linear_interp(self[i - 1], self[i], z)
        };
        debug_assert!(
            x + self.eval(x) - z < T::large_margin(),
            "{:?} != {:?}",
            x + self.eval(x),
            z
        );
        Some(x)
    }

    /// Simplifies the PWL function using Reumann-Witkam simplification.
    pub fn approximate(&mut self, error: T) {
        if self.len() <= 2 {
            return;
        }
        let mut current_segment = [self[0], self[1]];
        let mut ids_to_keep = Vec::with_capacity(self.len());
        ids_to_keep.push(0);
        for (current_id, (p0, p1)) in self.double_iter().enumerate().skip(1) {
            if !segment_contains(current_segment, error, p1) {
                ids_to_keep.push(current_id);
                // Update the segment.
                current_segment = [*p0, *p1];
            }
        }
        // Always keep the last point.
        ids_to_keep.push(self.len() - 1);
        if ids_to_keep.len() == self.len() {
            return;
        }
        self.min = None;
        self.max = None;
        let mut new_points = Vec::with_capacity(ids_to_keep.len());
        for &id in ids_to_keep.iter() {
            new_points.push(self[id]);
            self.update_min_max(self[id].y);
        }
        self.points = new_points;
        self.setup_buckets();
    }

    /// Returns the average `y` values for different `x` intervals.
    ///
    /// Given `n` intervals `[x_0, x_1, ..., x_n]`, the function returns `n - 1` values `[y_0, y_1,
    /// ..., y_n-1]`, where the value `y_i` is the average `y` value in the interval `[x_i,
    /// x_i-1]`.
    pub fn average_y_in_intervals(&self, xs: &[T]) -> Vec<T> {
        assert!(xs[0] >= self.period[0]);
        assert!(xs[xs.len() - 1] <= self.period[1]);
        let mut ys = Vec::with_capacity(xs.len());
        let mut iter = self.double_iter().enumerate().peekable();
        let last_index = self.len() - 1;
        for (&x0, &x1) in xs.iter().zip(xs[1..].iter()) {
            debug_assert!(x1 > x0);
            // We find the largest `i` such that `self[i].x <= x0` and the smallest `j` such that
            // `self[j].x >= x1`.
            while let Some((_, (_, &q))) = iter.peek() {
                if q.x > x0 {
                    break;
                }
                iter.next();
            }
            let i = iter.peek().map(|&(i, _)| i).unwrap_or(last_index);
            while let Some((_, (_, &q))) = iter.peek() {
                if q.x >= x1 {
                    break;
                }
                iter.next();
            }
            let j = iter.peek().map(|&(j, _)| j).unwrap_or(last_index) + 1;
            ys.push(self.average_y_in_interval(x0, x1, i, j));
        }
        ys
    }

    fn average_y_in_interval(&self, x0: T, x1: T, i: usize, j: usize) -> T {
        debug_assert!(x0 < x1);
        debug_assert!(i < j);
        debug_assert!(self[i].x <= x0);
        debug_assert!(i + 1 == self.len() || self[i + 1].x > x0);
        debug_assert!(self[j - 1].x < x1);
        debug_assert!(j == self.len() || self[j].x >= x1);
        // Point of `self` at `x0`.
        let p0 = if self[i].x.approx_eq(&x0) {
            self[i]
        } else if i == self.len() - 1 {
            Point {
                x: x0,
                y: self[i].y,
            }
        } else {
            Point {
                x: x0,
                y: linear_interp(self[i], self[i + 1], x0),
            }
        };
        // Point of `self` at `x1`.
        let p1 = if j == self.len() {
            Point {
                x: x1,
                y: self[j - 1].y,
            }
        } else if self[j].x.approx_eq(&x1) {
            self[j]
        } else {
            Point {
                x: x1,
                y: linear_interp(self[j - 1], self[j], x1),
            }
        };
        if i + 1 == j {
            return area_below(p0, p1) / (x1 - x0);
        }
        let mut y = area_below(p0, self[i + 1]);
        for h in (i + 1)..(j - 1) {
            y += area_below(self[h], self[h + 1]);
        }
        y += area_below(self[j - 1], p1);
        y / (x1 - x0)
    }

    #[allow(dead_code)]
    fn dbg_check_link(&self, f: &Self, g: &Self) -> bool {
        let mut x_values = Vec::with_capacity(f.len() + g.len() + self.len());
        for &x in g.iter_x() {
            x_values.push(x);
        }
        for &x in f.iter_x() {
            x_values.push(x);
        }
        for &x in self.iter_x() {
            x_values.push(x);
        }

        for x in x_values {
            let result = self.eval(x);
            let f_res = f.eval(x);
            let expected_result = f_res + g.eval(f_res);
            debug_assert!(
                result.approx_eq(&expected_result),
                "h(x) =  {:?} != f(x) + g(f(x)) = {:?} + {:?} = {:?}",
                result,
                f_res,
                g.eval(f_res),
                expected_result
            );
        }

        true
    }

    #[allow(dead_code)]
    fn dbg_check_min(&self, f: &Self, g: &Self) -> bool {
        let mut x_values = Vec::with_capacity(f.len() + g.len() + self.len());
        for &x in g.iter_x() {
            x_values.push(x);
        }
        for &x in f.iter_x() {
            x_values.push(x);
        }
        for &x in self.iter_x() {
            x_values.push(x);
        }

        for x in x_values {
            let result = self.eval(x);
            let expected_result = f.eval(x).min(g.eval(x));
            debug_assert!(
                result.approx_eq(&expected_result),
                "h(x) = {:?} != min(f(x), g(x)) = min({:?}, {:?}) = {:?}",
                self.eval(x),
                f.eval(x),
                g.eval(x),
                f.eval(x).min(g.eval(x))
            );
        }

        true
    }

    /// Adds new `x` breakpoints corresponding to the given `z` values.
    ///
    /// The new breakpoints must be sorted in increasing order.
    pub fn add_z_breakpoints(&mut self, mut zs: Vec<T>) {
        // Computes the `x` corresponding to each `z`.
        zs.retain_mut(|z| {
            if let Some(x) = self.x_at_z(*z) {
                *z = x;
                true
            } else {
                false
            }
        });
        self.add_x_breakpoints(zs);
    }
}

impl<X, Y, T, S> ops::Index<usize> for PwlXYF<X, Y, T, S> {
    type Output = Point<X, Y>;

    fn index(&self, i: usize) -> &Self::Output {
        &self.points[std::cmp::min(i, self.points.len() - 1)]
    }
}

impl<X, Y, T, S> ops::IndexMut<usize> for PwlXYF<X, Y, T, S> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        let n = self.points.len();
        &mut self.points[std::cmp::min(i, n - 1)]
    }
}

fn linear_interp<X, Y, T>(p: Point<X, Y>, q: Point<X, Y>, x: X) -> Y
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    debug_assert!(p.x.approx_le(&x));
    debug_assert!(x.approx_le(&q.x));
    let m = (q.y - p.y).into() / (q.x - p.x).into();
    <Y as From<T>>::from(m * (x - p.x).into() + p.y.into())
}

fn inv_linear_interp<T: TTFNum>(p: Point<T, T>, q: Point<T, T>, z: T) -> T {
    debug_assert!((p.x + p.y).approx_le(&z));
    debug_assert!(z.approx_le(&(q.x + q.y)));
    let m = (q.x - p.x) / (q.x + q.y - p.x - p.y);
    m * (z - p.x - p.y) + p.x
}

fn area_below<T: TTFNum>(p: Point<T, T>, q: Point<T, T>) -> T {
    let (min_y, max_y) = if p.y > q.y { (q.y, p.y) } else { (p.y, q.y) };
    (q.x - p.x) * (min_y + (max_y.average(min_y) - min_y))
}

pub(crate) fn link<T: TTFNum, S1: Simplify, S2>(
    f: &PwlTTF<T, S1>,
    g: &PwlTTF<T, S2>,
) -> PwlTTF<T, S1> {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert!(f.is_fifo());
    debug_assert_eq!(f.period, g.period);
    debug_assert!(f[0].x.approx_eq(&g[0].x));
    debug_assert!(f.get_min() >= T::zero());
    debug_assert!(g.get_min() >= T::zero());

    let mut h: PwlTTFBuilder<T, S1> = PwlTTFBuilder::with_capacity(f.period, f.len() + g.len());
    let f_first_ta = f.period[0] + f.eval(f.period[0]);
    let mut i = if f_first_ta <= g.period[1] {
        g.first_index_with_x_ge(f_first_ta)
    } else {
        g.len()
    };
    let mut j = 0;

    while i < g.len() && j < f.len() {
        let (x, y);
        if g[i].x.approx_eq(&(f[j].x + f[j].y)) {
            x = f[j].x;
            y = f[j].y + g[i].y;
            i += 1;
            j += 1;
        } else if g[i].x < f[j].x + f[j].y {
            x = inv_linear_interp(f[j - 1], f[j], g[i].x);
            y = g[i].x + g[i].y - x;
            i += 1;
        } else {
            x = f[j].x;
            y = f[j].y + linear_interp(g[i - 1], g[i], f[j].x + f[j].y);
            j += 1;
        }
        h.push(x, y);
    }
    for j in j..f.len() {
        let x = f[j].x;
        let y = f[j].y + g[g.len() - 1].y;
        h.push(x, y);
    }
    for i in i..g.len() {
        let x = g[i].x - f[f.len() - 1].y;
        let y = f[f.len() - 1].y + g[i].y;
        h.push(x, y);
    }
    let h = h.finish();
    debug_assert!(h.is_fifo());
    // debug_assert!(h.dbg_check_link(f, g));
    h
}

pub(crate) fn link_cst_before<T: TTFNum, S1: Simplify, S2>(
    g: &PwlTTF<T, S2>,
    c: T,
) -> PwlTTF<T, S1> {
    debug_assert!(!g.is_empty());

    let mut h: PwlTTFBuilder<T, S1> = PwlTTFBuilder::with_capacity(g.period, g.len());
    let i = g.first_index_with_x_ge(g.period[0] + c);

    if i == g.len() {
        // g ends before first g.period[0] + c.
        h.push(h.period[0], c + g[0].x);
    }

    for i in i..g.len() {
        let p = Point {
            x: g[i].x - c,
            y: g[i].y + c,
        };
        debug_assert!(p.x >= h.period[0]);
        if p.x > h.period[0] && h.is_empty() {
            // Add first point.
            h.push(h.period[0], c + g.eval(h.period[0] + c));
        }
        h.push_point(p);
    }

    let h = h.finish();
    debug_assert!(h.is_fifo());
    h
}

pub(crate) fn merge<T: TTFNum, S: Simplify>(
    f: &PwlTTF<T, S>,
    g: &PwlTTF<T, S>,
) -> (PwlTTF<T, S>, UndercutDescriptor) {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert_eq!(f.period, g.period);

    let mut descr = UndercutDescriptor::default();

    if f.get_max().approx_lt(&g.get_min()) {
        descr.f_undercuts_strictly = true;
        return (f.clone(), descr);
    } else if g.get_max().approx_lt(&f.get_min()) {
        descr.g_undercuts_strictly = true;
        return (g.clone(), descr);
    }

    let mut h: PwlTTFBuilder<T, S> = PwlTTFBuilder::with_capacity(f.period, f.len() + g.len());

    debug_assert_eq!(f[0].x, h.period[0]);
    debug_assert_eq!(g[0].x, h.period[0]);
    h.push(h.period[0], f[0].y.min(g[0].y));

    let mut i = 1;
    let mut j = 1;

    while i < f.len() && j < g.len() {
        if intersect(&f[i - 1], &f[i], &g[j - 1], &g[j]) {
            let p = intersection_point(&f[i - 1], &f[i], &g[j - 1], &g[j]);
            h.push_point(p);
            descr.f_undercuts_strictly = true;
            descr.g_undercuts_strictly = true;
        }

        if f[i].x.approx_eq(&g[j].x) {
            if f[i].y.approx_eq(&g[j].y) {
                h.push_point(f[i]);

                if rotation::<T, T, T>(&g[j - 1], &f[i - 1], &f[i]) == Rotation::CounterClockwise
                    || rotation::<T, T, T>(&f[i], &f[i + 1], &g[j + 1])
                        == Rotation::CounterClockwise
                {
                    descr.f_undercuts_strictly = true;
                }

                if rotation::<T, T, T>(&g[j - 1], &f[i - 1], &f[i]) == Rotation::Clockwise
                    || rotation::<T, T, T>(&f[i], &f[i + 1], &g[j + 1]) == Rotation::Clockwise
                {
                    descr.g_undercuts_strictly = true;
                }
            } else if f[i].y < g[j].y {
                h.push_point(f[i]);
                descr.f_undercuts_strictly = true;
            } else {
                h.push_point(g[j]);
                descr.g_undercuts_strictly = true;
            }
            i += 1;
            j += 1;
        } else if f[i].x < g[j].x {
            match rotation::<T, T, T>(&g[j - 1], &f[i], &g[j]) {
                Rotation::CounterClockwise => {
                    descr.f_undercuts_strictly = true;
                    h.push_point(f[i]);
                }
                Rotation::Colinear => {
                    if rotation::<T, T, T>(&g[j - 1], &f[i - 1], &f[i])
                        == Rotation::CounterClockwise
                        || rotation::<T, T, T>(&f[i], &f[i + 1], &g[j])
                            == Rotation::CounterClockwise
                    {
                        descr.f_undercuts_strictly = true;
                        h.push_point(f[i]);
                    }
                    if rotation::<T, T, T>(&g[j - 1], &f[i - 1], &f[i]) == Rotation::Clockwise
                        || rotation::<T, T, T>(&f[i], &f[i + 1], &g[j]) == Rotation::Clockwise
                    {
                        descr.g_undercuts_strictly = true;
                    }
                }
                Rotation::Clockwise => (),
            }
            i += 1;
        } else {
            match rotation::<T, T, T>(&f[i - 1], &g[j], &f[i]) {
                Rotation::CounterClockwise => {
                    descr.g_undercuts_strictly = true;
                    h.push_point(g[j]);
                }
                Rotation::Colinear => {
                    if rotation::<T, T, T>(&f[i - 1], &g[j - 1], &g[j])
                        == Rotation::CounterClockwise
                        || rotation::<T, T, T>(&g[j], &g[j + 1], &f[i])
                            == Rotation::CounterClockwise
                    {
                        descr.g_undercuts_strictly = true;
                        h.push_point(g[j]);
                    }
                    if rotation::<T, T, T>(&f[i - 1], &g[j - 1], &g[j]) == Rotation::Clockwise
                        || rotation::<T, T, T>(&g[j], &g[j + 1], &f[i]) == Rotation::Clockwise
                    {
                        descr.g_undercuts_strictly = true;
                    }
                }
                Rotation::Clockwise => (),
            }
            j += 1;
        }
    }

    let last_y_from_other = if i < f.len() {
        g[g.len() - 1].y
    } else {
        f[f.len() - 1].y
    };
    let mut is_first = true;
    for i in i..f.len() {
        if f[i].y.approx_eq(&last_y_from_other) {
            h.push_point(f[i]);
        } else if f[i].y < last_y_from_other {
            if !is_first && f[i - 1].y > last_y_from_other {
                let p = intersection_point_horizontal(&f[i - 1], &f[i], last_y_from_other);
                h.push_point(p);
            }
            descr.f_undercuts_strictly = true;
            h.push_point(f[i]);
        } else if !is_first && f[i - 1].y < last_y_from_other {
            let p = intersection_point_horizontal(&f[i - 1], &f[i], last_y_from_other);
            descr.g_undercuts_strictly = true;
            h.push_point(p);
        }
        is_first = false;
    }
    for j in j..g.len() {
        if g[j].y.approx_eq(&last_y_from_other) {
            h.push_point(g[j]);
        } else if g[j].y < last_y_from_other {
            if !is_first && g[j - 1].y > last_y_from_other {
                let p = intersection_point_horizontal(&g[j - 1], &g[j], last_y_from_other);
                h.push_point(p);
            }
            descr.g_undercuts_strictly = true;
            h.push_point(g[j]);
        } else if !is_first && g[j - 1].y < last_y_from_other {
            let p = intersection_point_horizontal(&g[j - 1], &g[j], last_y_from_other);
            descr.f_undercuts_strictly = true;
            h.push_point(p);
        }
        is_first = false;
    }

    debug_assert!(!h.is_empty());
    let h = h.finish();
    // debug_assert!(h.dbg_check_min(f, g));
    debug_assert!(h.is_fifo());
    (h, descr)
}

pub(crate) fn merge_cst<T: TTFNum, S: Simplify>(
    f: &PwlTTF<T, S>,
    c: T,
) -> (PwlTTF<T, S>, UndercutDescriptor) {
    debug_assert!(!f.is_empty());

    let mut descr = UndercutDescriptor::default();

    if c.approx_lt(&f.get_max()) {
        descr.g_undercuts_strictly = true;
    }
    if f.get_min().approx_lt(&c) {
        descr.f_undercuts_strictly = true;
    }

    let mut h: PwlTTFBuilder<T, S> = PwlTTFBuilder::with_capacity(f.period, 2 * f.len());

    if c.approx_le(&f.get_min()) {
        h.push(h.period[0], c);
        let h = h.finish();
        debug_assert!(h.is_fifo());
        return (h, descr);
    }

    debug_assert_eq!(f[0].x, h.period[0]);
    h.push(h.period[0], f[0].y.min(c));

    for i in 1..f.len() {
        if f[i].y.approx_eq(&c) {
            if f[i - 1].y.approx_lt(&c) || (i < f.len() - 1 && f[i + 1].y.approx_lt(&c)) {
                h.push(f[i].x, c);
            }
        } else if f[i].y < c {
            if c.approx_lt(&f[i - 1].y) {
                let p = intersection_point_horizontal(&f[i - 1], &f[i], c);
                h.push_point(p);
            }
            h.push_point(f[i]);
        } else if f[i - 1].y.approx_lt(&c) {
            let p = intersection_point_horizontal(&f[i - 1], &f[i], c);
            h.push_point(p);
        }
    }

    debug_assert!(!h.is_empty());
    let h = h.finish();
    debug_assert!(h.is_fifo());
    (h, descr)
}

pub(crate) fn analyze_relative_position<T: TTFNum, S>(
    f: &PwlTTF<T, S>,
    g: &PwlTTF<T, S>,
) -> Either<Ordering, Vec<(T, Ordering)>> {
    debug_assert_eq!(f.period, g.period);

    if f.get_max().approx_le(&g.get_min()) {
        return Either::Left(Ordering::Less);
    }
    if g.get_max().approx_le(&f.get_min()) {
        return Either::Left(Ordering::Greater);
    }

    let mut results = Vec::with_capacity(f.len() + g.len());
    let mut i = 1;
    let mut j = 1;
    debug_assert_eq!(f[0].x, f.period[0]);
    debug_assert_eq!(g[0].x, g.period[0]);
    let mut rel_pos = if f[0].y.approx_eq(&g[0].y) {
        Ordering::Equal
    } else if f[0].y < g[0].y {
        Ordering::Less
    } else {
        Ordering::Greater
    };
    if rel_pos != Ordering::Equal {
        results.push((f.period[0], rel_pos));
    }

    while i < f.len() && j < g.len() {
        let mut increment_i = false;
        let mut increment_j = false;
        let old_rel_pos = rel_pos;
        if f[i].x.approx_eq(&g[j].x) {
            increment_i = true;
            increment_j = true;
            if g[j].y.approx_lt(&f[i].y) {
                rel_pos = Ordering::Greater;
            } else if f[i].y.approx_lt(&g[j].y) {
                rel_pos = Ordering::Less;
            }
        } else if f[i].x < g[j].x {
            increment_i = true;
            match rotation::<T, T, T>(&g[j - 1], &f[i], &g[j]) {
                Rotation::Clockwise => {
                    rel_pos = Ordering::Greater;
                }
                Rotation::CounterClockwise => {
                    rel_pos = Ordering::Less;
                }
                Rotation::Colinear => (),
            }
        } else {
            increment_j = true;
            match rotation::<T, T, T>(&f[i - 1], &g[j], &f[i]) {
                Rotation::Clockwise => {
                    rel_pos = Ordering::Less;
                }
                Rotation::CounterClockwise => {
                    rel_pos = Ordering::Greater;
                }
                Rotation::Colinear => (),
            }
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if f[i - 1].x.approx_eq(&g[j - 1].x) && f[i - 1].y.approx_eq(&g[j - 1].y) {
                f[i - 1].x
            } else if rotation::<T, T, T>(&g[j - 1], &f[i - 1], &g[j]) == Rotation::Colinear
                && rotation::<T, T, T>(&f[i - 1], &g[j - 1], &f[i]) == Rotation::Colinear
            {
                f[i - 1].x.max(g[j - 1].x)
            } else if rotation::<T, T, T>(&g[j - 1], &f[i - 1], &g[j]) == Rotation::Colinear {
                f[i - 1].x
            } else if rotation::<T, T, T>(&f[i - 1], &g[j - 1], &f[i]) == Rotation::Colinear {
                g[j - 1].x
            } else {
                intersection_point(&f[i - 1], &f[i], &g[j - 1], &g[j]).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }

        if increment_i {
            i += 1;
        }
        if increment_j {
            j += 1
        }
    }

    let last_y_from_other = if i < f.len() {
        g[g.len() - 1].y
    } else {
        f[f.len() - 1].y
    };
    for i in i..f.len() {
        let old_rel_pos = rel_pos;
        if f[i].y.approx_lt(&last_y_from_other) {
            rel_pos = Ordering::Less;
        } else if f[i].y.approx_gt(&last_y_from_other) {
            rel_pos = Ordering::Greater;
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if f[i - 1].x.approx_eq(&last_y_from_other) {
                f[i - 1].x
            } else {
                intersection_point_horizontal(&f[i - 1], &f[i], last_y_from_other).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            debug_assert!(results.is_empty() || results.last().unwrap().0 < x);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }
    }
    for j in j..g.len() {
        let old_rel_pos = rel_pos;
        if g[j].y.approx_lt(&last_y_from_other) {
            rel_pos = Ordering::Greater;
        } else if g[j].y.approx_gt(&last_y_from_other) {
            rel_pos = Ordering::Less;
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if g[j - 1].x.approx_eq(&last_y_from_other) {
                g[j - 1].x
            } else {
                intersection_point_horizontal(&g[j - 1], &g[j], last_y_from_other).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            debug_assert!(results.is_empty() || results.last().unwrap().0 < x);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }
    }

    if results.is_empty() {
        results.push((f.period[0], Ordering::Less));
    }

    debug_assert_eq!(results[0].0, f.period[0]);

    Either::Right(results)
}

pub(crate) fn analyze_relative_position_to_cst<T: TTFNum, S>(
    f: &PwlTTF<T, S>,
    c: T,
) -> Either<Ordering, Vec<(T, Ordering)>> {
    if f.get_max().approx_le(&c) {
        return Either::Left(Ordering::Less);
    }
    if c.approx_le(&f.get_min()) {
        return Either::Left(Ordering::Greater);
    }

    let mut results = Vec::with_capacity(2 * f.len());
    debug_assert_eq!(f[0].x, f.period[0]);
    let mut rel_pos = if f[0].y.approx_eq(&c) {
        Ordering::Equal
    } else if f[0].y < c {
        Ordering::Less
    } else {
        Ordering::Greater
    };
    if rel_pos != Ordering::Equal {
        results.push((f.period[0], rel_pos));
    }

    for i in 0..f.len() {
        let old_rel_pos = rel_pos;
        if f[i].y.approx_lt(&c) {
            rel_pos = Ordering::Less;
        } else if f[i].y.approx_gt(&c) {
            rel_pos = Ordering::Greater;
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if f[i - 1].x.approx_eq(&c) {
                f[i - 1].x
            } else {
                intersection_point_horizontal(&f[i - 1], &f[i], c).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            debug_assert!(results.is_empty() || results.last().unwrap().0 < x);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }
    }

    if results.is_empty() {
        results.push((f.period[0], Ordering::Greater));
    }

    debug_assert_eq!(results[0].0, f.period[0]);

    Either::Right(results)
}

fn segment_contains<T: TTFNum>(segment: [Point<T, T>; 2], error: T, p: &Point<T, T>) -> bool {
    // Coefficient of the segment.
    let b = (segment[1].y - segment[0].y) / (segment[1].x - segment[0].x);
    // Value of Y at origin for the segment.
    let a = segment[0].y - b * segment[0].x;
    let dist = (p.y - b * p.x - a).abs();
    dist <= error
}

pub(crate) fn apply<T: TTFNum, F: Fn(T, T) -> T, S: Simplify>(
    f: &PwlTTF<T, S>,
    g: &PwlTTF<T, S>,
    func: F,
) -> PwlTTF<T, S> {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert_eq!(f.period, g.period);

    let mut h: PwlTTFBuilder<T, S> = PwlTTFBuilder::with_capacity(f.period, f.len() + g.len());

    debug_assert_eq!(f[0].x, h.period[0]);
    debug_assert_eq!(g[0].x, h.period[0]);
    h.push(h.period[0], func(f[0].y, g[0].y));

    let mut i = 1;
    let mut j = 1;

    while i < f.len() && j < g.len() {
        if f[i].x.approx_eq(&g[j].x) {
            h.push(f[i].x, func(f[i].y, g[j].y));
            i += 1;
            j += 1;
        } else if f[i].x < g[j].x {
            h.push(f[i].x, func(f[i].y, g.eval(f[i].x)));
            i += 1;
        } else {
            h.push(g[j].x, func(f.eval(g[j].x), g[j].y));
            j += 1;
        }
    }

    let last_y_from_other = if i < f.len() {
        g[g.len() - 1].y
    } else {
        f[f.len() - 1].y
    };
    for i in i..f.len() {
        h.push(f[i].x, func(f[i].y, last_y_from_other));
    }
    for j in j..g.len() {
        h.push(g[j].x, func(last_y_from_other, g[j].y));
    }

    debug_assert!(!h.is_empty());
    let h = h.finish();
    debug_assert!(h.is_fifo());
    h
}

/// A struct to conveniently build a [PwlXYF].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PwlXYFBuilder<X, Y, T, S = Simplification> {
    /// Breakpoints representing the function.
    points: Vec<Point<X, Y>>,
    /// Minimum `y` value of the function.
    min: Option<Y>,
    /// Maximum `y` value of the function.
    max: Option<Y>,
    /// Array `[x0, x1]` representing the domain of the function.
    period: [X; 2],
    convert_type: std::marker::PhantomData<T>,
    simplification: std::marker::PhantomData<S>,
}

/// A struct to conveniently build a [PwlTTF].
pub type PwlTTFBuilder<T, S = Simplification> = PwlXYFBuilder<T, T, T, S>;

impl<X, Y, T, S> PwlXYFBuilder<X, Y, T, S> {
    /// Creates a new [PwlXYFBuilder] with no point.
    pub fn new(period: [X; 2]) -> Self {
        Self {
            points: Vec::new(),
            min: None,
            max: None,
            period,
            convert_type: std::marker::PhantomData,
            simplification: std::marker::PhantomData,
        }
    }

    /// Creates a new [PwlXYFBuilder] with no point, that can hold at least the given capacity of
    /// points.
    pub fn with_capacity(period: [X; 2], capacity: usize) -> Self {
        Self {
            points: Vec::with_capacity(capacity),
            min: None,
            max: None,
            period,
            convert_type: std::marker::PhantomData,
            simplification: std::marker::PhantomData,
        }
    }
}

impl<X, Y, T, S> PwlXYFBuilder<X, Y, T, S>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
{
    /// Returns `true` if the function is empty (there is no breakpoint).
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// Returns the number of breakpoints of the function.
    pub fn len(&self) -> usize {
        self.points.len()
    }

    fn update_min_max(&mut self, y: Y) {
        if self.min.is_none() {
            assert!(self.max.is_none());
            self.min = Some(y);
            self.max = Some(y);
        }
        if y < self.min.unwrap() {
            self.min = Some(y);
        } else if y > self.max.unwrap() {
            self.max = Some(y);
        }
    }

    /// Consumes the PwlXYFBuilder and returns a PwlXYF.
    ///
    /// *Panics* if the PwlXYFBuilder has no point.
    pub fn finish(mut self) -> PwlXYF<X, Y, T, S> {
        assert!(
            !self.is_empty(),
            "The piecewise-linear function must have at least 1 point"
        );
        debug_assert!(
            self.min.unwrap().approx_eq(
                &self
                    .points
                    .iter()
                    .min_by(|p, q| p.y.partial_cmp(&q.y).unwrap())
                    .unwrap()
                    .y
            ),
            "Minimum value is incorrect"
        );
        debug_assert!(
            self.max.unwrap().is_infinite()
                || self.max.unwrap().approx_eq(
                    &self
                        .points
                        .iter()
                        .max_by(|p, q| p.y.partial_cmp(&q.y).unwrap())
                        .unwrap()
                        .y
                ),
            "Maximum value in incorrect"
        );
        self.points.shrink_to_fit();
        let mut xyf = PwlXYF {
            points: self.points,
            min: self.min,
            max: self.max,
            period: self.period,
            buckets: Vec::with_capacity(BUCKET_SIZE),
            bucket_shift: 0,
            convert_type: self.convert_type,
            simplification: self.simplification,
        };
        xyf.setup_buckets();
        xyf
    }
}

impl<X, Y, T, S> PwlXYFBuilder<X, Y, T, S>
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T> + From<T>,
    T: TTFNum,
    S: Simplify,
{
    /// Pushes a new point (`x`, `y`) to the [PwlXYFBuilder].
    pub fn push(&mut self, x: X, y: Y) {
        self.push_point(Point { x, y });
    }

    /// Pushes a new point to the [PwlXYFBuilder].
    fn push_point(&mut self, p: Point<X, Y>) {
        debug_assert!(
            self.is_empty() || self.points.last().unwrap().x.approx_le(&p.x),
            "{:?} > {:?}",
            self.points.last().unwrap().x,
            p.x
        );
        debug_assert!(!self.is_empty() || p.x == self.period[0]);
        debug_assert!(p.x >= self.period[0]);
        debug_assert!(p.x <= self.period[1]);
        self.update_min_max(p.y);
        if let Some(last_point) = self.points.last_mut() {
            if last_point.x.approx_eq(&p.x) {
                // The point to add has the same x as the last point added.
                if last_point.y.approx_eq(&p.y) {
                    // Do not try to add the same point again.
                    return;
                }
                let new_x = last_point.x.max(p.x) + X::small_margin();
                last_point.x = last_point.x.min(p.x);
                debug_assert!(last_point.x < new_x);
                self.points.push(Point { x: new_x, y: p.y });
                return;
            }
            debug_assert!(last_point.x < p.x);
        }
        if S::simplify()
            && self.len() > 1
            && rotation(
                &self.points[self.len() - 2],
                &self.points[self.len() - 1],
                &p,
            ) == Rotation::Colinear
        {
            // The new point is colinear with the two previous points.
            // The new point replaces the last one.
            *self.points.last_mut().unwrap() = p;
            return;
        }
        debug_assert!(self.is_empty() || self.points.last().unwrap().x < p.x);
        self.points.push(p);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn piecewise_test() {
        let breakpoints = vec![(-10., 15.), (0., 20.), (10., 5.)];
        let ttf: PwlTTF<_, Simplification> = PwlTTF::from_breakpoints(breakpoints);
        assert_eq!(ttf.eval(-10.), 15.);
        assert_eq!(ttf.eval(0.), 20.);
        assert_eq!(ttf.eval(10.), 5.);
        assert_eq!(ttf.eval(-5.), 17.5);
        assert_eq!(ttf.eval(15.), 5.0);
    }

    #[test]
    #[should_panic]
    fn piecewise_panic_test1() {
        let breakpoints = vec![(-10., 5.), (0., 10.), (10., -5.)];
        let ttf: PwlTTF<_, Simplification> = PwlTTF::from_breakpoints(breakpoints);
        ttf.eval(-15.);
    }

    #[test]
    #[should_panic]
    fn piecewise_panic_test3() {
        let breakpoints = vec![(-10., 5.), (0., 10.), (10., -5.)];
        let ttf: PwlTTF<_, Simplification> = PwlTTF::from_breakpoints(breakpoints);
        ttf.eval(f64::NAN);
    }

    #[test]
    fn add_x_breakpoints_test() {
        let mut ttf: PwlTTF<_, Simplification> =
            PwlTTF::from_breakpoints(vec![(0.0, 0.0), (10.0, 10.0), (20.0, 0.0)]);
        ttf.add_x_breakpoints(vec![-5.0, 5.0, 10.0, 15.0, 20.0, 25.0]);
        let new_ttf = PwlTTF::<f64, NoSimplification>::from_breakpoints(vec![
            (0.0, 0.0),
            (5.0, 5.0),
            (10.0, 10.0),
            (15.0, 5.0),
            (20.0, 0.0),
        ])
        .with_simplification();
        assert_eq!(ttf, new_ttf);
    }

    #[test]
    fn add_z_breakpoints_test() {
        let mut ttf: PwlTTF<_, Simplification> =
            PwlTTF::from_breakpoints(vec![(0.0, 5.0), (10.0, 10.0), (20.0, 5.0)]);
        ttf.add_z_breakpoints(vec![-5.0, 0.0, 5.0, 11.0, 12.5, 20.0, 22.5, 25.0, 30.0]);
        let new_ttf = PwlTTF::<f64, NoSimplification>::from_breakpoints(vec![
            (0.0, 5.0),
            (4.0, 7.0),
            (5.0, 7.5),
            (10.0, 10.0),
            (15.0, 7.5),
            (20.0, 5.0),
        ])
        .with_simplification();
        assert_eq!(ttf, new_ttf);
    }

    #[test]
    fn constrain_to_domain_test() {
        let mut ttf: PwlTTF<_, Simplification> =
            PwlTTF::from_breakpoints(vec![(0.0, 5.0), (10.0, 10.0), (20.0, 5.0)]);
        ttf.constrain_to_domain([4.0, 16.0]);
        let new_ttf = PwlTTF::from_breakpoints(vec![(4.0, 7.0), (10.0, 10.0), (16.0, 7.0)]);
        assert_eq!(ttf, new_ttf);
    }

    #[test]
    fn constrain_to_domain2_test() {
        let mut ttf: PwlTTF<_, Simplification> =
            PwlTTF::from_breakpoints(vec![(0.0, 5.0), (10.0, 10.0), (20.0, 5.0)]);
        let new_ttf = ttf.clone();
        ttf.constrain_to_domain([-5.0, 25.0]);
        assert_eq!(ttf, new_ttf);
    }
}
