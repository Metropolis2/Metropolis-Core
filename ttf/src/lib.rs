// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Travel-time functions represented as piecewise linear functions.
#![warn(
    elided_lifetimes_in_paths,
    explicit_outlives_requirements,
    macro_use_extern_crate,
    missing_debug_implementations,
    missing_docs,
    non_ascii_idents,
    noop_method_call,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unused_crate_dependencies,
    unused_extern_crates,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications
)]

mod point;
mod pwl;
mod ttf_num;

use std::cmp::Ordering;

use either::Either;
pub use pwl::{PwlTTF, PwlXYF};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
pub use ttf_num::TTFNum;

/// Descriptor used when merging two TTFs `f` and `g`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UndercutDescriptor {
    /// If `true`, it means that there exists `x` such that `f(x) < g(x)`.
    pub f_undercuts_strictly: bool,
    /// If `true`, it means that there exists `x` such that `g(x) < f(x)`.
    pub g_undercuts_strictly: bool,
}

impl UndercutDescriptor {
    /// Reverses the role of `f` and `g` in the descriptor.
    fn reverse(mut self) -> Self {
        std::mem::swap(
            &mut self.f_undercuts_strictly,
            &mut self.g_undercuts_strictly,
        );
        self
    }
}

/// A travel-time function (TTF) that can be either constant or piecewise-linear.
///
/// If the function is piecewise-linear, it is represented using a [PwlTTF].
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[serde(untagged)]
#[schemars(title = "TTF")]
#[schemars(description = "Constant or piecewise-linear travel time function.")]
pub enum TTF<T> {
    /// A piecewise-linear travel-time function.
    Piecewise(PwlTTF<T>),
    /// A constant travel-time function.
    Constant(T),
}

impl<T: TTFNum> Default for TTF<T> {
    fn default() -> Self {
        TTF::Constant(T::zero())
    }
}

impl<T: TTFNum> TTF<T> {
    /// Returns the minimum travel time observed over the departure-time period, i.e., return `min_x
    /// f(x)`.
    pub fn get_min(&self) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.get_min(),
            Self::Constant(c) => *c,
        }
    }

    /// Returns the maximum travel time observed over the departure-time period, i.e., return `max_x
    /// f(x)`.
    pub fn get_max(&self) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.get_max(),
            Self::Constant(c) => *c,
        }
    }

    /// Returns the complexity of the TTF.
    ///
    /// - Returns 0 if the TTF is a constant.
    ///
    /// - Returns the number of breakpoints if the TTF is piecewise-linear.
    pub fn complexity(&self) -> usize {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.len(),
            Self::Constant(_) => 0,
        }
    }

    /// Returns the departure time at the middle of the departure-time period of the TTF.
    ///
    /// If the TTF is constant, the departure-time period is unknown so `None` is returned instead.
    pub fn middle_departure_time(&self) -> Option<T> {
        match self {
            Self::Piecewise(pwl_ttf) => Some(pwl_ttf.middle_x()),
            Self::Constant(_) => None,
        }
    }

    /// Returns the travel time at the given departure time.
    pub fn eval(&self, x: T) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.eval(x),
            Self::Constant(c) => *c,
        }
    }

    /// Returns the departure time `x` such that `f(x) = z`.
    ///
    /// Returns None if it is not possible to arrive at `z`.
    ///
    /// # Example
    ///
    /// ```
    /// use ttf::TTF;
    /// let ttf = TTF::Constant(1.0f64);
    /// assert_eq!(ttf.departure_time_with_arrival(3.0), Some(2.0));
    /// ```
    pub fn departure_time_with_arrival(&self, z: T) -> Option<T> {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.x_at_z(z),
            Self::Constant(c) => Some(z - *c),
        }
    }

    /// Links the TTF with another TTF.
    ///
    /// The link operation returns the TTF `h` such that `h(x) = f(x) + g(f(x))`.
    ///
    /// # Example
    ///
    /// ```
    /// use ttf::TTF;
    /// let f = TTF::Constant(1.0f64);
    /// let g = TTF::Constant(2.0f64);
    /// assert_eq!(f.link(&g), TTF::Constant(3.0));
    /// ```
    #[must_use]
    pub fn link(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => Self::Piecewise(pwl::link(f, g)),
            (Self::Piecewise(f), Self::Constant(c)) => Self::Piecewise(f.add(*c)),
            (Self::Constant(c), Self::Piecewise(g)) => Self::Piecewise(pwl::link_cst_before(g, *c)),
            (Self::Constant(a), Self::Constant(b)) => Self::Constant(*a + *b),
        }
    }

    /// Merges the TTF with another TTF.
    ///
    /// The merge operation returns the TTF `h` such that `h(x) = min(f(x), g(x))`.
    /// It also returns an [UndercutDescriptor] that describes if `f` is strictly below `g` and if
    /// `g` is strictly below `f` at some point.
    ///
    /// # Example
    ///
    /// ```
    /// use ttf::{UndercutDescriptor, TTF};
    /// let f = TTF::Constant(2.0f64);
    /// let g = TTF::Constant(1.0f64);
    /// let descr = UndercutDescriptor {
    ///     f_undercuts_strictly: false,
    ///     g_undercuts_strictly: true,
    /// };
    /// assert_eq!(f.merge(&g), (g, descr));
    /// ```
    #[must_use]
    pub fn merge(&self, other: &Self) -> (Self, UndercutDescriptor) {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => {
                let (h, descr) = pwl::merge(f, g);
                (Self::Piecewise(h), descr)
            }
            (Self::Piecewise(f), &Self::Constant(c)) => {
                let (h, descr) = pwl::merge_cst(f, c);
                let h = if h.is_cst() {
                    Self::Constant(h[0].y)
                } else {
                    Self::Piecewise(h)
                };
                (h, descr)
            }
            (&Self::Constant(c), Self::Piecewise(g)) => {
                let (h, rev_descr) = pwl::merge_cst(g, c);
                let h = if h.is_cst() {
                    Self::Constant(h[0].y)
                } else {
                    Self::Piecewise(h)
                };
                (h, rev_descr.reverse())
            }
            (&Self::Constant(a), &Self::Constant(b)) => {
                let descr = UndercutDescriptor {
                    f_undercuts_strictly: a.approx_lt(&b),
                    g_undercuts_strictly: b.approx_lt(&a),
                };
                (Self::Constant(a.min(b)), descr)
            }
        }
    }

    /// Simulates the merge operation between two TTFs `f` and `g` and check where `f` is below `g`
    /// and where `g` is below `f`.
    ///
    /// Returns either
    /// - an `Ordering` implying that `f` is always below `g` or `g` is always below `f`.
    ///
    /// - a vector of tuples `(T, Ordering)`, where a value `(t, ord)` means that, starting from
    ///   departure time `t`, the ordering between `f` and `g` is `ord`.
    ///   The vector is ordered by increasing departure times.
    pub fn analyze_relative_position(&self, other: &Self) -> Either<Ordering, Vec<(T, Ordering)>> {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => pwl::analyze_relative_position(f, g),
            (Self::Piecewise(f), &Self::Constant(c)) => pwl::analyze_relative_position_to_cst(f, c),
            (&Self::Constant(c), Self::Piecewise(g)) => {
                let mut pos = pwl::analyze_relative_position_to_cst(g, c);
                if let Either::Right(ref mut values) = pos {
                    for (_x, ord) in values.iter_mut() {
                        *ord = ord.reverse();
                    }
                }
                pos
            }
            (&Self::Constant(a), &Self::Constant(b)) => {
                let pos = if b < a {
                    Ordering::Greater
                } else {
                    Ordering::Less
                };
                Either::Left(pos)
            }
        }
    }

    /// Returns a new TTF equal to the input TTF plus a constant value.
    #[must_use]
    pub fn add(&self, c: T) -> Self {
        match self {
            Self::Piecewise(pwl_ttf) => TTF::Piecewise(pwl_ttf.add(c)),
            Self::Constant(c0) => TTF::Constant(*c0 + c),
        }
    }

    /// Reduces the number of breakpoints of the TTF, ensuring that the approximation error never
    /// exceeds a given bound.
    ///
    /// The approximation error is the difference between the `y` values of the initial TTF and the
    /// resulting TTF, for any `x`.
    pub fn approximate(&mut self, error: T) {
        if let Self::Piecewise(pwl_ttf) = self {
            pwl_ttf.approximate(error);
        }
    }

    /// Returns a new TTF by applying a given function on the `y` values of the two input TTFs.
    #[must_use]
    pub fn apply<F>(&self, other: &Self, func: F) -> Self
    where
        F: Fn(T, T) -> T,
    {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => Self::Piecewise(pwl::apply(f, g, func)),
            (Self::Piecewise(f), &Self::Constant(c)) => {
                Self::Piecewise(f.apply(|f_y| func(f_y, c)))
            }
            (&Self::Constant(c), Self::Piecewise(g)) => {
                Self::Piecewise(g.apply(|g_y| func(c, g_y)))
            }
            (&Self::Constant(a), &Self::Constant(b)) => Self::Constant(func(a, b)),
        }
    }
}

/// Description of a method to simplify a TTF.
#[derive(Copy, Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "values")]
pub enum TTFSimplification<T> {
    /// No simplification is done.
    Raw,
    /// Allow for a given error bound.
    Bound(T),
    /// Compute the values at fixed intervals.
    Interval(T),
}

impl<T> Default for TTFSimplification<T> {
    fn default() -> Self {
        TTFSimplification::Raw
    }
}

impl<T: TTFNum> TTFSimplification<T> {
    /// Applies the simplification method to a TTF.
    pub fn simplify(self, ttf: &mut TTF<T>) {
        match self {
            Self::Raw => (),
            Self::Bound(bound) => ttf.approximate(bound),
            Self::Interval(interval) => {
                if let TTF::Piecewise(ref mut pwl_ttf) = ttf {
                    let &[start, end] = pwl_ttf.period();
                    let mut xs =
                        Vec::with_capacity(((end - start) / interval).to_usize().unwrap() + 1);
                    let mut bins =
                        Vec::with_capacity(((end - start) / interval).to_usize().unwrap() + 2);
                    let mut current_time = start;
                    let half_interval = interval.average(&T::zero());
                    bins.push(start);
                    loop {
                        xs.push(current_time);
                        if current_time + half_interval < end {
                            bins.push(current_time + half_interval);
                        }
                        current_time = current_time + interval;
                        if current_time > end {
                            break;
                        }
                    }
                    bins.push(end);
                    let ys = pwl_ttf.average_y_in_intervals(&bins);
                    *pwl_ttf = PwlTTF::from_x_and_y(xs, ys);
                    pwl_ttf.ensure_fifo();
                }
            }
        }
    }
}
