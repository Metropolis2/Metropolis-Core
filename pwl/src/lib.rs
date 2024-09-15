// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Travel-time functions represented as piecewise linear functions.
#![doc(html_no_source)]

mod pwl;
mod ttf_num;

use std::cmp::Ordering;

use either::Either;
use enum_as_inner::EnumAsInner;
use num_traits::ConstZero;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

pub use self::pwl::{PwlTTF, PwlXYF};
pub use self::ttf_num::TTFNum;

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

/// A function that can be either constant or piecewise-linear.
///
/// If the function is piecewise-linear, it is represented using a [PwlXYF].
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize, EnumAsInner)]
#[serde(bound(serialize = "X: Serialize, Y: Serialize"))]
#[serde(bound(deserialize = "X: TTFNum + DeserializeOwned, Y: TTFNum + DeserializeOwned"))]
pub enum XYF<X, Y, T> {
    /// A piecewise-linear function.
    Piecewise(PwlXYF<X, Y, T>),
    /// A constant function.
    Constant(Y),
}

/// A travel-time function (TTF) that can be either constant or piecewise-linear.
///
/// If the function is piecewise-linear, it is represented using a [PwlTTF].
pub type TTF<T> = XYF<T, T, T>;

impl<X, Y: ConstZero, T> Default for XYF<X, Y, T> {
    fn default() -> Self {
        XYF::Constant(Y::ZERO)
    }
}

impl<X, Y, T> XYF<X, Y, T>
where
    X: TTFNum,
    Y: TTFNum + From<T>,
    T: TTFNum + From<X> + From<Y>,
{
    /// Returns the minimum `y` value observed over the `x`-domain, i.e., return `min_x f(x)`.
    pub fn get_min(&self) -> Y {
        match self {
            Self::Piecewise(pwl_xyf) => pwl_xyf.min(),
            Self::Constant(c) => *c,
        }
    }

    /// Returns the maximum `y` value observed over the `x`-domain, i.e., return `max_x f(x)`.
    pub fn get_max(&self) -> Y {
        match self {
            Self::Piecewise(pwl_xyf) => pwl_xyf.max(),
            Self::Constant(c) => *c,
        }
    }

    /// Returns the complexity of the XYF.
    ///
    /// - Returns 0 if the XYF is a constant.
    ///
    /// - Returns the number of breakpoints if the XYF is piecewise-linear.
    pub fn complexity(&self) -> usize {
        match self {
            Self::Piecewise(pwl_xyf) => pwl_xyf.len(),
            Self::Constant(_) => 0,
        }
    }

    /// Returns the `x` value at the middle of the `x`-domain of the XYF.
    ///
    /// If the XYF is constant, the `x`-domain is unknown so `None` is returned instead.
    pub fn middle_x(&self) -> Option<X> {
        match self {
            Self::Piecewise(pwl_xyf) => Some(pwl_xyf.middle_x()),
            Self::Constant(_) => None,
        }
    }

    /// Returns the `y` value at the given `x` value.
    pub fn eval(&self, x: X) -> Y {
        match self {
            Self::Piecewise(pwl_xyf) => pwl_xyf.eval(x),
            Self::Constant(c) => *c,
        }
    }

    /// Takes an iterator of `x` values that needs to be evaluated and returns an iterator of the
    /// computed `y` values.
    pub fn iter_eval<'a>(
        &'a self,
        iter: impl Iterator<Item = X> + 'a,
    ) -> Box<dyn Iterator<Item = Y> + 'a> {
        match self {
            Self::Constant(c) => Box::new(iter.map(|_| *c)),
            Self::Piecewise(pwl_xyf) => Box::new(iter.map(|x| pwl_xyf.eval(x))),
        }
    }

    /// Returns a new XYF equal to the input XYF plus a constant value.
    #[must_use]
    pub fn add(&self, c: Y) -> Self {
        match self {
            Self::Piecewise(pwl_xyf) => XYF::Piecewise(pwl_xyf.add(c)),
            Self::Constant(c0) => XYF::Constant(*c0 + c),
        }
    }

    /// Returns a new XYF equal to the input XYF after applying a function to all the `y` values.
    #[must_use]
    pub fn map<F, W>(&self, func: F) -> XYF<X, W, T>
    where
        F: Fn(Y) -> W,
        W: TTFNum + Into<T> + From<T>,
    {
        match self {
            Self::Piecewise(pwl_xyf) => XYF::Piecewise(pwl_xyf.map(func)),
            Self::Constant(c) => XYF::Constant(func(*c)),
        }
    }
}

impl<T, U> XYF<T, T, U> {
    /// Convenient way to transform a `XYF<T, T, U, S>` in a `TTF<T, S>`.
    pub fn to_ttf(self) -> TTF<T> {
        match self {
            Self::Piecewise(pwl_xyf) => TTF::Piecewise(pwl_xyf.to_ttf()),
            Self::Constant(c) => TTF::Constant(c),
        }
    }
}

impl<T: TTFNum> TTF<T> {
    /// Links the TTF with another TTF.
    ///
    /// The link operation returns the TTF `h` such that `h(x) = f(x) + g(f(x))`.
    ///
    /// # Example
    ///
    /// ```
    /// use ttf::TTF;
    /// let f: TTF<f64> = TTF::Constant(1.0);
    /// let g: TTF<f64> = TTF::Constant(2.0);
    /// assert_eq!(f.link(&g), TTF::Constant(3.0));
    /// ```
    #[must_use]
    pub fn link(&self, other: &TTF<T>) -> Self {
        match (self, other) {
            (TTF::Piecewise(f), TTF::Piecewise(g)) => Self::Piecewise(pwl::link(f, g)),
            (TTF::Piecewise(f), TTF::Constant(c)) => Self::Piecewise(f.add(*c)),
            (TTF::Constant(c), TTF::Piecewise(g)) => Self::Piecewise(pwl::link_cst_before(g, *c)),
            (TTF::Constant(a), TTF::Constant(b)) => Self::Constant(*a + *b),
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
    /// let f: TTF<f64> = TTF::Constant(2.0);
    /// let g: TTF<f64> = TTF::Constant(1.0);
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
                    Self::Constant(h.min())
                } else {
                    Self::Piecewise(h)
                };
                (h, descr)
            }
            (&Self::Constant(c), Self::Piecewise(g)) => {
                let (h, rev_descr) = pwl::merge_cst(g, c);
                let h = if h.is_cst() {
                    Self::Constant(h.min())
                } else {
                    Self::Piecewise(h)
                };
                (h, rev_descr.reverse())
            }
            (&Self::Constant(a), &Self::Constant(b)) => {
                let descr = UndercutDescriptor {
                    f_undercuts_strictly: a < b,
                    g_undercuts_strictly: b < a,
                };
                (Self::Constant(a.min(b)), descr)
            }
        }
    }

    /// Returns the integral of the squared difference between `self` and `other`, divided by the
    /// length of the period.
    pub fn squared_difference(&self, other: &Self) -> T {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => pwl::squared_difference(f, g),
            (Self::Piecewise(f), &Self::Constant(c)) => pwl::squared_difference_cst(f, c),
            (&Self::Constant(c), Self::Piecewise(g)) => pwl::squared_difference_cst(g, c),
            (&Self::Constant(a), &Self::Constant(b)) => {
                let diff = (a - b).pow(2);
                debug_assert!(diff.is_finite(), "a: {a:?}, b: {b:?}");
                diff
            }
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
            (Self::Piecewise(f), &Self::Constant(c)) => Self::Piecewise(f.map(|f_y| func(f_y, c))),
            (&Self::Constant(c), Self::Piecewise(g)) => Self::Piecewise(g.map(|g_y| func(c, g_y))),
            (&Self::Constant(a), &Self::Constant(b)) => Self::Constant(func(a, b)),
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

    /// Modifies `self` inplace to ensure that it is a FIFO function.
    pub fn ensure_fifo(&mut self) {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.ensure_fifo(),
            Self::Constant(_) => (),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn analyze_relative_position_test() {
        let f = TTF::Constant(13.0);
        let g = TTF::Piecewise(PwlTTF::from_values(vec![10., 15., 40., 40.], 0., 30.));

        let res = f.analyze_relative_position(&g);
        let exp_res = Either::Right(vec![(0.0, Ordering::Greater), (18.0, Ordering::Less)]);
        assert_eq!(res, exp_res);

        let res = g.analyze_relative_position(&f);
        let exp_res = Either::Right(vec![(0.0, Ordering::Less), (18.0, Ordering::Greater)]);
        assert_eq!(res, exp_res);
    }
}
