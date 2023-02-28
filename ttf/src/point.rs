// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use std::ops;

use num_traits::Num;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::TTFNum;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize, JsonSchema)]
#[serde(into = "RawPoint<X, Y>")]
#[serde(from = "RawPoint<X, Y>")]
#[serde(bound(serialize = "X: Clone + Serialize, Y: Clone + Serialize"))]
pub struct Point<X, Y> {
    pub x: X,
    pub y: Y,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "A 2-D point")]
#[schemars(description = "An array `[x, y]`.")]
pub struct RawPoint<X, Y>(X, Y);

impl<X, Y> From<RawPoint<X, Y>> for Point<X, Y> {
    fn from(p: RawPoint<X, Y>) -> Self {
        Self { x: p.0, y: p.1 }
    }
}

impl<X, Y> From<Point<X, Y>> for RawPoint<X, Y> {
    fn from(p: Point<X, Y>) -> Self {
        Self(p.x, p.y)
    }
}

impl<X: Num, Y: Num> ops::Add for Point<X, Y> {
    type Output = Point<X, Y>;

    #[inline]
    fn add(self, other: Self) -> Self {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl<T: Copy + Num> ops::Add<T> for Point<T, T> {
    type Output = Point<T, T>;

    #[inline]
    fn add(self, a: T) -> Self {
        Point {
            x: self.x + a,
            y: self.y + a,
        }
    }
}

impl<X: Num, Y: Num> ops::Sub for Point<X, Y> {
    type Output = Point<X, Y>;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Point {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

impl<T: Copy + Num> ops::Mul<T> for Point<T, T> {
    type Output = Point<T, T>;

    #[inline]
    fn mul(self, a: T) -> Self {
        Point {
            x: self.x * a,
            y: self.y * a,
        }
    }
}

#[inline]
fn approx_eq<X: TTFNum, Y: TTFNum>(p: &Point<X, Y>, q: &Point<X, Y>) -> bool {
    p.x.approx_eq(&q.x) && p.y.approx_eq(&q.y)
}

#[inline]
fn perp_dot_product<X, Y, T>(p: &Point<X, Y>, q: &Point<X, Y>) -> T
where
    X: Copy + Into<T>,
    Y: Copy + Into<T>,
    T: TTFNum,
{
    p.x.into() * q.y.into() - q.x.into() * p.y.into()
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rotation {
    Colinear,
    Clockwise,
    CounterClockwise,
}

#[inline]
pub(crate) fn rotation<X, Y, T>(a: &Point<X, Y>, b: &Point<X, Y>, c: &Point<X, Y>) -> Rotation
where
    X: TTFNum + Into<T>,
    Y: TTFNum + Into<T>,
    T: TTFNum,
{
    if approx_eq(a, b) && approx_eq(a, c) && approx_eq(b, c) {
        return Rotation::Colinear;
    }

    let v = perp_dot_product(&(*c - *a), &(*b - *a));
    if v.approx_eq(&T::zero()) {
        return Rotation::Colinear;
    }

    if v > T::zero() {
        Rotation::Clockwise
    } else {
        Rotation::CounterClockwise
    }
}

#[inline]
pub(crate) fn intersect<T: TTFNum>(
    a: &Point<T, T>,
    b: &Point<T, T>,
    p: &Point<T, T>,
    q: &Point<T, T>,
) -> bool {
    use Rotation::*;
    if rotation::<T, T, T>(a, b, p) == Colinear
        || rotation::<T, T, T>(a, b, q) == Colinear
        || rotation::<T, T, T>(p, q, a) == Colinear
        || rotation::<T, T, T>(p, q, b) == Colinear
    {
        return false;
    }

    !(rotation::<T, T, T>(a, b, p) == rotation::<T, T, T>(a, b, q)
        || rotation::<T, T, T>(p, q, a) == rotation::<T, T, T>(p, q, b))
}

#[inline]
pub(crate) fn intersection_point<T: TTFNum>(
    a: &Point<T, T>,
    b: &Point<T, T>,
    p: &Point<T, T>,
    q: &Point<T, T>,
) -> Point<T, T> {
    debug_assert_ne!(
        perp_dot_product::<T, T, T>(&(*p - *q), &(*b - *a)),
        T::zero(),
        "a: {a:?}, b: {b:?}, p: {p:?}, q: {q:?}"
    );
    *a + (*b - *a)
        * (perp_dot_product::<T, T, T>(&(*p - *q), &(*p - *a))
            / perp_dot_product::<T, T, T>(&(*p - *q), &(*b - *a)))
}

/// Returns the intersection point of the line (a, b), with `a.x < b.x`, and the horizontal line
/// given by the equation `y = c`.
#[inline]
pub(crate) fn intersection_point_horizontal<T: TTFNum>(
    a: &Point<T, T>,
    b: &Point<T, T>,
    c: T,
) -> Point<T, T> {
    if a.y.approx_eq(&c) {
        return *a;
    }
    if b.y.approx_eq(&c) {
        return *b;
    }

    debug_assert!(a.y.min(b.y).approx_lt(&c));
    debug_assert!(a.y.max(b.y).approx_gt(&c));

    if a.x.approx_eq(&b.x) {
        // a and b form a vertical line.
        return Point {
            x: a.x.average(b.x),
            y: c,
        };
    }

    let p = &Point { x: a.x, y: c };
    let q = &Point { x: b.x, y: c };

    let result = intersection_point(a, b, p, q);
    debug_assert!(c.approx_eq(&result.y));
    debug_assert!(a.y.min(b.y).approx_le(&result.y));
    debug_assert!(a.y.max(b.y).approx_ge(&result.y));
    debug_assert!(a.x.min(b.x).approx_le(&result.x));
    debug_assert!(a.x.max(b.x).approx_ge(&result.x));
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intersect_test() {
        let a: Point<f64, f64> = Point { x: 0., y: 0. };
        let b = Point { x: 1., y: 1. };
        // Parallel.
        assert!(!intersect(
            &a,
            &b,
            &Point { x: 0., y: 1. },
            &Point { x: 1., y: 2. }
        ));
        // Colinear.
        assert!(!intersect(
            &a,
            &b,
            &Point { x: 0., y: 0. },
            &Point { x: 2., y: 2. }
        ));
        // No intersection.
        assert!(!intersect(
            &a,
            &b,
            &Point { x: -0.5, y: 0.5 },
            &Point { x: 0., y: 0.5 }
        ));
        // Intersection.
        assert!(intersect(
            &a,
            &b,
            &Point { x: 0., y: 1. },
            &Point { x: 1., y: 0. }
        ));
        // Corner intersection.
        assert!(!intersect(
            &a,
            &b,
            &Point { x: 0., y: 0. },
            &Point { x: 1., y: 0. }
        ));
        assert!(!intersect(
            &a,
            &b,
            &Point { x: 1., y: 0. },
            &Point { x: 0., y: 0. }
        ));
        assert!(!intersect(
            &a,
            &b,
            &Point { x: -0.5, y: 0.5 },
            &Point { x: 0.5, y: 0.5 }
        ));
    }

    #[test]
    fn intersection_point_test() {
        let a: Point<f64, f64> = Point { x: 0., y: 0. };
        let b = Point { x: 1., y: 1. };
        assert_eq!(
            intersection_point(&a, &b, &Point { x: 0., y: 1. }, &Point { x: 1., y: 0. }),
            Point { x: 0.5, y: 0.5 }
        );
        assert_eq!(
            intersection_point(&a, &b, &Point { x: 0., y: 0. }, &Point { x: 1., y: 0. }),
            Point { x: 0., y: 0. }
        );
        assert_eq!(
            intersection_point(&a, &b, &Point { x: 1., y: 0. }, &Point { x: 0., y: 0. }),
            Point { x: 0., y: 0. }
        );
        assert_eq!(
            intersection_point(
                &a,
                &b,
                &Point { x: -0.5, y: 0.5 },
                &Point { x: 0.5, y: 0.5 }
            ),
            Point { x: 0.5, y: 0.5 }
        );
    }

    #[test]
    fn intersection_point_horizontal_test() {
        let a = Point { x: 0., y: 0. };
        let b = Point {
            x: f64::small_margin() + f64::EPSILON,
            y: 1.0 + f64::small_margin() + f64::EPSILON,
        };
        let p = intersection_point_horizontal(&a, &b, 1.0);
        assert!(
            p.x.approx_eq(&(f64::small_margin() + f64::EPSILON)),
            "{:?} != {:?}",
            p.x,
            f64::small_margin() + f64::EPSILON
        );
        assert!(p.y.approx_eq(&1.0), "{:?} != 1.0", p.y);
    }
}
