use crate::TTFNum;

use num_traits::Num;
use std::ops;

#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct Point<T> {
    pub x: T,
    pub y: T,
}

impl<T: Num> ops::Add for Point<T> {
    type Output = Point<T>;

    #[inline]
    fn add(self, other: Self) -> Self {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl<T: Copy + Num> ops::Add<T> for Point<T> {
    type Output = Point<T>;

    #[inline]
    fn add(self, a: T) -> Self {
        Point {
            x: self.x + a,
            y: self.y + a,
        }
    }
}

impl<T: Num> ops::Sub for Point<T> {
    type Output = Point<T>;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Point {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

impl<T: Copy + Num> ops::Mul<T> for Point<T> {
    type Output = Point<T>;

    #[inline]
    fn mul(self, a: T) -> Self {
        Point {
            x: self.x * a,
            y: self.y * a,
        }
    }
}

#[inline]
fn approx_eq<T: TTFNum>(p: &Point<T>, q: &Point<T>) -> bool {
    p.x.approx_eq(&q.y) && p.y.approx_eq(&q.y)
}

#[inline]
fn perp_dot_product<T: TTFNum>(p: &Point<T>, q: &Point<T>) -> T {
    p.x * q.y - q.x * p.y
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Rotation {
    Colinear,
    Clockwise,
    CounterClockwise,
}

#[inline]
pub fn rotation<T: TTFNum>(a: &Point<T>, b: &Point<T>, c: &Point<T>) -> Rotation {
    if approx_eq(a, b) && approx_eq(a, c) && approx_eq(b, c) {
        return Rotation::Colinear;
    }

    let x = perp_dot_product(&(*c - *a), &(*b - *a));
    if x.approx_eq(&T::zero()) {
        return Rotation::Colinear;
    }

    if x > T::zero() {
        Rotation::Clockwise
    } else {
        Rotation::CounterClockwise
    }
}

#[inline]
pub fn intersect<T: TTFNum>(a: &Point<T>, b: &Point<T>, p: &Point<T>, q: &Point<T>) -> bool {
    use Rotation::*;
    if rotation(a, b, p) == Colinear
        || rotation(a, b, q) == Colinear
        || rotation(p, q, a) == Colinear
        || rotation(p, q, b) == Colinear
    {
        return false;
    }

    !(rotation(a, b, p) == rotation(a, b, q) || rotation(p, q, a) == rotation(p, q, b))
}

#[inline]
pub fn intersection_point<T: TTFNum>(
    a: &Point<T>,
    b: &Point<T>,
    p: &Point<T>,
    q: &Point<T>,
) -> Point<T> {
    debug_assert_ne!(perp_dot_product(&(*p - *q), &(*b - *a)), T::zero());
    *a + (*b - *a)
        * (perp_dot_product(&(*p - *q), &(*p - *a)) / perp_dot_product(&(*p - *q), &(*b - *a)))
}

/// Return the intersection point of the line (a, b), with `a.x < b.x`, and the horizontal line
/// given by the equation `y = c`.
#[inline]
pub fn intersection_point_horizontal<T: TTFNum>(a: &Point<T>, b: &Point<T>, c: T) -> Point<T> {
    debug_assert!(a.y.min(b.y).approx_le(&c));
    debug_assert!(a.y.max(b.y).approx_ge(&c));

    let p = &Point { x: a.x, y: c };
    let q = &Point { x: b.x, y: c };

    if p.x.approx_eq(&q.x) {
        // a and b form a vertical line.
        Point {
            x: p.x.average(&q.x),
            y: c,
        }
    } else {
        debug_assert!(intersect(a, b, p, q));
        let result = intersection_point(a, b, p, q);
        debug_assert!(c.approx_eq(&result.y));
        debug_assert!(a.y.min(b.y).approx_le(&result.y));
        debug_assert!(a.y.max(b.y).approx_ge(&result.y));
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intersect_test() {
        let a: Point<f64> = Point { x: 0., y: 0. };
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
        let a: Point<f64> = Point { x: 0., y: 0. };
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
}
