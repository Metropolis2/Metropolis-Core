#![warn(clippy::all)]
#![feature(is_sorted)]

#[cfg(feature = "serde-1")]
#[macro_use]
extern crate serde_derive;

mod float;
mod piecewise_linear;
mod step;

pub use self::float::NextSmallerLarger;
pub use self::piecewise_linear::{merge, PWLFunction, UndercutDescriptor};
pub use self::step::{PostStepFunction, PreStepFunction};

use anyhow::{anyhow, Context, Result};
use itertools::Itertools;
use itertools::MinMaxResult::MinMax;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Index;

/// A set of breakpoints defining a function (e.g., a piecewise-linear function or a step
/// function).
///
/// The breakpoints have the following properties:
///
/// - There are at least 2 breakpoints.
/// - The breakpoints are ordered by (strictly) increasing X.
///
/// The supported functions are:
///
/// - [Piecewise-linear function](PWLFunction), i.e., the function is linear between any two
/// breakpoints.
/// - [Post-step function](PostStepFunction), i.e., the function is constant between any two
/// breakpoints and take the value of y at the previous breakpoint.
/// - [Pre-step function](PreStepFunction), i.e., the function is constant between any two
/// breakpoints and take the value of y at the next breakpoint.
///
/// # Example
///
/// ```
/// use breakpoint_function::{PWLFunction, PostStepFunction, PreStepFunction, EvaluableFunction};
/// let breakpoints = vec![(0., 10.), (10., 30.), (20., 20.)];
/// let bpf = PWLFunction::from_breakpoints(breakpoints.clone()).unwrap();
/// assert_eq!(bpf.y_at_x(5.).unwrap(), Some(20.));
/// let bpf = PreStepFunction::from_breakpoints(breakpoints.clone()).unwrap();
/// assert_eq!(bpf.y_at_x(5.).unwrap(), Some(30.));
/// let bpf = PostStepFunction::from_breakpoints(breakpoints.clone()).unwrap();
/// assert_eq!(bpf.y_at_x(5.).unwrap(), Some(10.));
/// ```
#[derive(Clone)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct BreakpointFunction<X, Y, Ty = ()> {
    /// Vector of breakpoints (x, y).
    breakpoints: Vec<(X, Y)>,
    /// Smallest of the Y values.
    lower_bound: Y,
    /// Largest of the Y values.
    upper_bound: Y,
    /// Indicator for the function type that the breakpoints represent.
    ty: PhantomData<Ty>,
}

impl<X: fmt::Debug, Y: fmt::Debug, Ty: fmt::Debug> fmt::Debug for BreakpointFunction<X, Y, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision();
        let mut dbg_struct = f.debug_struct("BreakpointFunction");
        if let Some(p) = precision {
            if self.len() > p {
                dbg_struct.field(
                    "breakpoints",
                    &format_args!(
                        "{:?} (Skipping {} additional values)",
                        &self.breakpoints[..p].iter(),
                        self.len() - p
                    ),
                );
            } else {
                dbg_struct.field("breakpoints", &format_args!("{:?}", &self.breakpoints));
            }
        } else {
            dbg_struct.field("breakpoints", &self.breakpoints);
        }
        dbg_struct.field("lower_bound", &format_args!("{:?}", &self.lower_bound));
        dbg_struct.field("upper_bound", &format_args!("{:?}", &self.upper_bound));
        dbg_struct.field("ty", &self.ty);
        dbg_struct.finish()
    }
}

impl<X, Y, Ty> BreakpointFunction<X, Y, Ty> {
    /// Create a new breakpoint function from a vector of breakpoints (x,y), a lower bound and an
    /// upper bound.
    ///
    /// No check is made but the following properties must be satisfied:
    ///
    /// - There are at least two breakpoints.
    /// - The x values are sorted in increasing order.
    /// - The lower_bound and upper_bound values match the minimum and maximum of the y values.
    /// - The y values can all be compared (i.e., no NAN).
    fn new_unchecked(breakpoints: Vec<(X, Y)>, lower_bound: Y, upper_bound: Y) -> Self {
        BreakpointFunction {
            breakpoints,
            lower_bound,
            upper_bound,
            ty: PhantomData,
        }
    }
}

impl<X, Y, Ty> BreakpointFunction<X, Y, Ty>
where
    X: Copy + PartialOrd + fmt::Debug,
    Y: Copy + PartialOrd + fmt::Debug,
{
    /// Create a new breakpoint function from a vector of breakpoints (x, y).
    ///
    /// Return an error if:
    ///
    /// - There are less than two breakpoints.
    /// - The x values are not sorted in increasing order.
    /// - The y values cannot be compared one another.
    pub fn from_breakpoints(breakpoints: Vec<(X, Y)>) -> Result<Self> {
        if breakpoints.len() < 2 {
            return Err(anyhow!(
                "The breakpoint function must have at least 2 breakpoints"
            ));
        }
        if !is_increasing(breakpoints.iter().map(|(x, _y)| x)) {
            let xs: Vec<_> = breakpoints.iter().map(|(x, _y)| x).collect();
            return Err(anyhow!(
                "The x values must be sorted in increasing order, got: {:?}",
                xs
            ));
        }
        let (lower_bound, upper_bound) = min_max(breakpoints.iter().map(|(_x, y)| y))
            .context("Failed to compute the lower and upper bound of the y values")?;
        Ok(BreakpointFunction::new_unchecked(
            breakpoints,
            lower_bound,
            upper_bound,
        ))
    }

    /// Create a new breakpoint function from a vector of x values and a vector of y values.
    ///
    /// Return an error if:
    ///
    /// - The two vectors do not have the same number of values.
    /// - There are less than two breakpoints.
    /// - The x values are not sorted in increasing order.
    /// - The y values cannot be compared one another.
    pub fn from_x_and_y(xs: Vec<X>, ys: Vec<Y>) -> Result<Self> {
        if xs.len() != ys.len() {
            return Err(anyhow!(
                "The vectors of x and y values must have the same length, got {} and {}",
                xs.len(),
                ys.len()
            ));
        }
        if xs.len() < 2 {
            return Err(anyhow!(
                "The breakpoint function must have at least 2 breakpoints"
            ));
        }
        if !is_increasing(xs.iter()) {
            return Err(anyhow!(
                "The x values must be sorted in increasing order, got: {:?}",
                xs
            ));
        }
        let (lower_bound, upper_bound) = min_max(ys.iter())
            .context("Failed to compute the lower and upper bound of the y values")?;
        Ok(BreakpointFunction::new_unchecked(
            xs.into_iter().zip(ys.into_iter()).collect(),
            lower_bound,
            upper_bound,
        ))
    }
}

impl<X, Y, Ty> BreakpointFunction<X, Y, Ty> {
    /// Iterate over the breakpoints.
    pub fn iter(&self) -> impl Iterator<Item = &(X, Y)> {
        self.breakpoints.iter()
    }

    /// Iterate over the x values.
    pub fn iter_x(&self) -> impl Iterator<Item = &X> {
        self.iter().map(|(x, _y)| x)
    }

    /// Iterate over the y values.
    pub fn iter_y(&self) -> impl Iterator<Item = &Y> {
        self.iter().map(|(_x, y)| y)
    }

    /// Iterate over the segments ((x_i, y_i), (x_i+1, y_i+1)).
    pub fn iter_segments(&self) -> impl Iterator<Item = (&(X, Y), &(X, Y))> {
        self.iter().zip(self.iter().skip(1))
    }

    /// Return the number of breakpoints.
    // The `is_empty` method is not needed as breakpoint functions cannot be empty.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.breakpoints.len()
    }

    /// Return a slice over the breakpoints.
    pub fn values(&self) -> &[(X, Y)] {
        &self.breakpoints
    }

    /// Return the segment ((x_i, y_i), (x_i+1, y_i+1)) at id i.
    ///
    /// **Panics** if the id is out of bounds, i.e., id > len - 2.
    fn segment_at_id(&self, id: usize) -> (&(X, Y), &(X, Y)) {
        (&self.breakpoints[id], &self.breakpoints[id + 1])
    }
}

impl<X: Copy, Y, Ty> BreakpointFunction<X, Y, Ty> {
    /// Return the value of x at the breakpoint of given id.
    ///
    /// **Panics** if the id is out of bounds, i.e., id > len - 1.
    pub fn x_at_id(&self, id: usize) -> X {
        self.breakpoints[id].0
    }

    /// Return the smallest and largest x values.
    pub fn x_bounds(&self) -> (X, X) {
        (self.breakpoints[0].0, self.breakpoints.last().unwrap().0)
    }
}

impl<X, Y: Copy, Ty> BreakpointFunction<X, Y, Ty> {
    /// Return the value of y at the breakpoint of given id.
    ///
    /// **Panics** if the id is out of bounds, i.e., id > len - 1.
    pub fn y_at_id(&self, id: usize) -> Y {
        self.breakpoints[id].1
    }

    /// Return the smallest and largest y values.
    pub fn y_bounds(&self) -> (Y, Y) {
        (self.lower_bound, self.upper_bound)
    }

    /// Return the smallest y value.
    pub fn get_lower_bound(&self) -> Y {
        self.lower_bound
    }

    /// Return the largest y value.
    pub fn get_upper_bound(&self) -> Y {
        self.upper_bound
    }
}

impl<X, Y, Ty> BreakpointFunction<X, Y, Ty>
where
    X: Copy + PartialOrd + fmt::Debug,
{
    /// Find the segment such that `x_i <= x < x_i+1`.
    ///
    /// - Return `Ok(Ok(i))` if `x_i = x`.
    /// - Return `Ok(Err(i))` if `x_i-1 < x < x_i`.
    /// - Return `Ok(Err(0))` if `x < x_0`.
    /// - Return `Ok(Err(n))` if `x > x_n-1`, where `n` is the number of breakpoints.
    /// - Return `Err(Error::InvalidTarget)` if `x` is not comparable.
    fn segment_at_x(&self, target_x: X) -> Result<std::result::Result<usize, usize>> {
        // X does not satisfies Ord so we have to use `partial_cmp`.
        // We know that the x values are comparable because they are sorted.
        // However, it can happen that the target value is not comparable (e.g., the target value
        // is a NaN).
        // If the `binary_search_by` call finds an invalid comparison, it will unwrap to
        // `Ordering::Equal` and return `Ok(i)`.
        // Then, if it returns `Ok(i)`, we simply check if the comparison was valid.
        match self
            .breakpoints
            .binary_search_by(|(x, _y)| x.partial_cmp(&target_x).unwrap_or(Ordering::Equal))
        {
            Ok(i) => {
                if self.x_at_id(i) == target_x {
                    Ok(Ok(i))
                } else {
                    Err(anyhow!(
                        "Cannot find the position of value {:?} in the vector of x values",
                        target_x
                    ))
                }
            }
            Err(i) => Ok(Err(i)),
        }
    }
}

impl<X, Y, Ty> Index<usize> for BreakpointFunction<X, Y, Ty> {
    type Output = (X, Y);
    fn index(&self, i: usize) -> &(X, Y) {
        &self.breakpoints[i]
    }
}

/// Trait for single-variable functions `X -> Y` that can be evaluated at any point `x` within some
/// bounds.
pub trait EvaluableFunction {
    type X: PartialOrd;
    type Y;
    /// Return the value of `y = f(x)` of the function `f`.
    ///
    /// Return None if `x` is out of bounds for the function `f`.
    fn y_at_x(&self, x: Self::X) -> Result<Option<Self::Y>>;
    /// Return the smallest and largest `x` values.
    ///
    /// Return None when `x` is unbounded.
    fn bounds(&self) -> (Option<Self::X>, Option<Self::X>) {
        (None, None)
    }
    /// Return `true` if the bounds of `self` encompases the bounds of `other`.
    fn contains(&self, other: &Self) -> bool {
        let (f_first_x, f_last_x) = self.bounds();
        let (g_first_x, g_last_x) = other.bounds();
        (f_first_x.is_none() || f_first_x <= g_first_x)
            && (f_last_x.is_none() || f_last_x >= g_last_x)
    }
}

impl<X, Y, Ty> BreakpointFunction<X, Y, Ty>
where
    BreakpointFunction<X, Y, Ty>: EvaluableFunction<X = X, Y = Y>,
    X: Copy + PartialEq,
    Y: Copy + PartialEq,
{
    /// Return `true` if `self` is equal to `other` for all x values in `self`, where `other` is
    /// defined.
    fn always_equal(&self, other: &Self) -> bool {
        self.iter().all(|&(f_x, f_y)| {
            if let Ok(Some(g_y)) = other.y_at_x(f_x) {
                f_y == g_y
            } else {
                // `g` is not valid at `x`.
                true
            }
        })
    }
}

impl<X, Y, Ty> BreakpointFunction<X, Y, Ty>
where
    BreakpointFunction<X, Y, Ty>: EvaluableFunction<X = X, Y = Y>,
    X: Copy + PartialOrd,
    Y: Copy + PartialOrd,
{
    /// Return `true` if `self` is smaller than `other` for all x values in `self`, where `other`
    /// is defined.
    fn always_smaller(&self, other: &Self) -> bool {
        self.iter().all(|&(f_x, f_y)| {
            if let Ok(Some(g_y)) = other.y_at_x(f_x) {
                f_y <= g_y
            } else {
                // `g` is not valid at `x`.
                true
            }
        })
    }

    /// Return `true` if `self` is greater than `other` for all x values in `self`, where `other`
    /// is defined.
    fn always_greater(&self, other: &Self) -> bool {
        self.iter().all(|&(f_x, f_y)| {
            if let Ok(Some(g_y)) = other.y_at_x(f_x) {
                f_y >= g_y
            } else {
                // `g` is not valid at `x`.
                true
            }
        })
    }
}

impl<X, Y, Ty> PartialEq for BreakpointFunction<X, Y, Ty>
where
    BreakpointFunction<X, Y, Ty>: EvaluableFunction<X = X, Y = Y>,
    X: Copy + PartialEq,
    Y: Copy + PartialEq,
{
    /// Return `true` if `self` and `other` are defined on the same bounds and are equal for all
    /// possible values of `x`.
    ///
    /// Note that this does not always imply that `self` and `other` have the same breakpoints.
    fn eq(&self, other: &Self) -> bool {
        if self.breakpoints == other.breakpoints {
            true
        } else if self.bounds() == other.bounds() && self.y_bounds() == other.y_bounds() {
            self.always_equal(other) && other.always_equal(self)
        } else {
            false
        }
    }
}

impl<X, Y, Ty> PartialOrd for BreakpointFunction<X, Y, Ty>
where
    BreakpointFunction<X, Y, Ty>: EvaluableFunction<X = X, Y = Y>,
    X: Copy + PartialOrd,
    Y: Copy + PartialOrd,
{
    /// Return an ordering between `self` and `other` if one exists.
    ///
    /// In particular:
    ///
    /// - If `self` does not contain `other` (i.e., `other` is defined for some values `x` where
    /// `self` is not), then `self` cannot be compared to `other` (the function returns `None`).
    /// - Return `Some(Ordering::Equal)` if and only if `self == other`.
    /// - Return `Some(Ordering::Less)` if and only if `self` is smaller or equal to `other` for
    /// any point where `other` is defined.
    /// - Return `Some(Ordering::Greater)` if and only if `self` is larger or equal to `other` for
    /// any point where `other` is defined.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // Check the easiest cases first.
        if !self.contains(other) {
            // g has x points where f cannot be evaluated, we cannot compare.
            None
        } else if self.upper_bound < other.lower_bound {
            // f is always below g
            Some(Ordering::Less)
        } else if self.lower_bound > other.upper_bound {
            // f is always above f
            Some(Ordering::Greater)
        } else if self == other {
            Some(Ordering::Equal)
        } else if self.always_smaller(other) && other.always_greater(self) {
            // f is point by point below g.
            Some(Ordering::Less)
        } else if other.always_smaller(self) && self.always_greater(other) {
            // f is point by point above g.
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

/// Return true if the elements in the iterator are storted in a (strictly) increasing order.
fn is_increasing<X: PartialOrd>(iter: impl Iterator<Item = X>) -> bool {
    iter.is_sorted_by(|a, b| {
        if a.partial_cmp(b) == Some(Ordering::Less) {
            Some(Ordering::Less)
        } else {
            None
        }
    })
}

/// Return the minimum and maximum value from an iterator.
///
/// Return an error if two elements in the iterator are not comparible.
///
/// **Panics** if the iterator has less than 2 elements.
fn min_max<'a, Y>(iter: impl Iterator<Item = &'a Y>) -> Result<(Y, Y)>
where
    Y: Copy + PartialOrd + fmt::Debug + 'a,
{
    // When the comparison is invalid, we always return Less so that NAN values will be returned as
    // either `min` or `max`.
    if let MinMax(&min, &max) = iter.minmax_by(|&a, &b| a.partial_cmp(b).unwrap_or(Ordering::Less))
    {
        if min.partial_cmp(&max).is_none() {
            // We cannot compare `min` with `max`, so one of them is NAN.
            Err(anyhow!(
                "Found an invalid min or max value: {:?} or {:?}",
                min,
                max
            ))
        } else {
            Ok((min, max))
        }
    } else {
        panic!("The iterator must have at least 2 elements.");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn example_bpf() -> BreakpointFunction<f64, f64> {
        let breakpoints = vec![(-10., 5.), (0., 10.), (10., -5.)];
        BreakpointFunction::from_breakpoints(breakpoints).unwrap()
    }

    #[test]
    fn from_breakpoints_test() {
        // Test valid functions.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_breakpoints(vec![(-10., 5.), (0., 10.), (10., -5.)]);
        assert!(bpf.is_ok());

        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_breakpoints(vec![(0., 5.), (5., 5.)]);
        assert!(bpf.is_ok());

        // Test invalid functions.
        // Not enough breakpoints.
        let bpf: Result<BreakpointFunction<f64, f64>> =
            BreakpointFunction::from_breakpoints(vec![]);
        assert!(bpf.is_err());

        // Not enough breakpoints.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_breakpoints(vec![(0., 0.)]);
        assert!(bpf.is_err());

        // Unsorted x.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_breakpoints(vec![(0., 0.), (0., 10.)]);
        assert!(bpf.is_err());

        // Unsorted x.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_breakpoints(vec![(0., 0.), (-0., 10.)]);
        assert!(bpf.is_err());

        // Unsorted x.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_breakpoints(vec![(0., 0.), (f64::NAN, 10.)]);
        assert!(bpf.is_err());

        // Invalid y.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_breakpoints(vec![(0., 0.), (10., f64::NAN)]);
        assert!(bpf.is_err());
    }

    #[test]
    fn from_x_and_y_test() {
        // Test valid functions.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_x_and_y(vec![-10., 0., 10.], vec![5., 10., -5.]);
        assert!(bpf.is_ok());
        assert_eq!(bpf.unwrap().y_bounds(), (-5., 10.));

        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_x_and_y(vec![0., 5.], vec![5., 5.]);
        assert!(bpf.is_ok());
        assert_eq!(bpf.unwrap().y_bounds(), (5., 5.));

        // Test invalid functions.
        // Not enough breakpoints.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_x_and_y(vec![0.], vec![0.]);
        assert!(bpf.is_err());

        // Unsorted x.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_x_and_y(vec![0., 0.], vec![0., 10.]);
        assert!(bpf.is_err());

        // Different x and y length.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_x_and_y(vec![0., 0.], vec![0., 0., 0.]);
        assert!(bpf.is_err());

        // Invalid y.
        let bpf: Result<BreakpointFunction<_, _>> =
            BreakpointFunction::from_x_and_y(vec![0., 10., 20.], vec![f64::NAN, 1., 1.]);
        assert!(bpf.is_err());

        // Valid y.
        let bpf: Result<BreakpointFunction<_, _>> = BreakpointFunction::from_x_and_y(
            vec![0., 10., 20.],
            vec![f64::INFINITY, f64::INFINITY, 1.],
        );
        assert!(bpf.is_ok());
        assert_eq!(bpf.unwrap().y_bounds(), (1., f64::INFINITY));

        // Valid y.
        let bpf: Result<BreakpointFunction<_, _>> = BreakpointFunction::from_x_and_y(
            vec![0., 10., 20.],
            vec![f64::INFINITY, 1., f64::NEG_INFINITY],
        );
        assert!(bpf.is_ok());
        assert_eq!(bpf.unwrap().y_bounds(), (f64::NEG_INFINITY, f64::INFINITY));
    }

    #[test]
    fn iter_segments_test() {
        let bpf = example_bpf();
        let mut iter = bpf.iter_segments();
        assert_eq!(iter.next(), Some((&(-10., 5.), &(0., 10.))));
        assert_eq!(iter.next(), Some((&(0., 10.), &(10., -5.))));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn x_bounds_test() {
        let bpf = example_bpf();
        assert_eq!(bpf.x_bounds(), (-10., 10.));
    }

    #[test]
    fn y_bounds_test() {
        let bpf = example_bpf();
        assert_eq!(bpf.y_bounds(), (-5., 10.));
    }

    #[test]
    fn segment_at_id_test() {
        let bpf = example_bpf();
        assert_eq!(bpf.segment_at_id(1), (&(0., 10.), &(10., -5.)));
    }

    #[test]
    fn segment_at_x_test() {
        let bpf = example_bpf();
        assert_eq!(bpf.segment_at_x(-10.).unwrap(), Ok(0));
        assert_eq!(bpf.segment_at_x(10.).unwrap(), Ok(2));
        assert_eq!(bpf.segment_at_x(-5.).unwrap(), Err(1));
        assert_eq!(bpf.segment_at_x(-15.).unwrap(), Err(0));
        assert_eq!(bpf.segment_at_x(15.).unwrap(), Err(3));
        assert!(bpf.segment_at_x(f64::NAN).is_err());
    }
}
