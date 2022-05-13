use super::{BreakpointFunction, EvaluableFunction};

use anyhow::{Context, Result};
use std::fmt;

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum PostStep {}

/// A step function represented as a set of breakpoints.
///
/// For any `x` value within the bounds, the `y` values is computed using `y` value of the previous
/// breakpoint.
///
/// The function is unbounded on the right and the left bound is defined by the first breakpoint.
///
/// # Example
///
/// ```
/// use breakpoint_function::{PostStepFunction, EvaluableFunction};
/// let bpf = PostStepFunction::from_breakpoints(
///     vec![(0., 10.), (10., 30.), (20., 20.)]
/// ).unwrap();
/// assert_eq!(bpf.y_at_x(5.).unwrap(), Some(10.));
/// assert_eq!(bpf.bounds(), (Some(0.), None));
/// ```
pub type PostStepFunction<X, Y> = BreakpointFunction<X, Y, PostStep>;

impl<X, Y> EvaluableFunction for PostStepFunction<X, Y>
where
    X: Copy + PartialOrd + fmt::Debug,
    Y: Copy + PartialOrd,
{
    type X = X;
    type Y = Y;
    fn y_at_x(&self, x: X) -> Result<Option<Y>> {
        match self
            .segment_at_x(x)
            .context("Failed to compute the segment where `x` lies")?
        {
            // The exact value of y is known.
            Ok(i) => Ok(Some(self.y_at_id(i))),
            // We have x_i-1 < x < x_i. We return y_i-1.
            Err(i) => {
                if i == 0 {
                    return Ok(None);
                }
                Ok(Some(self.y_at_id(i - 1)))
            }
        }
    }
    fn bounds(&self) -> (Option<X>, Option<X>) {
        // Post-step functions are unbounded on the right.
        (Some(self.x_at_id(0)), None)
    }
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum PreStep {}

/// A step function represented as a set of breakpoints.
///
/// For any `x` value within the bounds, the `y` values is computed using `y` value of the next
/// breakpoint.
///
/// The function is unbounded on the left and the right bound is defined by the last breakpoint.
///
/// # Example
///
/// ```
/// use breakpoint_function::{PreStepFunction, EvaluableFunction};
/// let bpf = PreStepFunction::from_breakpoints(
///     vec![(0., 10.), (10., 30.), (20., 20.)]
/// ).unwrap();
/// assert_eq!(bpf.y_at_x(5.).unwrap(), Some(30.));
/// assert_eq!(bpf.bounds(), (None, Some(20.)));
/// ```
pub type PreStepFunction<X, Y> = BreakpointFunction<X, Y, PreStep>;

impl<X, Y> EvaluableFunction for PreStepFunction<X, Y>
where
    X: Copy + PartialOrd + fmt::Debug,
    Y: Copy + PartialOrd,
{
    type X = X;
    type Y = Y;
    fn y_at_x(&self, x: X) -> Result<Option<Y>> {
        match self
            .segment_at_x(x)
            .context("Failed to compute the segment where `x` lies")?
        {
            // The exact value of y is known.
            Ok(i) => Ok(Some(self.y_at_id(i))),
            // We have x_i-1 < x < x_i. We return y_i-1.
            Err(i) => {
                if i == self.len() {
                    return Ok(None);
                }
                Ok(Some(self.y_at_id(i)))
            }
        }
    }
    fn bounds(&self) -> (Option<X>, Option<X>) {
        // Pre-step functions are unbounded on the left.
        (None, Some(self.x_at_id(self.len() - 1)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    fn example_breakpoints() -> Vec<(f64, f64)> {
        vec![(-10., 5.), (0., 10.), (10., -5.)]
    }

    #[test]
    fn post_step_test() {
        let bpf = PostStepFunction::from_breakpoints(example_breakpoints()).unwrap();
        assert_eq!(bpf.y_at_x(-10.).unwrap(), Some(5.));
        assert_eq!(bpf.y_at_x(0.).unwrap(), Some(10.));
        assert_eq!(bpf.y_at_x(10.).unwrap(), Some(-5.));
        assert_eq!(bpf.y_at_x(-5.).unwrap(), Some(5.));
        assert_eq!(bpf.y_at_x(-15.).unwrap(), None);
        assert_eq!(bpf.y_at_x(15.).unwrap(), Some(-5.));
        assert!(bpf.y_at_x(f64::NAN).is_err());
    }

    #[test]
    fn pre_step_test() {
        let bpf = PreStepFunction::from_breakpoints(example_breakpoints()).unwrap();
        assert_eq!(bpf.y_at_x(-10.).unwrap(), Some(5.));
        assert_eq!(bpf.y_at_x(0.).unwrap(), Some(10.));
        assert_eq!(bpf.y_at_x(10.).unwrap(), Some(-5.));
        assert_eq!(bpf.y_at_x(-5.).unwrap(), Some(10.));
        assert_eq!(bpf.y_at_x(-15.).unwrap(), Some(5.));
        assert_eq!(bpf.y_at_x(15.).unwrap(), None);
        assert!(bpf.y_at_x(f64::NAN).is_err());
    }

    #[test]
    fn partial_eq_post_test() {
        let f = PostStepFunction::from_breakpoints(vec![(0, 0), (1, 0), (2, 1)]).unwrap();
        let g = PostStepFunction::from_breakpoints(vec![(0, 0), (2, 1), (3, 1)]).unwrap();
        assert_eq!(f, g);
        let h = PostStepFunction::from_breakpoints(vec![(0, 0), (1, 0), (2, 1), (3, 2)]).unwrap();
        assert_ne!(f, h);
    }

    #[test]
    fn partial_eq_pre_test() {
        let f = PreStepFunction::from_breakpoints(vec![(0, 0), (1, 1), (2, 1)]).unwrap();
        let g = PreStepFunction::from_breakpoints(vec![(-1, 0), (0, 0), (2, 1)]).unwrap();
        assert_eq!(f, g);
        let h = PreStepFunction::from_breakpoints(vec![(0, 0), (1, 0), (2, 1), (3, 2)]).unwrap();
        assert_ne!(f, h);
    }

    #[test]
    fn partial_ord_post_test() {
        let f = PostStepFunction::from_breakpoints(vec![(0, 0), (2, 2)]).unwrap();
        let g = PostStepFunction::from_breakpoints(vec![(0, 0), (2, 1), (3, 2)]).unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Greater));
        let h = PostStepFunction::from_breakpoints(vec![(0, 0), (1, 0), (2, 1), (3, 3)]).unwrap();
        assert_eq!(f.partial_cmp(&h), None);
        let j = PostStepFunction::from_breakpoints(vec![(-1, -2), (0, -1), (2, 1)]).unwrap();
        assert_eq!(f.partial_cmp(&j), None);
    }

    #[test]
    fn partial_ord_pre_test() {
        let f = PreStepFunction::from_breakpoints(vec![(0, 0), (2, 2)]).unwrap();
        let g = PreStepFunction::from_breakpoints(vec![(0, 0), (1, 1), (2, 2)]).unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Greater));
        let h = PreStepFunction::from_breakpoints(vec![(-1, 1), (0, 0), (2, 1)]).unwrap();
        assert_eq!(f.partial_cmp(&h), None);
        let j = PreStepFunction::from_breakpoints(vec![(0, -1), (2, 1), (3, 0)]).unwrap();
        assert_eq!(f.partial_cmp(&j), None);
    }
}
