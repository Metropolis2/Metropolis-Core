use super::{BreakpointFunction, EvaluableFunction, NextSmallerLarger};

use anyhow::{anyhow, Context, Result};
use num_traits::Float;
use std::cmp::Ordering;
use std::fmt;

const MARGIN: f64 = 1e-4;

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum PieceWiseLinear {}

/// A piecewise-linear function represented as a set of breakpoints.
///
/// The `x` and `y` values must be of the same type.
///
/// The bounds of the function are defined by the first and last breakpoint.
///
/// For any `x` value within the bounds, the `y` values is computed using linear interpolation.
///
/// # Example
///
/// ```
/// use breakpoint_function::{PWLFunction, EvaluableFunction};
/// let bpf = PWLFunction::from_breakpoints(
///     vec![(0., 10.), (10., 30.), (20., 20.)]
/// ).unwrap();
/// assert_eq!(bpf.y_at_x(5.).unwrap(), Some(20.));
/// assert_eq!(bpf.bounds(), (Some(0.), Some(20.)));
/// ```
pub type PWLFunction<T> = BreakpointFunction<T, T, PieceWiseLinear>;

impl<T: Float> Default for PWLFunction<T> {
    fn default() -> Self {
        BreakpointFunction::new_unchecked(
            vec![(T::neg_infinity(), T::zero()), (T::infinity(), T::zero())],
            T::zero(),
            T::zero(),
        )
    }
}

impl<T> EvaluableFunction for PWLFunction<T>
where
    T: Float + fmt::Debug,
{
    type X = T;
    type Y = T;
    fn y_at_x(&self, x: T) -> Result<Option<T>> {
        match self
            .segment_at_x(x)
            .context("Failed to compute the segment where `x` lies")?
        {
            // The exact value of y is known.
            Ok(i) => Ok(Some(self.y_at_id(i))),
            // Use linear interpolation to compute the value.
            Err(i) => {
                if i == 0 || i == self.len() {
                    return Ok(None);
                }
                Ok(Some(
                    self.y_at_x_in_segment(x, i - 1)
                        .context("Failed to interpolate `y` in the segment")?,
                ))
            }
        }
    }
    fn bounds(&self) -> (Option<T>, Option<T>) {
        let (x0, x1) = self.x_bounds();
        (Some(x0), Some(x1))
    }
}

impl<T> PWLFunction<T>
where
    T: Float + fmt::Debug,
{
    /// Compute the value of `y` at the given `x` value given the id `i` such that
    /// `x_i <= x <= x_i+1`.
    ///
    /// No additional check is done to verify that `x_i <= x <= x_i+1`.
    ///
    /// **Panics** if `id > len - 2`.
    fn y_at_x_in_segment(&self, x: T, id: usize) -> Result<T> {
        let (&(x0, y0), &(x1, y1)) = self.segment_at_id(id);
        lin_interp(x, ((x0, y0), (x1, y1)))
    }

    /// Compute the value of `x` at the given `z = x + y` value given an id `i` such that
    /// `z_i <= z <= z_i+1`.
    ///
    /// No additional check is done to verify that `z_i <= z <= z_i+1`.
    ///
    /// **Panics** if `id > len - 2`.
    fn x_at_z_in_segment(&self, z: T, id: usize) -> Result<T> {
        let (&(x0, y0), &(x1, y1)) = self.segment_at_id(id);
        if y0 == y1 {
            return Ok(z - y0);
        }
        let (z0, z1) = (x0 + y0, x1 + y1);
        lin_interp(z, ((z0, x0), (z1, x1)))
    }
}

impl<T> PWLFunction<T>
where
    T: Float + NextSmallerLarger + fmt::Debug,
{
    /// Link operation between two piecewise-linear functions.
    ///
    /// Given two functions `f` and `g`, the link operation returns the function `h(x) = f(x) +
    /// g(x + f(x))`.
    ///
    /// Return `None` if the link operation is invalid, i.e., `f` ends before `g` starts or `g`
    /// ends before `f` starts.
    ///
    /// Return an error if `f` or `g` do not satisfy the FIFO property (first-in, first-out), i.e.,
    /// if the `x + f(x)` and `x + g(x)` values are not ordered in non-decreasing order.
    ///
    /// # Example
    ///
    /// ```
    /// use breakpoint_function::PWLFunction;
    /// let f = PWLFunction::from_breakpoints(
    ///     vec![(0., 10.), (10., 30.)]
    /// ).unwrap();
    /// let g = PWLFunction::from_breakpoints(
    ///     vec![(10., 20.), (25., 10.), (40., 10.)]
    /// ).unwrap();
    /// let h = PWLFunction::from_breakpoints(
    ///     vec![(0., 30.), (5., 30.), (10., 40.)]
    /// ).unwrap();
    /// assert_eq!(f.link(&g).unwrap(), Some(h));
    /// ```
    pub fn link(&self, other: &Self) -> Result<Option<Self>> {
        // In the following, we denote `self` by `f` and `other` by `g`.
        let (f_first_x, f_last_x) = self.x_bounds();
        let (f_first_y, f_last_y) = (self.y_at_id(0), self.y_at_id(self.len() - 1));
        // Let z = x + y.
        let (f_first_z, f_last_z) = (f_first_x + f_first_y, f_last_x + f_last_y);
        let (g_first_x, g_last_x) = other.x_bounds();
        if g_last_x < f_first_z || f_last_z < g_first_x {
            // The two functions have incompatible bounds.
            return Ok(None);
        }
        let mut breakpoints: Vec<(T, T)> = Vec::with_capacity(self.len() + other.len());
        let mut lb = T::infinity();
        let mut ub = T::neg_infinity();
        let mut f_iter = self.iter().enumerate().peekable();
        let mut g_iter = other.iter().enumerate().peekable();
        // Skip the first breakpoints of f such that `x + f(x) < g_first_x`
        while let Some(&(_, &(f_x, f_y))) = f_iter.peek() {
            if f_x + f_y < g_first_x {
                f_iter.next();
            } else {
                break;
            }
        }
        // Skip the first breakpoints of g such that `x < f_first_z`.
        while let Some(&(_, &(g_x, _))) = g_iter.peek() {
            if g_x < f_first_z {
                g_iter.next();
            } else {
                break;
            }
        }
        let mut prev_f_z = f_first_z;
        while let (Some(&(f_id, &(f_x, f_y))), Some(&(g_id, &(g_x, g_y)))) =
            (f_iter.peek(), g_iter.peek())
        {
            let f_z = f_x + f_y;
            // Check that `f` satisfies the FIFO property.
            if f_z < prev_f_z {
                return Err(anyhow!(
                    "The first PWL function does not respected the FIFO property near id {}",
                    f_id
                ));
            }
            prev_f_z = f_z;
            let (x, y) = if (f_z - g_x).abs() < T::from(MARGIN).unwrap() {
                f_iter.next();
                g_iter.next();
                (f_x, f_y + g_y)
            } else {
                match f_z.partial_cmp(&g_x) {
                    Some(Ordering::Less) => {
                        // f_z is such that `g_x at g_id - 1 < f_z < g_x at g_id`
                        let y = f_y
                            + other.y_at_x_in_segment(f_z, g_id - 1).with_context(|| {
                                format!("Failed to interpolate {:?} at segment {}", f_z, g_id - 1)
                            })?;
                        f_iter.next();
                        (f_x, y)
                    }
                    Some(Ordering::Greater) => {
                        let x = self.x_at_z_in_segment(g_x, f_id - 1).with_context(|| {
                            format!("Failed to interpolate {:?} at segment {}", g_x, f_id - 1)
                        })?;
                        // x + y = g_x + g_y so y = g_x + g_y - x.
                        let y = g_x - x + g_y;
                        g_iter.next();
                        (x, y)
                    }
                    Some(Ordering::Equal) => unreachable!(),
                    None => {
                        return Err(anyhow!("Cannot compare {:?} with {:?}", f_z, g_x));
                    }
                }
            };
            if let Some(&(last_x, last_y)) = breakpoints.last() {
                if x <= last_x {
                    // Force the x values to be in increasing order (this is not always the case
                    // because of rounding errors).
                    continue;
                }
                if x + y < last_x + last_y {
                    // `h` does not satisfy the FIFO property.
                    // We detected that `f` satisfies FIFO so this is possible only because `g`
                    // does not satisfy FIFO.
                    return Err(anyhow!(
                        "The second PWL function does not respected the FIFO property near id {}",
                        g_id
                    ));
                }
            }
            push_point(&mut breakpoints, (x, y), &mut lb, &mut ub);
        }
        if breakpoints.len() < 2 {
            return Ok(None);
        }
        Ok(Some(PWLFunction::new_unchecked(breakpoints, lb, ub)))
    }
}

fn lin_interp<T: Float + fmt::Debug>(x: T, ((x0, y0), (x1, y1)): ((T, T), (T, T))) -> Result<T> {
    if y0 == y1 {
        return Ok(y0);
    }
    let alpha = (x - x0) / (x1 - x0);
    let y = alpha * y1 + (T::one() - alpha) * y0;
    if y.is_finite() {
        debug_assert!(
            (T::zero()..=T::one()).contains(&alpha),
            "Invalid linear interpolation: `{:?}` at `{:?}`",
            x,
            ((x0, y0), (x1, y1))
        );
        Ok(y)
    } else {
        Err(anyhow!(
            "Cannot compute the linear interpolation of {:?} on the segment defined by (({:?}, {:?}) and ({:?}, {:?}))",
            x,
            x0,
            y0,
            x1,
            y1
        ))
    }
}

impl<T> PWLFunction<T>
where
    T: Float + NextSmallerLarger + fmt::Debug,
{
    /// Merge operation between two piecewise-linear functions.
    ///
    /// Given two functions `f` and `g`, the merge operation returns the function
    /// `h(x) = min{f(x), g(x)}`.
    ///
    /// The return type is a tuple with the [PWLFunction] resulting from the merge operation and a
    /// provenance function.
    /// The provenance function is a vector of ordered tuples `(x_i, [Ordering])` indicating
    /// whether `self` was below, above or equal to `other` in the interval `[x_i, x_i+1)`.
    ///
    /// # Example
    ///
    /// ```
    /// use breakpoint_function::PWLFunction;
    /// use std::cmp::Ordering;
    /// let f = PWLFunction::from_breakpoints(
    ///     vec![(0., 0.), (1., 1.)]
    /// ).unwrap();
    /// let g = PWLFunction::from_breakpoints(
    ///     vec![(0., 1.), (1., 0.)]
    /// ).unwrap();
    /// let h = PWLFunction::from_breakpoints(
    ///     vec![(0., 0.), (0.5, 0.5), (1., 0.)]
    /// ).unwrap();
    /// assert_eq!(
    ///     f.merge(&g).unwrap(),
    ///     (h, vec![(0., Ordering::Less), (0.5, Ordering::Greater)])
    /// );
    /// ```
    pub fn merge(&self, other: &Self) -> Result<(Self, Vec<(T, Ordering)>)> {
        // Easy cases: f < g, g < f or f == g.
        // TODO: For the easy cases, the provenance is not correct for sections where f and g are
        // equal.
        // TODO: Get inspiration from
        // https://github.com/GVeitBatz/KaTCH/blob/70b18ad0791a687c554fbfe9039edf79bc3a8ff3/datastr/base/pwl_ttf.h
        // In particular, we can simplify the merge if one of the function is constant + the merge
        // of functions with large x diff would now work.
        let (f_first_x, f_last_x) = self.x_bounds();
        let (g_first_x, g_last_x) = other.x_bounds();
        if f_last_x < g_first_x {
            // g starts after f ends.
            return Err(anyhow!(
                "The x-bounds do not overlap: {:?} < {:?}",
                f_last_x,
                g_first_x
            ));
        }
        if g_last_x < f_first_x {
            // f starts after g ends.
            return Err(anyhow!(
                "The x-bounds do not overlap: {:?} < {:?}",
                g_last_x,
                f_first_x
            ));
        }
        if self.contains(other) && self.upper_bound < other.lower_bound {
            let pf = vec![(self.breakpoints[0].0, Ordering::Less)];
            return Ok((self.clone(), pf));
        } else if other.contains(self) && other.upper_bound < self.lower_bound {
            let pf = vec![(other.breakpoints[0].0, Ordering::Greater)];
            return Ok((other.clone(), pf));
        } else if self.lower_bound == other.upper_bound && self.upper_bound == other.lower_bound {
            let first_x = if f_first_x < g_first_x {
                f_first_x
            } else {
                g_first_x
            };
            let last_x = if f_last_x < g_last_x {
                f_last_x
            } else {
                g_last_x
            };
            let pf = vec![(first_x, Ordering::Equal)];
            let breakpoints = vec![(first_x, self.lower_bound), (last_x, self.lower_bound)];
            return Ok((
                Self::new_unchecked(breakpoints, self.lower_bound, self.lower_bound),
                pf,
            ));
        }

        // match self.partial_cmp(other) {
        // Some(Ordering::Less) => {
        // // f is below g and "covers" g.
        // let pf = vec![(self.breakpoints[0].0, Ordering::Less)];
        // assert_eq!(res.unwrap(), (self.clone(), pf.clone()));
        // return Ok((self.clone(), pf));
        // }
        // Some(Ordering::Greater) => {
        // // g is below f but g does not necessarily "covers" f.
        // if other.contains(self) {
        // let pf = vec![(other.breakpoints[0].0, Ordering::Greater)];
        // assert_eq!(res.unwrap(), (other.clone(), pf.clone()));
        // return Ok((other.clone(), pf));
        // }
        // }
        // Some(Ordering::Equal) => {
        // let pf = vec![(self.breakpoints[0].0, Ordering::Equal)];
        // assert_eq!(res.unwrap(), (self.clone(), pf.clone()));
        // return Ok((self.clone(), pf));
        // }
        // None => {
        // // It is still possible that g is below f, with g "covering" f.
        // if !self.contains(other)
        // && other.contains(self)
        // && self.always_greater(other)
        // && other.always_smaller(self)
        // {
        // let pf = vec![(other.breakpoints[0].0, Ordering::Greater)];
        // assert_eq!(res.unwrap(), (other.clone(), pf.clone()));
        // return Ok((other.clone(), pf));
        // }
        // }
        // }
        self.merge_impl(other)
    }

    /// Actual merge of `self` and `other`.
    fn merge_impl(&self, other: &Self) -> Result<(Self, Vec<(T, Ordering)>)> {
        let mut breakpoints = Vec::with_capacity(self.len() + other.len());
        let mut provenances = Vec::with_capacity(self.len() + other.len());
        let (f_first_x, f_last_x) = self.x_bounds();
        let (g_first_x, g_last_x) = other.x_bounds();
        if f_last_x < g_first_x {
            // g starts after f ends.
            return Err(anyhow!(
                "The x-bounds do not overlap: {:?} < {:?}",
                f_last_x,
                g_first_x
            ));
        }
        if g_last_x < f_first_x {
            // f starts after g ends.
            return Err(anyhow!(
                "The x-bounds do not overlap: {:?} < {:?}",
                g_last_x,
                f_first_x
            ));
        }
        let mut lb = self.lower_bound.min(other.lower_bound);
        let mut ub = T::neg_infinity();
        let mut f_iter = self.iter().enumerate().peekable();
        let mut g_iter = other.iter().enumerate().peekable();
        match f_first_x.partial_cmp(&g_first_x) {
            Some(Ordering::Less) => {
                // Case where f starts before g.
                provenances.push((f_first_x, Ordering::Less));
                let next_f_id = add_breakpoints_before(&mut breakpoints, &mut f_iter, g_first_x)
                    .context("Failed to add the breakpoints from f before g starts")?;
                let g_first_y = other.y_at_id(0);
                let f_y_at_g_first_x = self
                    .y_at_x_in_segment(g_first_x, next_f_id - 1)
                    .context("Failed to compute the y value of f when g starts")?;
                handle_discontinuity_before(
                    &mut breakpoints,
                    &mut provenances,
                    g_first_x,
                    f_y_at_g_first_x,
                    g_first_y,
                )
                .context("Failed to handle the discontinuity as g starts after f")?;
                // Skip the first point of g because it has already been handled.
                g_iter.next();
            }
            Some(Ordering::Greater) => {
                // Case where g starts before f.
                provenances.push((g_first_x, Ordering::Greater));
                let next_g_id = add_breakpoints_before(&mut breakpoints, &mut g_iter, f_first_x)
                    .context("Failed to add the breakpoints from g before f starts")?;
                let f_first_y = self.y_at_id(0);
                let g_y_at_f_first_x = other
                    .y_at_x_in_segment(f_first_x, next_g_id - 1)
                    .context("Failed to compute the y value of g when f starts")?;
                handle_discontinuity_before(
                    &mut breakpoints,
                    &mut provenances,
                    f_first_x,
                    g_y_at_f_first_x,
                    f_first_y,
                )
                .context("Failed to handle the discontinuity as f starts after g")?;
                // Skip the first point of g because it has already been handled.
                f_iter.next();
            }
            // f and g start at the same time.
            Some(Ordering::Equal) => (),
            None => {
                return Err(anyhow!(
                    "Cannot compare {:?} with {:?}",
                    f_first_x,
                    g_first_x
                ));
            }
        }
        // Main loop.
        // At this point, f and g are both at the second element (at least), unless they both start at
        // the same time (in which case, they are both at the first element).
        while let (Some(&(f_id, &(f_x, f_y))), Some(&(g_id, &(g_x, g_y)))) =
            (f_iter.peek(), g_iter.peek())
        {
            // Previous ordering between f and g.
            let prev_ord = provenances
                .last()
                .map(|&(_, o)| o)
                .unwrap_or(Ordering::Equal);
            let res = match f_x.partial_cmp(&g_x) {
                Some(Ordering::Less) => {
                    // g_id cannot be 0 at this point
                    let g_y_eq = other.y_at_x_in_segment(f_x, g_id - 1).with_context(|| {
                        format!(
                            "Failed to interpolate {:?} at segment {} of g",
                            f_x,
                            g_id - 1
                        )
                    })?;
                    f_iter.next();
                    handle_next_point(f_y, g_y_eq, Ordering::Less, prev_ord).with_context(|| {
                        format!("Failed to handle next point (coming from f at id {})", f_id)
                    })?
                }
                Some(Ordering::Greater) => {
                    // f_id cannot be 0 at this point
                    let f_y_eq = self.y_at_x_in_segment(g_x, f_id - 1).with_context(|| {
                        format!(
                            "Failed to interpolate {:?} at segment {} of g",
                            g_x,
                            f_id - 1
                        )
                    })?;
                    g_iter.next();
                    handle_next_point(f_y_eq, g_y, Ordering::Greater, prev_ord).with_context(
                        || format!("Failed to handle next point (coming from g at id {})", g_id),
                    )?
                }
                Some(Ordering::Equal) => {
                    f_iter.next();
                    g_iter.next();
                    handle_next_point(f_y, g_y, Ordering::Equal, prev_ord).with_context(|| {
                        format!(
                            "Failed to handle next point (coming from f at id {} and g at id {})",
                            f_id, g_id
                        )
                    })?
                }
                None => {
                    return Err(anyhow!("Cannot compare {:?} with {:?}", f_x, g_x));
                }
            };
            if res.add_intersection {
                // Add the intersection point between the last segment of f and g.
                let (&f_p0, &f_p1) = self.segment_at_id(f_id - 1);
                let (&g_p0, &g_p1) = other.segment_at_id(g_id - 1);
                let (x, _y) = segment_intersection((f_p0, f_p1), (g_p0, g_p1))?;
                let y = T::min(
                    self.y_at_x_in_segment(x, f_id - 1)?,
                    other.y_at_x_in_segment(x, g_id - 1)?,
                );
                let last_x = breakpoints.last().unwrap().0;
                if x == last_x {
                    // Because of rounding errors with floats, the x value of the intersection
                    // matches the previous x value.
                    // We take the next x value.
                    let next_x = x.next_larger();
                    if (res.add_f_point && next_x < f_x) || (res.add_g_point && next_x < g_x) {
                        let next_y = Float::min(
                            self.y_at_x_in_segment(next_x, f_id - 1).with_context(|| {
                                format!(
                                    "Failed to interpolate {:?} at segment {} of f",
                                    next_x,
                                    f_id - 1
                                )
                            })?,
                            other.y_at_x_in_segment(next_x, g_id - 1).with_context(|| {
                                format!(
                                    "Failed to interpolate {:?} at segment {} of g",
                                    next_x,
                                    g_id - 1
                                )
                            })?,
                        );
                        push_point(&mut breakpoints, (next_x, next_y), &mut lb, &mut ub);
                    }
                    provenances.push((next_x, prev_ord.reverse()));
                } else if (res.add_f_point && x == f_x) || (res.add_g_point && x == g_x) {
                    // Because of rounding errors with floats, the x value of the intersection
                    // matches the next x value that will be added.
                    // We take the previous x value.
                    let prev_x = x.next_smaller();
                    if prev_x > last_x {
                        let prev_y = Float::min(
                            self.y_at_x_in_segment(prev_x, f_id - 1).with_context(|| {
                                format!(
                                    "Failed to interpolate {:?} at segment {} of f",
                                    prev_x,
                                    f_id - 1
                                )
                            })?,
                            other.y_at_x_in_segment(prev_x, g_id - 1).with_context(|| {
                                format!(
                                    "Failed to interpolate {:?} at segment {} of g",
                                    prev_x,
                                    g_id - 1
                                )
                            })?,
                        );
                        push_point(&mut breakpoints, (prev_x, prev_y), &mut lb, &mut ub);
                        provenances.push((prev_x, prev_ord.reverse()));
                    } else {
                        provenances.push((x, prev_ord.reverse()));
                    }
                } else {
                    debug_assert!(x > last_x);
                    push_point(&mut breakpoints, (x, y), &mut lb, &mut ub);
                    // Reverse the provenance.
                    provenances.push((x, prev_ord.reverse()));
                }
            }
            if res.add_f_point {
                // Handle the provenance if it was Equal or it is Equal now (the case Greater ->
                // Less has already been handled with the intersection).
                if provenances.is_empty() {
                    let ord = if res.is_equal {
                        Ordering::Equal
                    } else {
                        Ordering::Less
                    };
                    provenances.push((f_x, ord));
                } else if !res.is_equal && prev_ord == Ordering::Equal {
                    let last_x = breakpoints.last().unwrap().0;
                    match provenances.last() {
                        Some((x, _)) if *x == last_x => {
                            // The equality was in fact an intersection.
                            provenances.last_mut().unwrap().1 = Ordering::Less;
                        }
                        Some(_) => {
                            // The two functions were equal but they diverged at `last_x`.
                            provenances.push((last_x, Ordering::Less));
                        }
                        None => unreachable!(),
                    }
                } else if res.is_equal && prev_ord != Ordering::Equal {
                    provenances.push((f_x, Ordering::Equal));
                }
                push_point(&mut breakpoints, (f_x, f_y), &mut lb, &mut ub);
            }
            if res.add_g_point {
                // Handle the provenance if it was Equal or it is Equal now (the case Less ->
                // Greater has already been handled with the intersection).
                if provenances.is_empty() {
                    // The case where f = g is not possible here.
                    provenances.push((g_x, Ordering::Greater));
                } else if !res.is_equal && prev_ord == Ordering::Equal {
                    let last_x = breakpoints.last().unwrap().0;
                    match provenances.last() {
                        Some((x, _)) if *x == last_x => {
                            // The equality was in fact an intersection.
                            provenances.last_mut().unwrap().1 = Ordering::Greater;
                        }
                        Some(_) => {
                            // The two functions were equal but they diverged at `last_x`.
                            provenances.push((last_x, Ordering::Greater));
                        }
                        None => unreachable!(),
                    }
                } else if res.is_equal && prev_ord != Ordering::Equal {
                    provenances.push((g_x, Ordering::Equal));
                }
                push_point(&mut breakpoints, (g_x, g_y), &mut lb, &mut ub);
            }
        }
        if let Some(&(f_id, &(f_x, _))) = f_iter.peek() {
            if let Some(x_after) =
                handle_discontinuity_after(&breakpoints, &mut provenances, f_x, Ordering::Less)
            {
                push_point(
                    &mut breakpoints,
                    (
                        x_after,
                        self.y_at_x_in_segment(x_after, f_id - 1).with_context(|| {
                            format!(
                                "Failed to interpolate {:?} at segment {} for f",
                                x_after,
                                f_id - 1
                            )
                        })?,
                    ),
                    &mut lb,
                    &mut ub,
                );
            }
            add_breakpoints_after(&mut breakpoints, f_iter.map(|(_, (x, y))| (x, y)));
        } else if let Some(&(g_id, &(g_x, _))) = g_iter.peek() {
            if let Some(x_after) =
                handle_discontinuity_after(&breakpoints, &mut provenances, g_x, Ordering::Greater)
            {
                push_point(
                    &mut breakpoints,
                    (
                        x_after,
                        other
                            .y_at_x_in_segment(x_after, g_id - 1)
                            .with_context(|| {
                                format!(
                                    "Failed to interpolate {:?} at segment {} for g",
                                    x_after,
                                    g_id - 1
                                )
                            })?,
                    ),
                    &mut lb,
                    &mut ub,
                );
            }
            add_breakpoints_after(&mut breakpoints, g_iter.map(|(_, (x, y))| (x, y)));
        }
        breakpoints.shrink_to_fit();
        provenances.shrink_to_fit();
        assert!(breakpoints.len() >= 2);
        let bpf = PWLFunction::new_unchecked(breakpoints, lb, ub);
        debug_assert!(bpf
            .iter()
            .all(|&(x, y)| self.y_at_x(x).unwrap().unwrap_or(y) >= y
                && other.y_at_x(x).unwrap().unwrap_or(y) >= y));
        Ok((bpf, provenances))
    }
}

/// Add all breakpoints from the iterator until `x_limit` is reached and return the smallest id
/// where `x` >= `x_limit`.
///
/// The iterator is move to the point where the next `x` is larger or equal to `x_limit`.
///
/// - `breakpoints`: mutable reference to the breakpoints from the merge operation.
/// - `iter`: Peekable iterator over the `x` and `y` values of `f`.
/// - `x_limit`: `x` value when `g` starts.
fn add_breakpoints_before<'a, T: Float + fmt::Debug + 'a>(
    breakpoints: &mut Vec<(T, T)>,
    iter: &mut std::iter::Peekable<std::iter::Enumerate<impl Iterator<Item = &'a (T, T)>>>,
    x_limit: T,
) -> Result<usize> {
    while let Some(&(i, &(x, y))) = iter.peek() {
        match x.partial_cmp(&x_limit) {
            Some(Ordering::Less) => {
                breakpoints.push((x, y));
                iter.next();
            }
            Some(Ordering::Equal) => {
                iter.next();
                return Ok(i);
            }
            Some(Ordering::Greater) => {
                return Ok(i);
            }
            None => {
                return Err(anyhow!("Cannot compare {:?} and {:?}", x, x_limit));
            }
        }
    }
    unreachable!()
}

/// When `f` starts before `g`, check if there is a discontinuity when `g` starts.
/// If there is a discontinuity, add the necessary points.
///
/// - `breakpoints`: mutable reference to the breakpoints from the merge operation.
/// - `provenannces`: mutable reference to the vector of provenances from the merge operation.
/// - `x_limit`: `x` value when `g` starts.
/// - `f_y_at_limit`: `y` value of `f` at `x_limit`.
/// - `g_y_at_limit`: `y` value of `g` at `x_limit`.
fn handle_discontinuity_before<T: Float + NextSmallerLarger + fmt::Debug>(
    breakpoints: &mut Vec<(T, T)>,
    provenances: &mut Vec<(T, Ordering)>,
    x_limit: T,
    f_y_at_limit: T,
    g_y_at_limit: T,
) -> Result<()> {
    match f_y_at_limit.partial_cmp(&g_y_at_limit) {
        // When g starts, g is above f.
        // The first point of g can be skipped.
        Some(Ordering::Less) => (),
        Some(Ordering::Greater) => {
            // When g starts, g is below f.
            // There is a discontinuity.
            let x_before = x_limit.next_smaller();
            debug_assert!(x_before < x_limit);
            // Add the point just before the discontinuity (if needed).
            if x_before > breakpoints.last().unwrap().0 {
                breakpoints.push((x_before, f_y_at_limit));
            }
            // Add the point just after the discontinuity.
            breakpoints.push((x_limit, g_y_at_limit));
            let new_ord = provenances.last().unwrap().1.reverse();
            provenances.push((x_limit, new_ord));
        }
        Some(Ordering::Equal) => {
            // When g starts, f and g are equal.
            // Add the starting point.
            breakpoints.push((x_limit, f_y_at_limit));
            provenances.push((x_limit, Ordering::Equal));
        }
        None => {
            return Err(anyhow!(
                "Cannot compare {:?} and {:?}",
                f_y_at_limit,
                g_y_at_limit
            ));
        }
    }
    Ok(())
}

/// When `g` ends before `f`, check if there is a discontinuity when `g` ends.
///
/// Return `Some(x)` if there is a discontinuity, where `x` is the point just after the
/// discontinuity.
///
/// - `breakpoints`: slice of the breakpoints from the merge operation.
/// - `provenannces`: mutable reference to the vector of provenances from the merge operation.
/// - `next_x`: next `x` value for `f`.
/// - `next_ord`: Ordering between the two merge functions after the discontinuity.
fn handle_discontinuity_after<T: Float + NextSmallerLarger + fmt::Debug>(
    breakpoints: &[(T, T)],
    provenances: &mut Vec<(T, Ordering)>,
    next_x: T,
    next_ord: Ordering,
) -> Option<T> {
    let prev_ord = provenances.last().unwrap().1;
    if prev_ord != next_ord.reverse() {
        // No discontinuity.
        if prev_ord == Ordering::Equal {
            // The provenance must be adjusted.
            provenances.last_mut().unwrap().1 = next_ord;
        }
        return None;
    }
    let last_x = breakpoints.last().unwrap().0;
    let x_after = last_x.next_larger();
    debug_assert!(x_after > last_x);
    // Add the point just after the discontinuity (if needed).
    if x_after < next_x {
        provenances.push((x_after, next_ord));
        Some(x_after)
    } else {
        provenances.push((next_x, next_ord));
        None
    }
}

/// Add all breakpoints from the iterator until it is empty.
fn add_breakpoints_after<'a, T: Float + fmt::Debug + 'a>(
    breakpoints: &mut Vec<(T, T)>,
    iter: impl Iterator<Item = (&'a T, &'a T)>,
) {
    for (&x, &y) in iter {
        breakpoints.push((x, y));
    }
}

/// Struct representing the results for the function [handle_next_point].
struct NextPointResults {
    /// The next point for function `f` must be added.
    add_f_point: bool,
    /// The next point for function `g` must be added.
    add_g_point: bool,
    /// The intersection point between `f` and `g` must be added.
    add_intersection: bool,
    /// `f` and `g` are equal at the current point.
    is_equal: bool,
}

/// Compare the two next points of `f` and `g` in a merge operation.
///
/// - `f_y`: `y` value of `f` for the next point.
/// - `g_y`: `y` value of `g` for the next point.
/// - `x_ord`: Ordering between the next `x` value of `f` and `g`.
/// - `prev_ord`: `y` Ordering between `f` and `g` at the last breakpoint.
fn handle_next_point<T: PartialOrd + fmt::Debug>(
    f_y: T,
    g_y: T,
    x_ord: Ordering,
    prev_ord: Ordering,
) -> Result<NextPointResults> {
    // Current ordering between f and g.
    let new_ord = if let Some(ord) = f_y.partial_cmp(&g_y) {
        ord
    } else {
        return Err(anyhow!("Cannot compare {:?} and {:?}", f_y, g_y));
    };
    let add_f_point = matches!(
        (x_ord, new_ord),
        (
            Ordering::Less | Ordering::Equal,
            Ordering::Less | Ordering::Equal
        )
    );
    let add_g_point = !add_f_point
        && matches!(
            (x_ord, new_ord),
            (
                Ordering::Greater | Ordering::Equal,
                Ordering::Greater | Ordering::Equal
            )
        );
    let add_intersection = prev_ord != Ordering::Equal && prev_ord.reverse() == new_ord;
    let is_equal = new_ord == Ordering::Equal;
    Ok(NextPointResults {
        add_f_point,
        add_g_point,
        add_intersection,
        is_equal,
    })
}

/// Return the intersection between two segments.
///
/// Return an error if the two segments do not intersect or are colinear.
fn segment_intersection<T: Float + fmt::Debug>(
    f_segment: ((T, T), (T, T)),
    g_segment: ((T, T), (T, T)),
) -> Result<(T, T)> {
    let ((f_x0, f_y0), (f_x1, f_y1)) = f_segment;
    let ((g_x0, g_y0), (g_x1, g_y1)) = g_segment;
    let f_d = (f_x1 - f_x0, f_y1 - f_y0);
    let g_d = (g_x1 - g_x0, g_y1 - g_y0);
    let diff = (g_x0 - f_x0, g_y0 - f_y0);
    let slope_diff = cross_product(f_d, g_d);
    if slope_diff == T::zero() {
        // Parallel or colinear segments.
        Err(anyhow!(
            "The segments do not intersect: {:?} and {:?}",
            f_segment,
            g_segment
        ))
    } else {
        let t = cross_product(diff, g_d) / slope_diff;
        let u = cross_product(diff, f_d) / slope_diff;
        if t < T::zero() - T::from(MARGIN).unwrap()
            || t > T::one() + T::from(MARGIN).unwrap()
            || u < T::zero() - T::from(MARGIN).unwrap()
            || u > T::one() + T::from(MARGIN).unwrap()
        {
            Err(anyhow!(
                "The segments do not intersect: {:?} and {:?}",
                f_segment,
                g_segment
            ))
        } else {
            let t = T::max(T::zero(), T::min(T::one(), t));
            Ok((f_x0 + t * f_d.0, f_y0 + t * f_d.1))
        }
    }
}

/// Cross product between two vectors.
fn cross_product<T: Float>((x0, y0): (T, T), (x1, y1): (T, T)) -> T {
    x0 * y1 - y0 * x1
}

/// Return true if the line segments [a, b] and [p, q] intersect in exactly one point.
fn intersect<T: Float>(a: (T, T), b: (T, T), p: (T, T), q: (T, T)) -> bool {
    ccw(a, b, p) != 0
        && ccw(a, b, q) != 0
        && ccw(p, q, a) != 0
        && ccw(p, q, b) != 0
        && ccw(a, b, p) != ccw(a, b, q)
        && ccw(p, q, a) != ccw(p, q, b)
}

fn ccw<T: Float>(a: (T, T), b: (T, T), c: (T, T)) -> i8 {
    let margin = T::from(MARGIN).unwrap();
    if ((a.0 - b.0).abs() < margin && (a.1 - b.1).abs() < margin)
        || ((a.0 - c.0).abs() < margin && (a.1 - c.1).abs() < margin)
        || ((b.0 - c.0).abs() < margin && (b.1 - c.1).abs() < margin)
    {
        // a == b or a == c or b == c.
        return 0;
    }

    let x = cross_product((c.0 - a.0, c.1 - a.1), (b.0 - a.0, b.1 - a.1));
    if x.abs() < margin {
        return 0;
    }

    if x > T::zero() {
        1
    } else {
        -1
    }
}

fn intersection_point<T: Float>(a: (T, T), b: (T, T), p: (T, T), q: (T, T)) -> (T, T) {
    let alpha = cross_product((p.0 - q.0, p.1 - q.1), (p.0 - a.0, p.1 - a.1))
        / cross_product((p.0 - q.0, p.1 - q.1), (b.0 - a.0, b.1 - a.1));
    (a.0 + alpha * (b.0 - a.0), a.1 + alpha * (b.1 - a.1))
}

fn colinear<T: Float>(p: (T, T), q: (T, T), r: (T, T)) -> bool {
    ccw(p, q, r) == 0
}

fn clockwise<T: Float>(p: (T, T), q: (T, T), r: (T, T)) -> bool {
    ccw(p, q, r) == 1
}

fn counter_clockwise<T: Float>(p: (T, T), q: (T, T), r: (T, T)) -> bool {
    ccw(p, q, r) == -1
}

fn push_point<T: Float + NextSmallerLarger + fmt::Debug>(
    breakpoints: &mut Vec<(T, T)>,
    p: (T, T),
    lb: &mut T,
    ub: &mut T,
) {
    let epsilon = T::from(MARGIN).unwrap();
    debug_assert!(p.1 >= T::zero());
    debug_assert!(
        breakpoints.is_empty() || breakpoints.last().unwrap().0 < p.0 + epsilon,
        "bp: {:?}, p: {:?}",
        breakpoints,
        p
    );
    if let Some((last_x, last_y)) = breakpoints.last_mut() {
        if (*last_x - p.0).abs() < epsilon {
            // The point to add has the same x as the last point added.
            if (*last_y - p.1).abs() < epsilon {
                // Do not try to add the same point again.
                return;
            }
            let new_x = if p.0 < *last_x {
                let new_x = last_x.next_larger();
                *last_x = p.0;
                new_x
            } else {
                p.0.next_larger()
            };
            breakpoints.push((new_x, p.1));
            if p.1 < *lb {
                *lb = p.1;
            }
            if p.1 > *ub {
                *ub = p.1;
            }
            return;
        }
    }
    if p.1 < *lb {
        *lb = p.1;
    }
    if p.1 > *ub {
        *ub = p.1;
    }
    if breakpoints.len() > 1
        && colinear(
            breakpoints[breakpoints.len() - 2],
            breakpoints[breakpoints.len() - 1],
            p,
        )
    {
        *breakpoints.last_mut().unwrap() = p;
        return;
    }
    breakpoints.push(p);
}

#[derive(Default, Clone)]
pub struct UndercutDescriptor {
    f_undercuts_g: bool,
    g_undercuts_f: bool,
}

impl UndercutDescriptor {
    #[inline]
    pub fn set_f_undercut(&mut self) {
        self.f_undercuts_g = true;
    }

    #[inline]
    pub fn set_g_undercut(&mut self) {
        self.g_undercuts_f = true;
    }

    #[inline]
    pub fn f_undercuts_g(&mut self) -> bool {
        self.f_undercuts_g
    }

    #[inline]
    pub fn g_undercuts_f(&mut self) -> bool {
        self.g_undercuts_f
    }
}

pub fn merge<T: Float + NextSmallerLarger + fmt::Debug>(
    f: &PWLFunction<T>,
    g: &PWLFunction<T>,
) -> Result<(PWLFunction<T>, UndercutDescriptor)> {
    let (f_first_x, f_last_x) = f.x_bounds();
    let (g_first_x, g_last_x) = g.x_bounds();
    if f_last_x < g_first_x {
        // g starts after f ends.
        return Err(anyhow!(
            "The x-bounds do not overlap: {:?} < {:?}",
            f_last_x,
            g_first_x
        ));
    }
    if g_last_x < f_first_x {
        // f starts after g ends.
        return Err(anyhow!(
            "The x-bounds do not overlap: {:?} < {:?}",
            g_last_x,
            f_first_x
        ));
    }

    let epsilon = T::from(MARGIN).unwrap();
    let mut descr = UndercutDescriptor::default();
    if f.upper_bound + epsilon < g.lower_bound {
        descr.set_f_undercut();
        return Ok((f.clone(), descr));
    } else if g.upper_bound + epsilon < f.lower_bound {
        descr.set_g_undercut();
        return Ok((g.clone(), descr));
    }

    let mut breakpoints = Vec::with_capacity(f.len() + g.len());
    let mut lb = f.lower_bound.min(g.lower_bound);
    let mut ub = f.upper_bound.min(g.upper_bound);
    let mut f_id = 0;
    let mut g_id = 0;

    while f[f_id].0 < g_first_x {
        // f starts before g.
        descr.set_f_undercut();
        breakpoints.push(f[f_id]);
        f_id += 1;
    }
    while g[g_id].0 < f_first_x {
        // g starts before f.
        descr.set_g_undercut();
        breakpoints.push(g[g_id]);
        g_id += 1;
    }

    while f_id < f.len() && g_id < g.len() {
        if intersect(f[f_id - 1], f[f_id], g[g_id - 1], g[g_id]) {
            let p = intersection_point(f[f_id - 1], f[f_id], g[g_id - 1], g[g_id]);
            push_point(&mut breakpoints, p, &mut lb, &mut ub);
            descr.set_f_undercut();
            descr.set_g_undercut();
        }

        if (f[f_id].0 - g[g_id].0).abs() < epsilon {
            if (f[f_id].1 - g[g_id].1).abs() < epsilon {
                push_point(&mut breakpoints, f[f_id], &mut lb, &mut ub);

                if counter_clockwise(g[g_id - 1], f[f_id - 1], f[f_id])
                    || counter_clockwise(f[f_id], f[f_id + 1], g[g_id + 1])
                {
                    descr.set_f_undercut();
                }
                if clockwise(g[g_id - 1], f[f_id - 1], f[f_id])
                    || clockwise(f[f_id], f[f_id + 1], g[g_id + 1])
                {
                    descr.set_g_undercut();
                }
            } else if f[f_id].1 < g[g_id].1 {
                push_point(&mut breakpoints, f[f_id], &mut lb, &mut ub);
                descr.set_f_undercut();
            } else {
                push_point(&mut breakpoints, g[g_id], &mut lb, &mut ub);
                descr.set_g_undercut();
            }
            f_id += 1;
            g_id += 1;
        } else if f[f_id].0 < g[g_id].0 {
            if counter_clockwise(g[g_id - 1], f[f_id], g[g_id]) {
                push_point(&mut breakpoints, f[f_id], &mut lb, &mut ub);
                descr.set_f_undercut();
            } else if colinear(g[g_id - 1], f[f_id], g[g_id]) {
                if breakpoints.is_empty() {
                    push_point(&mut breakpoints, f[f_id], &mut lb, &mut ub);
                } else if counter_clockwise(g[g_id - 1], f[f_id - 1], f[f_id])
                    || counter_clockwise(f[f_id], f[f_id + 1], g[g_id])
                {
                    push_point(&mut breakpoints, f[f_id], &mut lb, &mut ub);
                    descr.set_f_undercut();
                }
                if clockwise(g[g_id - 1], f[f_id - 1], f[f_id])
                    || clockwise(f[f_id], f[f_id + 1], g[g_id])
                {
                    descr.set_g_undercut();
                }
            }
            f_id += 1;
        } else {
            if counter_clockwise(f[f_id - 1], g[g_id], f[f_id]) {
                push_point(&mut breakpoints, g[g_id], &mut lb, &mut ub);
                descr.set_g_undercut();
            } else if colinear(f[f_id - 1], g[g_id], f[f_id]) {
                if breakpoints.is_empty() {
                    push_point(&mut breakpoints, g[g_id], &mut lb, &mut ub);
                } else if counter_clockwise(f[f_id - 1], g[g_id - 1], g[g_id])
                    || counter_clockwise(g[g_id], g[g_id + 1], f[f_id])
                {
                    push_point(&mut breakpoints, g[g_id], &mut lb, &mut ub);
                    descr.set_g_undercut();
                }
                if clockwise(f[f_id - 1], g[g_id - 1], g[g_id])
                    || clockwise(g[g_id], g[g_id + 1], f[f_id])
                {
                    descr.set_f_undercut();
                }
            }
            g_id += 1;
        }
    }

    if intersect(f[f.len() - 1], f[f.len()], g[g.len() - 1], g[g.len()]) {
        let s = intersection_point(f[f.len() - 1], f[f.len()], g[g.len() - 1], g[g.len()]);
        push_point(&mut breakpoints, s, &mut lb, &mut ub);

        descr.set_f_undercut();
        descr.set_g_undercut();
    }
    assert!(!breakpoints.is_empty());
    breakpoints.shrink_to_fit();
    let bf = PWLFunction::new_unchecked(breakpoints, lb, ub);

    Ok((bf, descr))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn piecewise_test() {
        let breakpoints = vec![(-10., 5.), (0., 10.), (10., -5.)];
        let bpf = PWLFunction::from_breakpoints(breakpoints).unwrap();
        assert_eq!(bpf.y_at_x(-10.).unwrap(), Some(5.));
        assert_eq!(bpf.y_at_x(0.).unwrap(), Some(10.));
        assert_eq!(bpf.y_at_x(10.).unwrap(), Some(-5.));
        assert_eq!(bpf.y_at_x(-5.).unwrap(), Some(7.5));
        assert_eq!(bpf.y_at_x(-15.).unwrap(), None);
        assert_eq!(bpf.y_at_x(15.).unwrap(), None);
        assert!(bpf.y_at_x(f64::NAN).is_err());
    }

    #[test]
    fn partial_ord_test() {
        let f = PWLFunction::from_breakpoints(vec![(-10., 0.), (0., 10.), (10., 0.)]).unwrap();
        // g has a larger x-bound than f.
        let g = PWLFunction::from_breakpoints(vec![(-10., 20.), (20., 20.)]).unwrap();
        assert_eq!(f.partial_cmp(&g), None);
        let g = PWLFunction::from_breakpoints(vec![(-20., -20.), (10., -20.)]).unwrap();
        assert_eq!(f.partial_cmp(&g), None);
        // Only needs to look at the y bounds.
        let g = PWLFunction::from_breakpoints(vec![(-10., 20.), (10., 20.)]).unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Less));
        let g = PWLFunction::from_breakpoints(vec![(-10., -20.), (10., -20.)]).unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Greater));
        // Equality.
        let g = PWLFunction::from_breakpoints(vec![(-10., 0.), (-5., 5.), (0., 10.), (10., 0.)])
            .unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Equal));
        // f below g.
        let g = PWLFunction::from_breakpoints(vec![(-10., 0.), (-5., 10.), (5., 10.), (10., 0.)])
            .unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Less));
        let g = PWLFunction::from_breakpoints(vec![(-5., 10.), (5., 10.)]).unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Less));
        // f above g.
        let g = PWLFunction::from_breakpoints(vec![(-10., 0.), (-5., 1.), (5., 1.), (10., 0.)])
            .unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Greater));
        let g = PWLFunction::from_breakpoints(vec![(-5., 1.), (5., 1.)]).unwrap();
        assert_eq!(f.partial_cmp(&g), Some(Ordering::Greater));
        // Comparison impossible
        let g = PWLFunction::from_breakpoints(vec![(-10., 0.), (-5., 10.), (5., 0.), (10., 0.)])
            .unwrap();
        assert_eq!(f.partial_cmp(&g), None);
    }

    #[test]
    fn segment_intersection_test() {
        let f_segment = ((0., 0.), (1., 1.));
        // Parallel.
        assert!(segment_intersection(f_segment, ((0., 1.), (1., 2.))).is_err());
        // Colinear.
        assert!(segment_intersection(f_segment, ((0., 0.), (2., 2.))).is_err());
        // No intersection.
        assert!(segment_intersection(f_segment, ((-0.5, 0.5), (0., 0.5))).is_err());
        // Intersection.
        assert_eq!(
            segment_intersection(f_segment, ((0., 1.), (1., 0.))).unwrap(),
            (0.5, 0.5)
        );
        // Corner intersection.
        assert_eq!(
            segment_intersection(f_segment, ((0., 0.), (1., 0.))).unwrap(),
            (0., 0.)
        );
        assert_eq!(
            segment_intersection(f_segment, ((1., 0.), (0., 0.))).unwrap(),
            (0., 0.)
        );
        assert_eq!(
            segment_intersection(f_segment, ((-0.5, 0.5), (0.5, 0.5))).unwrap(),
            (0.5, 0.5)
        );
    }

    #[test]
    fn link_none_test() {
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.)]).unwrap();

        // g starts after f ends.
        let g = PWLFunction::from_breakpoints(vec![(3., 1.), (4., 1.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), None);

        // g ends before f starts.
        let g = PWLFunction::from_breakpoints(vec![(-2., 0.), (-1., 0.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), None);

        // g starts when f ends.
        let g = PWLFunction::from_breakpoints(vec![(2., 1.), (4., 1.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), None);

        // g ends when f starts.
        let g = PWLFunction::from_breakpoints(vec![(-2., 1.), (-1., 1.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), None);
    }

    #[test]
    fn link_err_test() {
        // First arrival time for f is NEG_INFINITY + INFINITY = NAN.
        let f = PWLFunction::from_breakpoints(vec![(f64::NEG_INFINITY, f64::INFINITY), (0., 0.)])
            .unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.)]).unwrap();
        assert!(f.link(&g).is_err());
    }

    #[test]
    fn link_1_test() {
        // Easy case.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 1.), (2., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 2.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(h));
    }

    #[test]
    fn link_2_test() {
        // First breakpoint of f is skipped because g has not started.
        let f = PWLFunction::from_breakpoints(vec![(-1., 1.), (0., 1.), (1., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 1.), (2., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 2.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(h));
    }

    #[test]
    fn link_3_test() {
        // First breakpoint of g is skipped because f has not started.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.), (2., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 2.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(h));
    }

    #[test]
    fn link_4_test() {
        // Last breakpoint of f is skipped because g has ended.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 1.), (2., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 2.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(h));
    }

    #[test]
    fn link_5_test() {
        // Last breakpoints of g is skipped because f has ended.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 1.), (2., 1.), (3., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 2.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(h));
    }

    #[test]
    fn link_6_test() {
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 1.), (2., 0.), (3., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 1.), (2., 2.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(h));
    }

    #[test]
    fn link_7_test() {
        let f = PWLFunction::from_breakpoints(vec![(-1., 0.), (0., 1.), (2. * f64::EPSILON, 1.)])
            .unwrap();
        let g = PWLFunction::from_breakpoints(vec![
            (-1., 0.),
            (1., 1.),
            (1. + f64::EPSILON, 1.),
            (2., 1.),
        ])
        .unwrap();
        // The two last points are ignored because they are almost equal to the second one.
        let h = PWLFunction::from_breakpoints(vec![
            (-1., 0.),
            (0., 2.),
            // (f64::EPSILON, 2.),
            // (2. * f64::EPSILON, 2.),
        ])
        .unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(h));
    }

    #[test]
    fn link_8_test() {
        // Non-FIFO f.
        let f = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 0.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 1.), (3., 1.)]).unwrap();
        assert!(f.link(&g).is_err());
    }

    #[test]
    fn link_9_test() {
        // Non-FIFO g.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (3., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 3.), (3., 0.)]).unwrap();
        assert!(f.link(&g).is_err());
    }

    #[test]
    fn link_10_test() {
        let f = PWLFunction::from_breakpoints(vec![(f64::NEG_INFINITY, 0.), (f64::INFINITY, 0.)])
            .unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.)]).unwrap();
        assert_eq!(f.link(&g).unwrap(), Some(g));
    }

    #[test]
    fn merge_easy_test() {
        let f = PWLFunction::from_breakpoints(vec![(-10., 1.), (0., 10.), (10., 1.)]).unwrap();
        // f = f.
        assert_eq!(
            f.merge(&f).unwrap(),
            (f.clone(), vec![(-10., Ordering::Equal)])
        );
        // f < g.
        let g = PWLFunction::from_breakpoints(vec![(-10., 20.), (10., 20.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (f.clone(), vec![(-10., Ordering::Less)])
        );
        // g < f and they have the same bounds.
        let g = PWLFunction::from_breakpoints(vec![(-10., 0.), (10., 0.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (g.clone(), vec![(-10., Ordering::Greater)])
        );
        // g < f and f does not cover g.
        let g = PWLFunction::from_breakpoints(vec![(-10., 0.), (0., 5.), (10., 0.), (20., 10.)])
            .unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (g.clone(), vec![(-10., Ordering::Greater)])
        );
    }

    #[test]
    fn merge_err_test() {
        // f ends before g starts.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(2., 1.), (3., 1.)]).unwrap();
        assert!(f.merge(&g).is_err());
        assert!(g.merge(&f).is_err());
    }

    #[test]
    fn merge_1_test() {
        // Simple intersection.
        let f = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 0.), (0.5, 0.5), (1., 0.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Less), (0.5, Ordering::Greater)])
        );
    }

    #[test]
    fn merge_2_test() {
        // f starts before, g ends after.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 0.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 0.), (2., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 0.), (2., 1.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Less), (1., Ordering::Greater)])
        );
    }

    #[test]
    fn merge_3_test() {
        // Simple intersection on a known point for both f and g.
        let f = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 2.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 2.), (1., 1.), (2., 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 0.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Less), (1., Ordering::Greater)])
        );
    }

    #[test]
    fn merge_4_test() {
        // Simple intersection on a known point for f only.
        let f = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 2.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 2.), (2., 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 0.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Less), (1., Ordering::Greater)])
        );
    }

    #[test]
    fn merge_5_test() {
        // f and g starts with the same value
        let f =
            PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 2.), (4., 0.)]).unwrap();
        let g =
            PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 0.), (4., 2.)]).unwrap();
        let h =
            PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 0.), (3., 1.), (4., 0.)])
                .unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (
                h,
                vec![
                    (0., Ordering::Equal),
                    (1., Ordering::Greater),
                    (3., Ordering::Less)
                ]
            )
        );
    }

    #[test]
    fn merge_6_test() {
        // f ends after g and f is below g when g ends.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 2.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 0.), (0.5, 1.), (2., 1.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Greater), (0.5, Ordering::Less)])
        );
    }

    #[test]
    fn merge_7_test() {
        // f ends after g and f is equal to g when g ends.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 1.), (2., 1.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Greater), (1., Ordering::Less)])
        );
    }

    #[test]
    fn merge_8_test() {
        // f ends after g and f is above g when g ends.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(0., 0.), (1., 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![
            (0., 0.),
            (1., 0.),
            (1.0f64.next_larger().next_larger(), 1.),
            (2., 1.),
        ])
        .unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (
                h,
                vec![
                    (0., Ordering::Greater),
                    (1.0f64.next_larger(), Ordering::Less)
                ]
            )
        );
    }

    #[test]
    #[ignore]
    fn merge_9_test() {
        // An intersection is skipped because of rounding errors.
        let f = PWLFunction::from_breakpoints(vec![(1., 0.), (1. + f64::EPSILON, 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 1.), (1. + f64::EPSILON, 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(1., 0.), (1. + f64::EPSILON, 0.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (
                h,
                vec![(1., Ordering::Less), (1. + f64::EPSILON, Ordering::Greater)]
            )
        );
    }

    #[test]
    fn merge_10_test() {
        // An intersection is skipped because of extreme rounding errors with the point just before.
        let f = PWLFunction::from_breakpoints(vec![(1., 1.), (2., f64::MAX)]).unwrap();
        let g =
            PWLFunction::from_breakpoints(vec![(1., 1. + f64::EPSILON), (2., 1. + f64::EPSILON)])
                .unwrap();
        let h = PWLFunction::from_breakpoints(vec![
            (1., 1.),
            // (1. + f64::EPSILON, 1. + f64::EPSILON),
            (2., 1. + f64::EPSILON),
        ])
        .unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (
                h,
                vec![(1., Ordering::Less), (1. + f64::EPSILON, Ordering::Greater)]
            )
        );
    }

    #[test]
    fn merge_11_test() {
        // An intersection is skipped because of extreme rounding errors with the point just after.
        let f = PWLFunction::from_breakpoints(vec![(1., f64::MAX), (2., 1.)]).unwrap();
        let g =
            PWLFunction::from_breakpoints(vec![(1., 1. + f64::EPSILON), (2., 1. + f64::EPSILON)])
                .unwrap();
        // The last point is ignored.
        let h = PWLFunction::from_breakpoints(vec![
            (1., 1. + f64::EPSILON),
            (2.0f64.next_smaller(), 1. + f64::EPSILON),
            // (2., 1.),
        ])
        .unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (
                h,
                vec![
                    (1., Ordering::Greater),
                    (2.0f64.next_smaller(), Ordering::Less)
                ]
            )
        );
    }

    #[test]
    fn merge_12_test() {
        // f starts before g and f is below g when g starts.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 2.), (2., 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 1.), (1.5, 1.), (2., 0.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Less), (1.5, Ordering::Greater)])
        );
    }

    #[test]
    fn merge_13_test() {
        // f starts before g and f is equal to g when g starts.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 1.), (2., 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![(0., 1.), (1., 1.), (2., 0.)]).unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Less), (1., Ordering::Greater)])
        );
    }

    #[test]
    fn merge_14_test() {
        // f starts before g and f is above g when g starts.
        let f = PWLFunction::from_breakpoints(vec![(0., 1.), (2., 1.)]).unwrap();
        let g = PWLFunction::from_breakpoints(vec![(1., 0.), (2., 0.)]).unwrap();
        let h = PWLFunction::from_breakpoints(vec![
            (0., 1.),
            (1.0f64.next_smaller(), 1.),
            (1., 0.),
            (2., 0.),
        ])
        .unwrap();
        assert_eq!(
            f.merge(&g).unwrap(),
            (h, vec![(0., Ordering::Less), (1., Ordering::Greater)])
        );
    }
}
