#[cfg(feature = "serde-1")]
#[macro_use]
extern crate serde_derive;

mod point;
mod pwl;
mod ttf_num;

pub use pwl::PwlTTF;
pub use ttf_num::TTFNum;

use either::Either;
use std::cmp::Ordering;

/// Descriptor used when merging two TTFs `f` and `g`.
///
/// If `f_undercuts_strictly` is `true`, it means that there exists `x` such that `f(x) < g(x)`.
///
/// If `g_undercuts_strictly` is `true`, it means that there exists `x` such that `g(x) < f(x)`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct UndercutDescriptor {
    pub f_undercuts_strictly: bool,
    pub g_undercuts_strictly: bool,
}

impl UndercutDescriptor {
    /// Reverse the role of `f` and `g` in the descriptor.
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
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub enum TTF<T> {
    Piecewise(PwlTTF<T>),
    Constant(T),
}

impl<T: TTFNum> Default for TTF<T> {
    fn default() -> Self {
        TTF::Constant(T::zero())
    }
}

impl<T: TTFNum> TTF<T> {
    /// Return the minimum travel time observed over the departure-time period, i.e., return `min_x
    /// f(x)`.
    pub fn get_min(&self) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.get_min(),
            Self::Constant(c) => *c,
        }
    }

    /// Return the maximum travel time observed over the departure-time period, i.e., return `max_x
    /// f(x)`.
    pub fn get_max(&self) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.get_max(),
            Self::Constant(c) => *c,
        }
    }

    /// Return the complexity of the TTF.
    ///
    /// - Return 0 if the TTF is a constant.
    /// - Return the number of breakpoints if the TTF is piecewise-linear.
    pub fn complexity(&self) -> usize {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.len(),
            Self::Constant(_) => 0,
        }
    }

    /// Return the departure time at the middle of the departure-time period of the TTF.
    ///
    /// If the TTF is constant, the departure-time period is unknown so `None` is returned instead.
    pub fn middle_departure_time(&self) -> Option<T> {
        match self {
            Self::Piecewise(pwl_ttf) => Some(pwl_ttf.middle_departure_time()),
            Self::Constant(_) => None,
        }
    }

    /// Return the travel time at the given departure time.
    pub fn eval(&self, x: T) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.eval(x),
            Self::Constant(c) => *c,
        }
    }

    /// Return the departure time `x` such that `f(x) = z`.
    ///
    /// # Example
    ///
    /// ```
    /// use ttf::TTF;
    /// let ttf = TTF::Constant(1.0f64);
    /// assert_eq!(ttf.departure_time_with_arrival(3.0), 2.0);
    /// ```
    pub fn departure_time_with_arrival(&self, z: T) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.x_at_z(z),
            Self::Constant(c) => z - *c,
        }
    }

    /// Link the TTF with another TTF.
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

    /// Merge the TTF with another TTF.
    ///
    /// The merge operation returns the TTF `h` such that `h(x) = min(f(x), g(x))`.
    /// It also returns an [UndercutDescriptor] that describes if `f` is strictly below `g` and if
    /// `g` is strictly below `f` at some point.
    ///
    /// # Example
    ///
    /// ```
    /// use ttf::TTF;
    /// let f = TTF::Constant(1.0f64);
    /// let g = TTF::Constant(2.0f64);
    /// let descr = UndercutDescriptor {
    ///     f_undercuts_strictly: false,
    ///     g_undercuts_strictly: true,
    /// }
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
                    Self::Constant(h.get_cst_value())
                } else {
                    Self::Piecewise(h)
                };
                (h, descr)
            }
            (&Self::Constant(c), Self::Piecewise(g)) => {
                let (h, rev_descr) = pwl::merge_cst(g, c);
                let h = if h.is_cst() {
                    Self::Constant(h.get_cst_value())
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

    /// Simulate the merge operation between two TTFs `f` and `g` and check where `f` is below `g`
    /// and where `g` is below `f`.
    ///
    /// Return either
    /// - an `Ordering` implying that `f` is always below `g` or `g` is always below `f`.
    /// - a vector of tuples `(T, Ordering)`, where a value `(t, ord)` means that, starting from
    ///   departure time `t`, the ordering between `f` and `g` is `ord`.
    ///   The vector is ordered by increasing departure times.
    pub fn analyze_relative_position(&self, other: &Self) -> Either<Ordering, Vec<(T, Ordering)>> {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => pwl::analyze_relative_position(f, g),
            (Self::Piecewise(f), &Self::Constant(c)) => pwl::analyze_relative_position_to_cst(f, c),
            (&Self::Constant(c), Self::Piecewise(g)) => {
                let mut pos = pwl::analyze_relative_position_to_cst(g, c);
                for (_x, ord) in pos.iter_mut() {
                    *ord = ord.reverse();
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

    #[must_use]
    pub fn add(&self, c: T) -> Self {
        match self {
            Self::Piecewise(pwl_ttf) => TTF::Piecewise(pwl_ttf.add(c)),
            Self::Constant(c0) => TTF::Constant(*c0 + c),
        }
    }

    pub fn approximate(&mut self, error: T) {
        if let Self::Piecewise(pwl_ttf) = self {
            pwl_ttf.approximate(error);
        }
    }

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
