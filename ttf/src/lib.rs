#[cfg(feature = "serde-1")]
#[macro_use]
extern crate serde_derive;

mod point;
mod pwl;
mod ttf_num;

pub use pwl::PwlTTF;
pub use ttf_num::TTFNum;

use std::cmp::Ordering;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct UndercutDescriptor {
    pub f_undercuts_strictly: bool,
    pub g_undercuts_strictly: bool,
}

impl UndercutDescriptor {
    fn reverse(mut self) -> Self {
        std::mem::swap(
            &mut self.f_undercuts_strictly,
            &mut self.g_undercuts_strictly,
        );
        self
    }
}

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
    pub fn get_min(&self) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.get_min(),
            Self::Constant(c) => *c,
        }
    }

    pub fn get_max(&self) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.get_max(),
            Self::Constant(c) => *c,
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.len(),
            Self::Constant(_) => 0,
        }
    }

    pub fn middle_departure_time(&self) -> Option<T> {
        match self {
            Self::Piecewise(pwl_ttf) => Some(pwl_ttf.middle_departure_time()),
            Self::Constant(_) => None,
        }
    }

    pub fn eval(&self, x: T) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.eval(x),
            Self::Constant(c) => *c,
        }
    }

    pub fn departure_time_with_arrival(&self, z: T) -> T {
        match self {
            Self::Piecewise(pwl_ttf) => pwl_ttf.x_at_z(z),
            Self::Constant(c) => z - *c,
        }
    }

    #[must_use]
    pub fn link(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => Self::Piecewise(pwl::link(f, g)),
            (Self::Piecewise(f), Self::Constant(c)) => Self::Piecewise(f.add(*c)),
            (Self::Constant(c), Self::Piecewise(g)) => Self::Piecewise(pwl::link_cst_before(g, *c)),
            (Self::Constant(a), Self::Constant(b)) => Self::Constant(*a + *b),
        }
    }

    #[must_use]
    pub fn merge(&self, other: &Self) -> (Self, UndercutDescriptor) {
        match (self, other) {
            (Self::Piecewise(f), Self::Piecewise(g)) => {
                let (h, descr) = pwl::merge(f, g);
                (Self::Piecewise(h), descr)
            }
            (Self::Piecewise(f), &Self::Constant(c)) => {
                let mut descr = UndercutDescriptor::default();
                if c.approx_lt(&f.get_min()) {
                    descr.g_undercuts_strictly = true;
                    (Self::Constant(c), descr)
                } else if f.get_max().approx_lt(&c) {
                    descr.f_undercuts_strictly = true;
                    (Self::Piecewise(f.clone()), descr)
                } else {
                    let (h, descr) = pwl::merge_cst(f, c);
                    let h = if h.is_cst() {
                        Self::Constant(h.get_cst_value())
                    } else {
                        Self::Piecewise(h)
                    };
                    (h, descr)
                }
            }
            (&Self::Constant(c), Self::Piecewise(g)) => {
                let mut descr = UndercutDescriptor::default();
                if c.approx_lt(&g.get_min()) {
                    descr.f_undercuts_strictly = true;
                    (Self::Constant(c), descr)
                } else if g.get_max().approx_lt(&c) {
                    descr.g_undercuts_strictly = true;
                    (Self::Piecewise(g.clone()), descr)
                } else {
                    let (h, rev_descr) = pwl::merge_cst(g, c);
                    let h = if h.is_cst() {
                        Self::Constant(h.get_cst_value())
                    } else {
                        Self::Piecewise(h)
                    };
                    (h, rev_descr.reverse())
                }
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

    pub fn analyze_relative_position(&self, other: &Self) -> Vec<(T, Ordering)> {
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
                let pos = if b.approx_lt(&a) {
                    Ordering::Greater
                } else {
                    Ordering::Less
                };
                vec![(T::zero(), pos)]
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
