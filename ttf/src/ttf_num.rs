use num_traits::Signed;

const MARGIN32: f32 = 1e-4;
const MARGIN64: f64 = 1e-4;

pub trait TTFNum: Copy + Default + Signed + PartialOrd + std::fmt::Debug {
    fn small_margin() -> Self;
    fn large_margin() -> Self;
    fn approx_eq(&self, other: &Self) -> bool;
    fn approx_ne(&self, other: &Self) -> bool {
        !self.approx_eq(other)
    }
    fn approx_le(&self, other: &Self) -> bool;
    fn approx_lt(&self, other: &Self) -> bool;
    fn approx_ge(&self, other: &Self) -> bool {
        // self >= other - margin  -->  other <= self + margin
        other.approx_le(self)
    }
    fn approx_gt(&self, other: &Self) -> bool {
        other.approx_lt(self)
    }
    #[must_use]
    fn min(&self, other: &Self) -> Self {
        if self < other {
            *self
        } else {
            *other
        }
    }
    #[must_use]
    fn max(&self, other: &Self) -> Self {
        if self > other {
            *self
        } else {
            *other
        }
    }
    #[must_use]
    fn average(&self, other: &Self) -> Self;
    fn to_usize(&self) -> usize;
}

impl TTFNum for f32 {
    fn small_margin() -> Self {
        MARGIN32
    }
    fn large_margin() -> Self {
        100. * MARGIN32
    }
    fn approx_eq(&self, other: &Self) -> bool {
        (self - other).abs() < MARGIN32
    }
    fn approx_le(&self, other: &Self) -> bool {
        *self <= *other + MARGIN32
    }
    fn approx_lt(&self, other: &Self) -> bool {
        *self + MARGIN32 < *other
    }
    fn average(&self, other: &Self) -> Self {
        (self + other) / 2.0
    }
    fn to_usize(&self) -> usize {
        *self as usize
    }
}

impl TTFNum for f64 {
    fn small_margin() -> Self {
        MARGIN64
    }
    fn large_margin() -> Self {
        100. * MARGIN64
    }
    fn approx_eq(&self, other: &Self) -> bool {
        (self - other).abs() < MARGIN64
    }
    fn approx_le(&self, other: &Self) -> bool {
        *self <= *other + MARGIN64
    }
    fn approx_lt(&self, other: &Self) -> bool {
        *self + MARGIN64 < *other
    }
    fn average(&self, other: &Self) -> Self {
        (self + other) / 2.0
    }
    fn to_usize(&self) -> usize {
        *self as usize
    }
}

// impl TTFNum for OrderedFloat<f32> {
// fn margin() -> Self {
// OrderedFloat(MARGIN32)
// }
// fn approx_eq(self, other: Self) -> bool {
// (self.0 - other.0).abs() < MARGIN32
// }
// fn approx_le(self, other: Self) -> bool {
// self.0 <= other.0 + MARGIN32
// }
// fn approx_lt(self, other: Self) -> bool {
// self.0 + MARGIN32 < other.0
// }
// fn average(self, other: Self) -> Self {
// (self + other) / 2.0
// }
// fn to_usize(self) -> usize {
// self.0 as usize
// }
// }

// impl TTFNum for OrderedFloat<f64> {
// fn margin() -> Self {
// OrderedFloat(MARGIN64)
// }
// fn approx_eq(self, other: Self) -> bool {
// (self.0 - other.0).abs() < MARGIN64
// }
// fn approx_le(self, other: Self) -> bool {
// self.0 <= other.0 + MARGIN64
// }
// fn approx_lt(self, other: Self) -> bool {
// self.0 + MARGIN64 < other.0
// }
// fn average(self, other: Self) -> Self {
// (self + other) / 2.0
// }
// fn to_usize(self) -> usize {
// self.0 as usize
// }
// }

// impl TTFNum for NotNan<f32> {
// fn margin() -> Self {
// unsafe { NotNan::new_unchecked(MARGIN32) }
// }
// fn approx_eq(self, other: Self) -> bool {
// (self.into_inner() - other.into_inner()).abs() < MARGIN32
// }
// fn approx_le(self, other: Self) -> bool {
// self.into_inner() <= other.into_inner() + MARGIN32
// }
// fn approx_lt(self, other: Self) -> bool {
// self.into_inner() + MARGIN32 < other.into_inner()
// }
// fn average(self, other: Self) -> Self {
// (self + other) / 2.0
// }
// fn to_usize(self) -> usize {
// self.into_inner() as usize
// }
// }

// impl TTFNum for NotNan<f64> {
// fn margin() -> Self {
// unsafe { NotNan::new_unchecked(MARGIN64) }
// }
// fn approx_eq(self, other: Self) -> bool {
// (self.into_inner() - other.into_inner()).abs() < MARGIN64
// }
// fn approx_le(self, other: Self) -> bool {
// self.into_inner() <= other.into_inner() + MARGIN64
// }
// fn approx_lt(self, other: Self) -> bool {
// self.into_inner() + MARGIN64 < other.into_inner()
// }
// fn average(self, other: Self) -> Self {
// (self + other) / 2.0
// }
// fn to_usize(self) -> usize {
// self.into_inner() as usize
// }
// }
