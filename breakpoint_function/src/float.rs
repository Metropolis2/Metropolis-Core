use float_next_after::NextAfter;
use ordered_float::{NotNan, OrderedFloat};

/// A number with methods to get the next larger and smaller value.
pub trait NextSmallerLarger {
    /// Return the smallest value that is larger than `self`.
    #[must_use]
    fn next_larger(self) -> Self;
    /// Return the largest value that is smaller than `self`.
    #[must_use]
    fn next_smaller(self) -> Self;
}

impl NextSmallerLarger for f32 {
    fn next_larger(self) -> Self {
        self.next_after(f32::INFINITY)
    }
    fn next_smaller(self) -> Self {
        self.next_after(f32::NEG_INFINITY)
    }
}

impl NextSmallerLarger for f64 {
    fn next_larger(self) -> Self {
        self.next_after(f64::INFINITY)
    }
    fn next_smaller(self) -> Self {
        self.next_after(f64::NEG_INFINITY)
    }
}

macro_rules! impl_notnan_float(
    ( $( $t:ident ),* ) => {
        $(
            impl NextSmallerLarger for NotNan<$t> {
                fn next_larger(self) -> Self {
                    // This is safe as `next_after` cannot return NaN if `self` is not NaN.
                    unsafe { NotNan::new_unchecked(self.into_inner().next_after($t::INFINITY)) }
                }
                fn next_smaller(self) -> Self {
                    // This is safe as `next_after` cannot return NaN if `self` is not NaN.
                    unsafe { NotNan::new_unchecked(self.into_inner().next_after($t::NEG_INFINITY)) }
                }
            }
        )*
    };
);

impl_notnan_float!(f32, f64);

macro_rules! impl_ordered_float(
    ( $( $t:ident ),* ) => {
        $(
            impl NextSmallerLarger for OrderedFloat<$t> {
                fn next_larger(self) -> Self {
                    // This is safe as `next_after` cannot return NaN if `self` is not NaN.
                    OrderedFloat(self.into_inner().next_after($t::INFINITY))
                }
                fn next_smaller(self) -> Self {
                    // This is safe as `next_after` cannot return NaN if `self` is not NaN.
                    OrderedFloat(self.into_inner().next_after($t::NEG_INFINITY))
                }
            }
        )*
    };
);

impl_ordered_float!(f32, f64);
