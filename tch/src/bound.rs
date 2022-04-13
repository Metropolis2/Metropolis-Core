/// Optional value representing a bound.
#[derive(Clone, Copy, Debug)]
pub struct Bound<T>(Option<T>);

impl<T> Default for Bound<T> {
    fn default() -> Self {
        Bound(None)
    }
}

impl<T> Bound<T> {
    /// Create an null bound.
    pub fn new() -> Self {
        Default::default()
    }

    /// Create a bound from a value.
    pub fn from_value(value: T) -> Self {
        Bound(Some(value))
    }

    /// Return the current value of the bound.
    pub fn get(&self) -> Option<&T> {
        self.0.as_ref()
    }
}

impl<T: Copy + PartialOrd> Bound<T> {
    /// Decrease the bound to the new value if it is smaller.
    ///
    /// Does nothing if the new value is larger than the bound.
    pub fn update(&mut self, new_value: T) {
        if let Some(ref mut old_value) = self.0 {
            if new_value < *old_value {
                *old_value = new_value;
            }
        } else {
            self.0 = Some(new_value);
        }
    }

    /// Return `true` if the bound is smaller than the given value.
    /// Return `false` if the bound is not smaller than the given value or if the bound is None.
    pub fn is_smaller(&self, value: T) -> bool {
        self.0.map(|b| b < value).unwrap_or(false)
    }

    /// Return `true` if the bound is smaller or equal to the given value.
    /// Return `false` if the bound is larger than the given value or if the bound is None.
    pub fn is_smaller_equal(&self, value: T) -> bool {
        self.0.map(|b| b <= value).unwrap_or(false)
    }
}
