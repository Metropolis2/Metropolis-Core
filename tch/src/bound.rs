// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

/// Optional value representing a bound.
#[derive(Clone, Copy, Debug)]
pub struct Bound<T>(Option<T>);

impl<T> Default for Bound<T> {
    fn default() -> Self {
        Bound(None)
    }
}

impl<T> Bound<T> {
    /// Creates a null bound.
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates a bound from a value.
    pub fn from_value(value: T) -> Self {
        Bound(Some(value))
    }

    /// Returns the current value of the bound.
    pub fn get(&self) -> Option<&T> {
        self.0.as_ref()
    }
}

impl<T: Copy + PartialOrd> Bound<T> {
    /// Decreases the bound to the new value if it is smaller.
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

    /// Returns `true` if the bound is smaller than the given value.
    /// Returns `false` if the bound is not smaller than the given value or if the bound is None.
    pub fn is_smaller(&self, value: T) -> bool {
        self.0.map(|b| b < value).unwrap_or(false)
    }

    /// Returns `true` if the bound is smaller or equal to the given value.
    /// Returns `false` if the bound is larger than the given value or if the bound is None.
    pub fn is_smaller_equal(&self, value: T) -> bool {
        self.0.map(|b| b <= value).unwrap_or(false)
    }
}
