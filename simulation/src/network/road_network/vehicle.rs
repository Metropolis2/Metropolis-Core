use crate::units::{Length, Speed};

use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

/// Enumerator representing a function that maps a baseline speed to an effective speed.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum SpeedFunction<T> {
    /// The identity function.
    Base,
    /// A linear function: `f(s) = a * s`.
    Multiplicator(T),
    /// A piecewise-linear function, represented by a vector of breakpoints `(x, y)`.
    ///
    /// The breakpoints `(x, y)` must be ordered by increasing `x` (the base speeds).
    Piecewise(Vec<(Speed<T>, Speed<T>)>),
}

impl<T: TTFNum> SpeedFunction<T> {
    /// Returns the effective speed given the baseline speed.
    ///
    /// If `self` is a piecewise-linear function and the baseline speed is out of bounds (the
    /// baseline speed is smaller than the smallest `x` or larger than the largest `x`), then the
    /// identity function is used.
    pub fn get_speed(&self, base_speed: Speed<T>) -> Speed<T> {
        match self {
            SpeedFunction::Base => base_speed,
            SpeedFunction::Multiplicator(mul) => Speed(*mul * base_speed.0),
            SpeedFunction::Piecewise(values) => {
                match values.binary_search_by_key(&base_speed, |&(x, _)| x) {
                    // The effective speed at the base speed is known.
                    Ok(i) => values[i].1,
                    // Use linear interpolation to compute the effective speed.
                    Err(i) => {
                        if i == 0 || i == values.len() {
                            // Base speed is out of bound.
                            return base_speed;
                        }
                        let alpha = (base_speed.0 - values[i - 1].0 .0)
                            / (values[i].0 .0 - values[i - 1].0 .0);
                        Speed(alpha * values[i].1 .0 + (T::one() - alpha) * values[i - 1].1 .0)
                    }
                }
            }
        }
    }
}

/// A road vehicle with a given [Length] and [SpeedFunction].
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Vehicle<T> {
    name: String,
    length: Length<T>,
    speed_function: SpeedFunction<T>,
}

impl<T> Vehicle<T> {
    /// Create a new vehicle with a given [Length] and [SpeedFunction].
    pub fn new(name: String, length: Length<T>, speed_function: SpeedFunction<T>) -> Self {
        Vehicle {
            name,
            length,
            speed_function,
        }
    }
}

impl<T: Copy> Vehicle<T> {
    /// Returns the length of the vehicle.
    pub fn get_length(&self) -> Length<T> {
        self.length
    }
}

impl<T: TTFNum> Vehicle<T> {
    /// Returns the effective speed of the vehicle given the baseline speed on the road.
    pub fn get_speed(&self, base_speed: Speed<T>) -> Speed<T> {
        self.speed_function.get_speed(base_speed)
    }
}

#[derive(
    Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash, Deserialize, Serialize,
)]
pub struct VehicleIndex(usize);

impl VehicleIndex {
    pub fn new(x: usize) -> Self {
        VehicleIndex(x)
    }

    pub fn index(self) -> usize {
        self.0
    }
}

pub fn vehicle_index(x: usize) -> VehicleIndex {
    VehicleIndex::new(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn speed_function_test() {
        let base = SpeedFunction::Base;
        assert_eq!(base.get_speed(Speed::new(0.0)), Speed::new(0.0));
        assert_eq!(base.get_speed(Speed::new(130.0)), Speed::new(130.0));
        assert_eq!(base.get_speed(Speed::new(50.0)), Speed::new(50.0));
        assert_eq!(base.get_speed(Speed::new(70.0)), Speed::new(70.0));

        let mult = SpeedFunction::Multiplicator(0.9);
        assert_eq!(mult.get_speed(Speed::new(0.0)), Speed::new(0.0));
        assert_eq!(mult.get_speed(Speed::new(130.0)), Speed::new(130.0 * 0.9));
        assert_eq!(mult.get_speed(Speed::new(50.0)), Speed::new(50.0 * 0.9));
        assert_eq!(mult.get_speed(Speed::new(70.0)), Speed::new(70.0 * 0.9));

        let func = SpeedFunction::Piecewise(vec![
            (Speed::new(0.0), Speed::new(0.0)),
            (Speed::new(50.0), Speed::new(50.0)),
            (Speed::new(90.0), Speed::new(80.0)),
            (Speed::new(130.0), Speed::new(110.0)),
        ]);
        assert_eq!(func.get_speed(Speed::new(0.0)), Speed::new(0.0));
        assert_eq!(func.get_speed(Speed::new(130.0)), Speed::new(110.0));
        assert_eq!(func.get_speed(Speed::new(50.0)), Speed::new(50.0));
        assert_eq!(func.get_speed(Speed::new(70.0)), Speed::new(65.0));
    }
}
