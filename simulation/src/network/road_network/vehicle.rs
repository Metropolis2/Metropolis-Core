//! Description of the vehicles that can travel on a [RoadNetwork].
use crate::units::{Length, Speed, PCE};

use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

/// Enumerator representing a function that maps a baseline speed to an effective speed.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "values")]
pub enum SpeedFunction<T> {
    /// The identity function.
    Base,
    /// A linear function: `f(s) = a * s`.
    Multiplicator(T),
    /// A piecewise-linear function, represented by a vector of breakpoints `(x, y)`.
    ///
    /// The breakpoints `(x, y)` must be ordered by increasing `x` (the base speeds).
    Piecewise(Vec<[Speed<T>; 2]>),
}

impl<T> Default for SpeedFunction<T> {
    fn default() -> Self {
        Self::Base
    }
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
                match values.binary_search_by_key(&base_speed, |&[x, _]| x) {
                    // The effective speed at the base speed is known.
                    Ok(i) => values[i][1],
                    // Use linear interpolation to compute the effective speed.
                    Err(i) => {
                        if i == 0 || i == values.len() {
                            // Base speed is out of bound.
                            return base_speed;
                        }
                        let alpha = (base_speed.0 - values[i - 1][0].0)
                            / (values[i][0].0 - values[i - 1][0].0);
                        Speed(alpha * values[i][1].0 + (T::one() - alpha) * values[i - 1][1].0)
                    }
                }
            }
        }
    }
}

/// A road vehicle with a given [Length], [PCE] and [SpeedFunction].
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[schemars(title = "Vehicle")]
#[schemars(
    description = "A road vehicle with a given length, passenger car equivalent and speed function."
)]
#[schemars(example = "crate::schema::example_vehicle")]
#[schemars(example = "crate::schema::example_vehicle2")]
pub struct Vehicle<T> {
    /// Length of the vehicle, used to compute vehicle density on the edges.
    length: Length<T>,
    /// Passenger car equivalent of the vehicle, used to compute bottleneck outflow.
    pce: PCE<T>,
    /// Speed function that gives the vehicle speed as a function of the edge base speed.
    #[serde(default)]
    speed_function: SpeedFunction<T>,
}

impl<T> Vehicle<T> {
    /// Create a new vehicle with a given [Length], [PCE] and [SpeedFunction].
    pub fn new(length: Length<T>, pce: PCE<T>, speed_function: SpeedFunction<T>) -> Self {
        Vehicle {
            length,
            pce,
            speed_function,
        }
    }
}

impl<T: Copy> Vehicle<T> {
    /// Returns the length of the vehicle.
    pub fn get_length(&self) -> Length<T> {
        self.length
    }

    /// Returns the PCE of the vehicle.
    pub fn get_pce(&self) -> PCE<T> {
        self.pce
    }
}

impl<T: TTFNum> Vehicle<T> {
    /// Returns the effective speed of the vehicle given the baseline speed on the road.
    pub fn get_speed(&self, base_speed: Speed<T>) -> Speed<T> {
        self.speed_function.get_speed(base_speed)
    }
}

#[derive(
    Copy,
    Clone,
    Debug,
    Default,
    PartialEq,
    PartialOrd,
    Eq,
    Ord,
    Hash,
    Deserialize,
    Serialize,
    JsonSchema,
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
        assert_eq!(base.get_speed(Speed(0.0)), Speed(0.0));
        assert_eq!(base.get_speed(Speed(130.0)), Speed(130.0));
        assert_eq!(base.get_speed(Speed(50.0)), Speed(50.0));
        assert_eq!(base.get_speed(Speed(70.0)), Speed(70.0));

        let mult = SpeedFunction::Multiplicator(0.9);
        assert_eq!(mult.get_speed(Speed(0.0)), Speed(0.0));
        assert_eq!(mult.get_speed(Speed(130.0)), Speed(130.0 * 0.9));
        assert_eq!(mult.get_speed(Speed(50.0)), Speed(50.0 * 0.9));
        assert_eq!(mult.get_speed(Speed(70.0)), Speed(70.0 * 0.9));

        let func = SpeedFunction::Piecewise(vec![
            [Speed(0.0), Speed(0.0)],
            [Speed(50.0), Speed(50.0)],
            [Speed(90.0), Speed(80.0)],
            [Speed(130.0), Speed(110.0)],
        ]);
        assert_eq!(func.get_speed(Speed(0.0)), Speed(0.0));
        assert_eq!(func.get_speed(Speed(130.0)), Speed(110.0));
        assert_eq!(func.get_speed(Speed(50.0)), Speed(50.0));
        assert_eq!(func.get_speed(Speed(70.0)), Speed(65.0));
    }
}
