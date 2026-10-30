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

//! Parameters of the road-capacity calibration.
use std::fmt;

use num_traits::ConstOne;
use serde_derive::Deserialize;

use crate::hash::HashMap;
use crate::units::{FlowPerLane, PositiveNum};

/// Set of parameters controlling the road-capacity calibration (`capacity_calibration`).
///
/// When these parameters are defined, the capacity calibration is run instead of the simulation.
///
/// The capacity per lane of a calibrated edge is `capacity` times the product of the values of its
/// factors (input file `capacity_factors`), which are calibrated.
#[derive(Clone, Debug, Deserialize)]
pub struct CapacityCalibrationParameters {
    /// Capacity per lane of an edge whose factors are all equal to 1, in PCE per second per lane
    /// (not calibrated).
    pub capacity: FlowPerLane,
    /// Initial value and optional bounds of the factors, by factor id (default: initial value 1
    /// and no bounds for the factors that are not given).
    #[serde(default)]
    pub factors: HashMap<String, Factor>,
    /// Vehicle type used to compute the free-flow travel times of the target routes.
    ///
    /// This is optional if a single vehicle type is defined.
    #[serde(default)]
    pub vehicle_type: Option<IdValue>,
    /// Parameters of the optimization of the capacities.
    #[serde(default)]
    pub optimizer: OptimizerParameters,
    /// Number of last simulated days whose surrogate models are averaged to score the capacities
    /// and to optimize them after each day (default: 1).
    ///
    /// The days may have been simulated with different capacities: the surrogate model of each
    /// day evaluates the queues of its arrival curves at any capacities.
    #[serde(default = "default_surrogate_days")]
    pub surrogate_days: u64,
    /// Number of warm-up days, simulated with the initial capacities before the first optimization
    /// (default: 0).
    ///
    /// Their routes are still far from the equilibrium (e.g., from free-flow conditions, the first
    /// day takes the free-flow routes), so they are not used by the surrogate models, nor in the
    /// stopping criteria and the calibrated capacities. They count in `stopping.max_days`.
    #[serde(default)]
    pub warmup_days: u64,
    /// Stopping criteria of the calibration.
    #[serde(default)]
    pub stopping: StoppingParameters,
}

const fn default_surrogate_days() -> u64 {
    1
}

/// Stopping criteria of the capacity calibration.
///
/// The calibrated capacities are the mean of the capacities of the last `window` simulated days.
#[derive(Clone, Debug, Deserialize)]
#[serde(default)]
pub struct StoppingParameters {
    /// Maximum number of simulated days (default: 100).
    pub max_days: u64,
    /// Number of days whose capacities are averaged, for the calibrated capacities and for the
    /// stability test (default: 10).
    pub window: u64,
    /// The calibration stops when the mean capacities of the last `window` days differ by at most
    /// this relative amount from the mean capacities of the `window` days before, for all the
    /// factors (default: no tolerance, the calibration runs `max_days` days).
    pub tolerance: Option<f64>,
}

impl Default for StoppingParameters {
    fn default() -> Self {
        Self {
            max_days: 100,
            window: 10,
            tolerance: None,
        }
    }
}

/// Parameters of the optimization of the capacities (Levenberg–Marquardt algorithm), given the
/// arrival curves of the last simulated days.
#[derive(Clone, Debug, Deserialize)]
#[serde(default)]
pub struct OptimizerParameters {
    /// Scale of the trust region (between 0 and 1, default: 0.4): after a day, each factor can
    /// change by at most this value times the weight of the day in the expected network conditions
    /// of the next day (see the learning model), relative to its value in the day (the capacity of
    /// an edge with `k` factors can then change by up to `(1 + r)^k - 1`, for a trust region `r`).
    ///
    /// The capacities then move only as fast as the expected network conditions, and so the
    /// routes, can follow. With `Exponential` learning 0.02, the weight of a day is 34% at
    /// iteration counter 1, 9.3% at counter 10, 3.1% at counter 50 and 2.0% from about counter
    /// 200, so a scale of 0.4 gives a trust region of 14%, 3.7%, 1.2% and 0.8%.
    pub trust_region_scale: f64,
    /// Maximum number of iterations (default: 30).
    pub max_iterations: u64,
    /// The optimization stops when no factor changes by more than this relative amount in an
    /// iteration (default: 1e-4).
    pub step_tolerance: f64,
    /// Weight λ of the penalty `λ·Σⱼ (fⱼ / fⱼ⁰)²` added to the mean squared error of the delays, in
    /// s², where `fⱼ` is the value of factor `j` and `fⱼ⁰` its initial value (default: 0, no
    /// penalty).
    ///
    /// A small penalty favors the lowest capacities consistent with the data: a factor whose edges
    /// have no queue gets about the value at which queues start. The factors whose edges are
    /// crossed by no target route are not penalized (they are not calibrated).
    pub penalty: f64,
}

impl Default for OptimizerParameters {
    fn default() -> Self {
        Self {
            trust_region_scale: 0.4,
            max_iterations: 30,
            step_tolerance: 1e-4,
            penalty: 0.,
        }
    }
}

/// Capacity factor: initial value and optional bounds.
///
/// It is given either as an object (`{"initial": 0.5, "min": 0.1, "max": 1.0}`, all the fields are
/// optional, the initial value is 1 by default) or as a number (the initial value, without
/// bounds).
#[derive(Clone, Copy, Debug, PartialEq, Deserialize)]
#[serde(from = "FactorValue")]
pub struct Factor {
    /// Initial value.
    pub initial: PositiveNum,
    /// Minimum value (no minimum if `None`).
    pub min: Option<PositiveNum>,
    /// Maximum value (no maximum if `None`).
    pub max: Option<PositiveNum>,
}

impl Default for Factor {
    fn default() -> Self {
        Self {
            initial: PositiveNum::ONE,
            min: None,
            max: None,
        }
    }
}

/// Forms of a [Factor] in the parameters.
#[derive(Deserialize)]
#[serde(untagged)]
enum FactorValue {
    Initial(PositiveNum),
    Full(FactorObject),
}

/// Object form of a [Factor] in the parameters (unknown fields are rejected).
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FactorObject {
    #[serde(default = "one")]
    initial: PositiveNum,
    #[serde(default)]
    min: Option<PositiveNum>,
    #[serde(default)]
    max: Option<PositiveNum>,
}

const fn one() -> PositiveNum {
    PositiveNum::ONE
}

impl From<FactorValue> for Factor {
    fn from(value: FactorValue) -> Self {
        match value {
            FactorValue::Initial(initial) => Self {
                initial,
                ..Default::default()
            },
            FactorValue::Full(FactorObject { initial, min, max }) => Self { initial, min, max },
        }
    }
}

impl Factor {
    /// Returns `true` if the initial value is between the bounds.
    pub(crate) fn is_within_bounds(&self) -> bool {
        self.min.is_none_or(|min| min <= self.initial)
            && self.max.is_none_or(|max| self.initial <= max)
    }
}

/// An identifier given in the parameters, either as an integer or as a string.
///
/// It is compared to the identifiers of the input files through their string representation.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(untagged)]
pub enum IdValue {
    /// Integer identifier.
    Integer(i64),
    /// String identifier.
    String(String),
}

impl fmt::Display for IdValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(i) => write!(f, "{i}"),
            Self::String(s) => write!(f, "{s}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(json: &str) -> serde_json::Result<CapacityCalibrationParameters> {
        serde_json::from_str(json)
    }

    fn num(value: f64) -> PositiveNum {
        PositiveNum::try_from(value).unwrap()
    }

    #[test]
    fn deserialize_test() {
        let params = parse(r#"{"capacity": 0.5}"#).unwrap();
        assert_eq!(params.capacity, FlowPerLane::try_from(0.5).unwrap());
        assert!(params.factors.is_empty());
        assert_eq!(params.vehicle_type, None);
        assert_eq!(params.optimizer.trust_region_scale, 0.4);
        assert_eq!(params.optimizer.max_iterations, 30);
        assert_eq!(params.optimizer.step_tolerance, 1e-4);
        assert_eq!(params.optimizer.penalty, 0.);
        assert_eq!(params.surrogate_days, 1);
        assert_eq!(params.warmup_days, 0);
        assert_eq!(params.stopping.max_days, 100);
        assert_eq!(params.stopping.window, 10);
        assert_eq!(params.stopping.tolerance, None);

        let params = parse(
            r#"{"capacity": 0.5, "factors": {"1": 0.5, "motorway": {"initial": 0.6, "min": 0.1,
            "max": 0.8}, "signals": {"max": 1.0}, "lanes": {}}, "vehicle_type": 3}"#,
        )
        .unwrap();
        assert_eq!(params.factors.len(), 4);
        assert_eq!(
            params.factors["1"],
            Factor {
                initial: num(0.5),
                min: None,
                max: None
            }
        );
        assert_eq!(
            params.factors["motorway"],
            Factor {
                initial: num(0.6),
                min: Some(num(0.1)),
                max: Some(num(0.8))
            }
        );
        // The initial value is 1 by default.
        assert_eq!(
            params.factors["signals"],
            Factor {
                initial: num(1.0),
                min: None,
                max: Some(num(1.0))
            }
        );
        assert_eq!(params.factors["lanes"], Factor::default());
        assert_eq!(params.vehicle_type, Some(IdValue::Integer(3)));
        assert_eq!(params.vehicle_type.unwrap().to_string(), "3");

        let params = parse(
            r#"{"capacity": 0.5, "vehicle_type": "car",
            "optimizer": {"trust_region_scale": 0.1, "max_iterations": 5, "penalty": 0.01}}"#,
        )
        .unwrap();
        assert_eq!(params.vehicle_type, Some(IdValue::String("car".to_owned())));
        assert_eq!(params.optimizer.trust_region_scale, 0.1);
        assert_eq!(params.optimizer.max_iterations, 5);
        assert_eq!(params.optimizer.step_tolerance, 1e-4);
        assert_eq!(params.optimizer.penalty, 0.01);

        let params = parse(
            r#"{"capacity": 0.5, "surrogate_days": 8, "warmup_days": 2,
            "stopping": {"max_days": 600, "tolerance": 0.01}}"#,
        )
        .unwrap();
        assert_eq!(params.surrogate_days, 8);
        assert_eq!(params.warmup_days, 2);
        assert_eq!(params.stopping.max_days, 600);
        assert_eq!(params.stopping.window, 10);
        assert_eq!(params.stopping.tolerance, Some(0.01));

        // The capacity and the factors must be positive.
        assert!(parse(r#"{"capacity": -0.5}"#).is_err());
        assert!(parse(r#"{"capacity": 0.5, "factors": {"1": 0.0}}"#).is_err());
        assert!(parse(r#"{"capacity": 0.5, "factors": {"1": {"min": 0.0}}}"#).is_err());
        // The capacity is mandatory.
        assert!(parse(r#"{"vehicle_type": "car"}"#).is_err());
        // Unknown fields of a factor are rejected.
        assert!(parse(r#"{"capacity": 0.5, "factors": {"1": {"maximum": 1.0}}}"#).is_err());
    }

    #[test]
    fn is_within_bounds_test() {
        let f = |min: Option<f64>, max: Option<f64>| Factor {
            initial: num(0.5),
            min: min.map(num),
            max: max.map(num),
        };
        assert!(f(None, None).is_within_bounds());
        assert!(f(Some(0.5), Some(0.5)).is_within_bounds());
        assert!(f(Some(0.1), None).is_within_bounds());
        assert!(!f(Some(0.6), None).is_within_bounds());
        assert!(!f(None, Some(0.4)).is_within_bounds());
    }
}
