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

use serde_derive::Deserialize;

use crate::hash::HashMap;
use crate::units::FlowPerLane;

/// Set of parameters controlling the road-capacity calibration (`capacity_calibration`).
///
/// When these parameters are defined, the capacity calibration is run instead of the simulation.
#[derive(Clone, Debug, Deserialize)]
pub struct CapacityCalibrationParameters {
    /// Initial bottleneck capacity of each edge category and its optional bounds, in PCE per
    /// second per lane.
    pub capacities: Capacities,
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
    /// categories (default: no tolerance, the calibration runs `max_days` days).
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
    /// Scale of the trust region (between 0 and 1, default: 0.4): after a day, the capacity of
    /// each category can change by at most this value times the weight of the day in the expected
    /// network conditions of the next day (see the learning model), relative to its capacity in
    /// the day.
    ///
    /// The capacities then move only as fast as the expected network conditions, and so the
    /// routes, can follow. With `Exponential` learning 0.02, the weight of a day is 34% at
    /// iteration counter 1, 9.3% at counter 10, 3.1% at counter 50 and 2.0% from about counter
    /// 200, so a scale of 0.4 gives a trust region of 14%, 3.7%, 1.2% and 0.8%.
    pub trust_region_scale: f64,
    /// Maximum number of iterations (default: 30).
    pub max_iterations: u64,
    /// The optimization stops when no capacity changes by more than this relative amount in an
    /// iteration (default: 1e-4).
    pub step_tolerance: f64,
    /// Weight λ of the penalty `λ·Σₖ (cₖ / cₖ⁰)²` added to the mean squared error of the delays, in
    /// s², where `cₖ` is the capacity of category `k` and `cₖ⁰` its initial capacity (default: 0,
    /// no penalty).
    ///
    /// A small penalty favors the lowest capacities consistent with the data: a category whose
    /// edges have no queue gets about the capacity at which queues start. The categories crossed
    /// by no target route are not penalized (their capacity is not calibrated).
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

/// Bottleneck capacities of the edge categories (initial value and optional bounds).
#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub enum Capacities {
    /// The same capacity for all the categories.
    Uniform(CategoryCapacity),
    /// The capacity of each category, given by category id.
    ByCategory(HashMap<String, CategoryCapacity>),
}

/// Bottleneck capacity of an edge category, in PCE per second per lane: initial value and optional
/// bounds.
///
/// It is given either as an object (`{"initial": 0.5, "min": 0.1, "max": 0.8}`, the bounds are
/// optional) or as a number (the initial value, without bounds).
#[derive(Clone, Copy, Debug, PartialEq, Deserialize)]
#[serde(from = "CategoryCapacityValue")]
pub struct CategoryCapacity {
    /// Initial capacity.
    pub initial: FlowPerLane,
    /// Minimum capacity (no minimum if `None`).
    pub min: Option<FlowPerLane>,
    /// Maximum capacity (no maximum if `None`).
    pub max: Option<FlowPerLane>,
}

/// Forms of a [CategoryCapacity] in the parameters.
#[derive(Deserialize)]
#[serde(untagged)]
enum CategoryCapacityValue {
    Initial(FlowPerLane),
    Full(CategoryCapacityObject),
}

/// Object form of a [CategoryCapacity] in the parameters (unknown fields are rejected, so that a
/// map of capacities by category is not read as a single capacity).
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CategoryCapacityObject {
    initial: FlowPerLane,
    #[serde(default)]
    min: Option<FlowPerLane>,
    #[serde(default)]
    max: Option<FlowPerLane>,
}

impl From<CategoryCapacityValue> for CategoryCapacity {
    fn from(value: CategoryCapacityValue) -> Self {
        match value {
            CategoryCapacityValue::Initial(initial) => Self {
                initial,
                min: None,
                max: None,
            },
            CategoryCapacityValue::Full(CategoryCapacityObject { initial, min, max }) => {
                Self { initial, min, max }
            }
        }
    }
}

impl CategoryCapacity {
    /// Returns `true` if the initial capacity is between the bounds.
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

    fn capacity(value: f64) -> FlowPerLane {
        FlowPerLane::try_from(value).unwrap()
    }

    #[test]
    fn deserialize_test() {
        let params = parse(r#"{"capacities": 0.5}"#).unwrap();
        let Capacities::Uniform(c) = params.capacities else {
            panic!("The capacity should be uniform");
        };
        assert_eq!(
            c,
            CategoryCapacity {
                initial: capacity(0.5),
                min: None,
                max: None
            }
        );
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

        let params = parse(r#"{"capacities": {"initial": 0.5, "max": 0.8}}"#).unwrap();
        let Capacities::Uniform(c) = params.capacities else {
            panic!("The capacity should be uniform");
        };
        assert_eq!(
            c,
            CategoryCapacity {
                initial: capacity(0.5),
                min: None,
                max: Some(capacity(0.8))
            }
        );

        let params = parse(
            r#"{"capacities": {"1": 0.5, "motorway": {"initial": 0.6, "min": 0.1, "max": 0.8}},
            "vehicle_type": 3}"#,
        )
        .unwrap();
        let Capacities::ByCategory(capacities) = params.capacities else {
            panic!("Capacities should be given by category");
        };
        assert_eq!(capacities.len(), 2);
        assert_eq!(capacities["1"].initial, capacity(0.5));
        assert_eq!(capacities["1"].min, None);
        assert_eq!(
            capacities["motorway"],
            CategoryCapacity {
                initial: capacity(0.6),
                min: Some(capacity(0.1)),
                max: Some(capacity(0.8))
            }
        );
        assert_eq!(params.vehicle_type, Some(IdValue::Integer(3)));
        assert_eq!(params.vehicle_type.unwrap().to_string(), "3");

        // A map whose keys are all fields of a capacity is read as a single capacity, unless the
        // values are objects.
        let params = parse(r#"{"capacities": {"initial": {"initial": 0.5}}}"#).unwrap();
        assert!(matches!(params.capacities, Capacities::ByCategory(_)));

        let params = parse(
            r#"{"capacities": 0.5, "vehicle_type": "car",
            "optimizer": {"trust_region_scale": 0.1, "max_iterations": 5, "penalty": 0.01}}"#,
        )
        .unwrap();
        assert_eq!(params.vehicle_type, Some(IdValue::String("car".to_owned())));
        assert_eq!(params.optimizer.trust_region_scale, 0.1);
        assert_eq!(params.optimizer.max_iterations, 5);
        assert_eq!(params.optimizer.step_tolerance, 1e-4);
        assert_eq!(params.optimizer.penalty, 0.01);

        let params = parse(
            r#"{"capacities": 0.5, "surrogate_days": 8, "warmup_days": 2,
            "stopping": {"max_days": 600, "tolerance": 0.01}}"#,
        )
        .unwrap();
        assert_eq!(params.surrogate_days, 8);
        assert_eq!(params.warmup_days, 2);
        assert_eq!(params.stopping.max_days, 600);
        assert_eq!(params.stopping.window, 10);
        assert_eq!(params.stopping.tolerance, Some(0.01));

        // Capacities must be positive.
        assert!(parse(r#"{"capacities": -0.5}"#).is_err());
        assert!(parse(r#"{"capacities": {"1": 0.0}}"#).is_err());
        assert!(parse(r#"{"capacities": {"initial": 0.5, "min": 0.0}}"#).is_err());
        // Initial capacities are mandatory.
        assert!(parse(r#"{"vehicle_type": "car"}"#).is_err());
        assert!(parse(r#"{"capacities": {"1": {"min": 0.5}}}"#).is_err());
    }

    #[test]
    fn is_within_bounds_test() {
        let c = |min: Option<f64>, max: Option<f64>| CategoryCapacity {
            initial: capacity(0.5),
            min: min.map(capacity),
            max: max.map(capacity),
        };
        assert!(c(None, None).is_within_bounds());
        assert!(c(Some(0.5), Some(0.5)).is_within_bounds());
        assert!(c(Some(0.1), None).is_within_bounds());
        assert!(!c(Some(0.6), None).is_within_bounds());
        assert!(!c(None, Some(0.4)).is_within_bounds());
    }
}
