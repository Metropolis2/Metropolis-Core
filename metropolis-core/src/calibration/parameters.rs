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
use crate::units::{FlowPerLane, NonNegativeSeconds};

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
    /// Parameters of the route-choice days, run before the optimization of the capacities, in each
    /// outer iteration.
    #[serde(default)]
    pub route_choice: RouteChoiceParameters,
    /// Parameters of the inner loop: optimization of the capacities, then simulation of a day with
    /// the optimized capacities and the same routes.
    #[serde(default)]
    pub inner_loop: InnerLoopParameters,
    /// Parameters of the outer loop: route-choice days, then inner loop.
    #[serde(default)]
    pub outer_loop: OuterLoopParameters,
}

/// Parameters of the route-choice days of an outer iteration (day-to-day learning with the current
/// capacities, until route choice is stable).
#[derive(Clone, Debug, Deserialize)]
#[serde(default)]
pub struct RouteChoiceParameters {
    /// The route-choice days stop when the RMSE between the expected and the simulated network
    /// conditions of a day is at most this value, in seconds (default: no tolerance).
    pub tolerance: Option<NonNegativeSeconds>,
    /// The route-choice days stop when the RMSE between the expected and the simulated network
    /// conditions of a day has decreased by less than this relative amount from the previous day,
    /// or has increased, i.e., when it has reached its floor (between 0 and 1, default: no
    /// minimum decrease).
    ///
    /// Unlike `tolerance`, it does not depend on the level of the floor, which is set by the
    /// congestion and the learning model.
    pub min_decrease: Option<f64>,
    /// Maximum number of route-choice days (default: 10).
    pub max_iterations: u64,
}

impl Default for RouteChoiceParameters {
    fn default() -> Self {
        Self {
            tolerance: None,
            min_decrease: None,
            max_iterations: 10,
        }
    }
}

/// Stopping criteria of the inner loop of the capacity calibration.
#[derive(Clone, Debug, Deserialize)]
#[serde(default)]
pub struct InnerLoopParameters {
    /// The loop stops when the fit of the surrogate model (RMSE of the delays) on the simulated day
    /// improves by less than this relative amount, or gets worse (default: 0.01).
    pub tolerance: f64,
    /// Maximum number of optimizations (default: 10).
    pub max_iterations: u64,
}

impl Default for InnerLoopParameters {
    fn default() -> Self {
        Self {
            tolerance: 0.01,
            max_iterations: 10,
        }
    }
}

/// Stopping criteria of the outer loop of the capacity calibration.
///
/// Each outer iteration is scored by the fit of the surrogate model (RMSE of the delays) after its
/// route-choice days; the capacities with the best score are returned.
#[derive(Clone, Debug, Deserialize)]
#[serde(default)]
pub struct OuterLoopParameters {
    /// The loop stops when the best score has not improved for this number of outer iterations
    /// (default: 5).
    pub patience: u64,
    /// Maximum number of outer iterations (default: 20).
    pub max_iterations: u64,
}

impl Default for OuterLoopParameters {
    fn default() -> Self {
        Self {
            patience: 5,
            max_iterations: 20,
        }
    }
}

/// Parameters of the optimization of the capacities (Levenberg–Marquardt algorithm), given the
/// arrival curves of a simulated day.
#[derive(Clone, Debug, Deserialize)]
#[serde(default)]
pub struct OptimizerParameters {
    /// Maximum relative change of the capacity of each category, compared to its capacity in the
    /// simulated day (between 0 and 1, default: 0.2).
    pub trust_region: f64,
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
            trust_region: 0.2,
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
        assert_eq!(params.optimizer.trust_region, 0.2);
        assert_eq!(params.optimizer.max_iterations, 30);
        assert_eq!(params.optimizer.step_tolerance, 1e-4);
        assert_eq!(params.optimizer.penalty, 0.);
        assert_eq!(params.route_choice.tolerance, None);
        assert_eq!(params.route_choice.min_decrease, None);
        assert_eq!(params.route_choice.max_iterations, 10);
        assert_eq!(params.inner_loop.tolerance, 0.01);
        assert_eq!(params.inner_loop.max_iterations, 10);
        assert_eq!(params.outer_loop.patience, 5);
        assert_eq!(params.outer_loop.max_iterations, 20);

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
            "optimizer": {"trust_region": 0.1, "max_iterations": 5, "penalty": 0.01}}"#,
        )
        .unwrap();
        assert_eq!(params.vehicle_type, Some(IdValue::String("car".to_owned())));
        assert_eq!(params.optimizer.trust_region, 0.1);
        assert_eq!(params.optimizer.max_iterations, 5);
        assert_eq!(params.optimizer.step_tolerance, 1e-4);
        assert_eq!(params.optimizer.penalty, 0.01);

        let params = parse(
            r#"{"capacities": 0.5, "route_choice": {"tolerance": 2.0, "min_decrease": 0.05},
            "inner_loop": {"tolerance": 0.001}, "outer_loop": {"max_iterations": 3}}"#,
        )
        .unwrap();
        assert_eq!(
            params.route_choice.tolerance,
            Some(NonNegativeSeconds::try_from(2.0).unwrap())
        );
        assert_eq!(params.route_choice.min_decrease, Some(0.05));
        assert_eq!(params.route_choice.max_iterations, 10);
        assert_eq!(params.inner_loop.tolerance, 0.001);
        assert_eq!(params.inner_loop.max_iterations, 10);
        assert_eq!(params.outer_loop.patience, 5);
        assert_eq!(params.outer_loop.max_iterations, 3);

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
