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
    /// Initial bottleneck capacity of each edge category, in PCE per second per lane.
    pub initial_capacities: InitialCapacities,
    /// Vehicle type used to compute the free-flow travel times of the target routes.
    ///
    /// This is optional if a single vehicle type is defined.
    #[serde(default)]
    pub vehicle_type: Option<IdValue>,
}

/// Initial bottleneck capacities of the edge categories, in PCE per second per lane.
#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub enum InitialCapacities {
    /// The same initial capacity for all the categories.
    Uniform(FlowPerLane),
    /// The initial capacity of each category, given by category id.
    ByCategory(HashMap<String, FlowPerLane>),
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

    #[test]
    fn deserialize_test() {
        let params = parse(r#"{"initial_capacities": 0.5}"#).unwrap();
        assert!(matches!(
            params.initial_capacities,
            InitialCapacities::Uniform(c) if c == FlowPerLane::try_from(0.5).unwrap()
        ));
        assert_eq!(params.vehicle_type, None);

        let params =
            parse(r#"{"initial_capacities": {"1": 0.5, "motorway": 0.6}, "vehicle_type": 3}"#)
                .unwrap();
        let InitialCapacities::ByCategory(capacities) = params.initial_capacities else {
            panic!("Capacities should be given by category");
        };
        assert_eq!(capacities.len(), 2);
        assert_eq!(capacities["1"], FlowPerLane::try_from(0.5).unwrap());
        assert_eq!(capacities["motorway"], FlowPerLane::try_from(0.6).unwrap());
        assert_eq!(params.vehicle_type, Some(IdValue::Integer(3)));
        assert_eq!(params.vehicle_type.unwrap().to_string(), "3");

        let params = parse(r#"{"initial_capacities": 0.5, "vehicle_type": "car"}"#).unwrap();
        assert_eq!(params.vehicle_type, Some(IdValue::String("car".to_owned())));

        // Capacities must be positive.
        assert!(parse(r#"{"initial_capacities": -0.5}"#).is_err());
        assert!(parse(r#"{"initial_capacities": {"1": 0.0}}"#).is_err());
        // Initial capacities are mandatory.
        assert!(parse(r#"{"vehicle_type": "car"}"#).is_err());
    }
}
