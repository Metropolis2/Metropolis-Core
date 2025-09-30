// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Description of the vehicles that can travel on a [RoadNetwork](super::RoadNetwork).
use anyhow::{anyhow, bail, Context, Result};
use hashbrown::HashSet;
use num_traits::ConstZero;

use super::OriginalEdgeId;
use crate::units::*;

/// Enumerator representing a function that maps a baseline speed to an effective speed.
#[derive(Clone, Debug, PartialEq)]
pub enum SpeedFunction {
    /// The identity function.
    Base,
    /// The effective speed is bounded by a given value: `f(s) = max(s, ub)`.
    UpperBound(MetersPerSecond),
    /// A linear function: `f(s) = a * s`.
    Multiplicator(PositiveNum),
    /// A piecewise-linear function, represented by a vector of breakpoints `(x, y)`, where `x` is
    /// the base speed on the edge and `y` is the effective speed.
    ///
    /// The breakpoints `(x, y)` must be ordered by increasing `x`.
    ///
    /// If the edge's base speed is out of bound (i.e., smaller than the smaller `x` value or
    /// larger than the largest `x` value), the base speed is used as the effective speed.
    Piecewise(Vec<[MetersPerSecond; 2]>),
}

impl Default for SpeedFunction {
    fn default() -> Self {
        Self::Base
    }
}

impl SpeedFunction {
    fn from_values(
        function_type: Option<&str>,
        upper_bound: Option<f64>,
        coef: Option<f64>,
        x: Option<Vec<f64>>,
        y: Option<Vec<f64>>,
    ) -> Result<Self> {
        match function_type {
            Some("Base") | None => Ok(Self::Base),
            Some("UpperBound") => {
                let upper_bound = MetersPerSecond::try_from(upper_bound.ok_or_else(|| {
                    anyhow!("Value `upper_bound` is mandatory when `type` is `\"UpperBound\"`")
                })?)
                .context("Value `upper_bound` does not satisfy the constraints")?;
                Ok(Self::UpperBound(upper_bound))
            }
            Some("Multiplicator") => {
                let coef = PositiveNum::try_from(coef.ok_or_else(|| {
                    anyhow!("Value `coef` is mandatory when `type` is `\"Multiplicator\"`")
                })?)
                .context("Value `coef` does not satisfy the constraints")?;
                Ok(Self::Multiplicator(coef))
            }
            Some("Piecewise") => {
                let x = x.ok_or_else(|| {
                    anyhow!("Value `x` is mandatory when `type` is `\"Piecewise\"`")
                })?;
                if x.is_empty() {
                    bail!("Value `x` is mandatory when `type` is `\"Piecewise\"`");
                }
                let y = y.ok_or_else(|| {
                    anyhow!("Value `y` is mandatory when `type` is `\"Piecewise\"`")
                })?;
                if y.is_empty() {
                    bail!("Value `y` is mandatory when `type` is `\"Piecewise\"`");
                }
                if !x.windows(2).all(|values| values[0] <= values[1]) {
                    bail!("The values in `x` must be sorted in increasing order");
                }
                if x.len() != y.len() {
                    bail!("`x` and `y` must have the same number of values");
                }
                let values = x
                    .into_iter()
                    .zip(y)
                    .map(|(x, y)| {
                        if let (Ok(x), Ok(y)) = (MetersPerSecond::try_from(x), MetersPerSecond::try_from(y)) {
                            Ok([x, y])
                        } else {
                            Err(anyhow!("The value of `x` or `y` does not satisfy the constraints: `x = {x}`, `y = {y}`"))
                        }
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Self::Piecewise(values))
            }
            Some(s) => Err(anyhow!("Unknown type: {s}")),
        }
    }

    /// Returns the effective speed given the baseline speed.
    ///
    /// If `self` is a piecewise-linear function and the baseline speed is out of bounds (the
    /// baseline speed is smaller than the smallest `x` or larger than the largest `x`), then the
    /// identity function is used.
    pub(crate) fn get_speed(&self, base_speed: MetersPerSecond) -> MetersPerSecond {
        match self {
            SpeedFunction::Base => base_speed,
            &SpeedFunction::UpperBound(upper_bound) => base_speed.min(upper_bound),
            &SpeedFunction::Multiplicator(mul) => base_speed * mul,
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
                        // values[i-1][0] < base_speed < values[i-1][1].
                        let num = (base_speed.to_num() - values[i - 1][0].to_num())
                            .assume_positive_unchecked();
                        let den = (values[i][0].to_num() - values[i - 1][0].to_num())
                            .assume_positive_unchecked();
                        // num < den so num / den is smaller than one.
                        let alpha = (num / den).assume_zero_one_unchecked();
                        values[i][1] * alpha + values[i - 1][1] * alpha.one_minus()
                    }
                }
            }
        }
    }
}

/// A road vehicle with a given headway, [PCE] and [SpeedFunction].
#[derive(Clone, Debug)]
pub struct Vehicle {
    /// Identifier of the vehicle.
    pub(crate) id: MetroId,
    /// Headway length of the vehicle, used to compute vehicle density on the edges.
    pub(crate) headway: NonNegativeMeters,
    /// Passenger car equivalent of the vehicle, used to compute bottleneck flow.
    pub(crate) pce: PCE,
    /// Speed function that gives the vehicle speed as a function of the edge base speed.
    pub(crate) speed_function: SpeedFunction,
    /// Set of edge indices that the vehicle is allowed to take (by default, all edges are allowed,
    /// unlesse specified in `restricted_edges`).
    pub(crate) allowed_edges: HashSet<OriginalEdgeId>,
    /// Set of edge indices that the vehicle cannot take. Note that `restricted_edges` is ignored
    /// if `allowed_edges` is specified.
    pub(crate) restricted_edges: HashSet<OriginalEdgeId>,
}

impl Vehicle {
    /// Creates a new vehicle with a given headway, [PCE] and [SpeedFunction].
    pub const fn new(
        id: i64,
        headway: NonNegativeMeters,
        pce: PCE,
        speed_function: SpeedFunction,
        allowed_edges: HashSet<OriginalEdgeId>,
        restricted_edges: HashSet<OriginalEdgeId>,
    ) -> Self {
        Vehicle {
            id: MetroId::Integer(id),
            headway,
            pce,
            speed_function,
            allowed_edges,
            restricted_edges,
        }
    }

    /// Returns `true` if the vehicle type has access to the given edge.
    pub(crate) fn can_access(&self, edge_id: OriginalEdgeId) -> bool {
        // Edge is allowed explicitly.
        let is_allowed = self.allowed_edges.contains(&edge_id);
        // Edge is not allowed but other edges are explicitly allowed.
        let is_not_allowed = !is_allowed && !self.allowed_edges.is_empty();
        // Edge is restricted explicitly.
        let is_restricted = self.restricted_edges.contains(&edge_id);
        is_allowed || (!is_restricted && !is_not_allowed)
    }
}

impl Vehicle {
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn from_values(
        id: MetroId,
        headway: Option<f64>,
        pce: Option<f64>,
        speed_function_type: Option<&str>,
        speed_function_upper_bound: Option<f64>,
        speed_function_coef: Option<f64>,
        speed_function_x: Option<Vec<f64>>,
        speed_function_y: Option<Vec<f64>>,
        allowed_edges: Option<Vec<OriginalEdgeId>>,
        restricted_edges: Option<Vec<OriginalEdgeId>>,
        edge_ids: &HashSet<OriginalEdgeId>,
    ) -> Result<Self> {
        let headway = NonNegativeMeters::try_from(
            headway.ok_or_else(|| anyhow!("Value `headway` is mandatory"))?,
        )
        .context("Value `headway` does not satisfy the constraints")?;
        let pce = PCE::try_from(pce.unwrap_or(1.0))
            .context("Value `pce` does not satisfy the constraints")?;
        if pce < PCE::ZERO {
            bail!("Value `pce` must be non-negative");
        }
        let speed_function = SpeedFunction::from_values(
            speed_function_type,
            speed_function_upper_bound,
            speed_function_coef,
            speed_function_x,
            speed_function_y,
        )
        .context("Failed to create speed function")?;
        let allowed_edges: HashSet<OriginalEdgeId> =
            allowed_edges.unwrap_or_default().into_iter().collect();
        if allowed_edges.difference(edge_ids).next().is_some() {
            bail!("The values in `allowed_edges` must be valid edge ids");
        }
        let restricted_edges: HashSet<OriginalEdgeId> =
            restricted_edges.unwrap_or_default().into_iter().collect();
        if restricted_edges.difference(edge_ids).next().is_some() {
            bail!("The values in `restricted_edges` must be valid edge ids");
        }
        Ok(Vehicle {
            id,
            headway,
            pce,
            speed_function,
            allowed_edges,
            restricted_edges,
        })
    }

    /// Returns the effective speed of the vehicle given the baseline speed on the road.
    pub(crate) fn get_speed(&self, base_speed: MetersPerSecond) -> MetersPerSecond {
        self.speed_function.get_speed(base_speed)
    }

    /// Returns `true` if the two given vehicles can share the same
    /// [RoadNetworkWeights](super::weights::RoadNetworkWeights).
    ///
    /// Two vehicle types can share the same weights if
    /// 1. They have the same speed function.
    /// 2. They have acces to the same edges (i.e., the sets of allowed edges and restricted edges
    ///    are equal).
    pub(crate) fn share_weights(&self, other: &Vehicle) -> bool {
        self.speed_function == other.speed_function
            && self.allowed_edges == other.allowed_edges
            && self.restricted_edges == other.restricted_edges
    }
}

/// Vehicle identifier.
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct VehicleIndex(usize);

impl VehicleIndex {
    /// Creates a new VehicleIndex.
    pub const fn new(x: usize) -> Self {
        VehicleIndex(x)
    }

    /// Returns the index of the VehicleIndex.
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Short version of `VehicleIndex::new`.
pub(crate) const fn vehicle_index(x: usize) -> VehicleIndex {
    VehicleIndex::new(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn speed_function_test() {
        let base = SpeedFunction::Base;
        assert_eq!(
            base.get_speed(MetersPerSecond::new_unchecked(1.0)),
            MetersPerSecond::new_unchecked(1.0)
        );
        assert_eq!(
            base.get_speed(MetersPerSecond::new_unchecked(130.0)),
            MetersPerSecond::new_unchecked(130.0)
        );
        assert_eq!(
            base.get_speed(MetersPerSecond::new_unchecked(50.0)),
            MetersPerSecond::new_unchecked(50.0)
        );
        assert_eq!(
            base.get_speed(MetersPerSecond::new_unchecked(70.0)),
            MetersPerSecond::new_unchecked(70.0)
        );

        let mult = SpeedFunction::Multiplicator(PositiveNum::new_unchecked(0.9));
        assert_eq!(
            mult.get_speed(MetersPerSecond::new_unchecked(1.0)),
            MetersPerSecond::new_unchecked(0.9)
        );
        assert_eq!(
            mult.get_speed(MetersPerSecond::new_unchecked(130.0)),
            MetersPerSecond::new_unchecked(130.0 * 0.9)
        );
        assert_eq!(
            mult.get_speed(MetersPerSecond::new_unchecked(50.0)),
            MetersPerSecond::new_unchecked(50.0 * 0.9)
        );
        assert_eq!(
            mult.get_speed(MetersPerSecond::new_unchecked(70.0)),
            MetersPerSecond::new_unchecked(70.0 * 0.9)
        );

        let func = SpeedFunction::Piecewise(vec![
            [
                MetersPerSecond::new_unchecked(1.0),
                MetersPerSecond::new_unchecked(1.0),
            ],
            [
                MetersPerSecond::new_unchecked(50.0),
                MetersPerSecond::new_unchecked(50.0),
            ],
            [
                MetersPerSecond::new_unchecked(90.0),
                MetersPerSecond::new_unchecked(80.0),
            ],
            [
                MetersPerSecond::new_unchecked(130.0),
                MetersPerSecond::new_unchecked(110.0),
            ],
        ]);
        assert_eq!(
            func.get_speed(MetersPerSecond::new_unchecked(1.0)),
            MetersPerSecond::new_unchecked(1.0)
        );
        assert_eq!(
            func.get_speed(MetersPerSecond::new_unchecked(130.0)),
            MetersPerSecond::new_unchecked(110.0)
        );
        assert_eq!(
            func.get_speed(MetersPerSecond::new_unchecked(50.0)),
            MetersPerSecond::new_unchecked(50.0)
        );
        assert_eq!(
            func.get_speed(MetersPerSecond::new_unchecked(70.0)),
            MetersPerSecond::new_unchecked(65.0)
        );
    }
}
