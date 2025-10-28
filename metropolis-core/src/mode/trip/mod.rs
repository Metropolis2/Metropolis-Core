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

//! Everything related to trips.
use std::ops::Deref;

use anyhow::{anyhow, bail, Context, Result};
use choice::{ChoiceModel, ContinuousChoiceModel};
use either::Either;
use enum_as_inner::EnumAsInner;
use hashbrown::HashSet;
use log::warn;
use num_traits::{clamp, ConstZero};
use once_cell::sync::OnceCell;
use petgraph::prelude::EdgeIndex;
use ttf::{PwlXYF, TTF};

use self::results::{RoadLegResults, TripResults};
use super::{ModeCallback, ModeResults};
use crate::mode::trip::results::{LegResults, LegTypeResults};
use crate::network::road_network::skim::{EAAllocation, RoadNetworkSkim, RoadNetworkSkims};
use crate::network::road_network::{
    OriginalEdgeId, OriginalNodeId, RoadNetworkPreprocessingData, RoadNetworkWeights,
};
use crate::progress_bar::MetroProgressBar;
use crate::schedule_utility::ScheduleUtility;
use crate::travel_utility::TravelUtility;
use crate::units::*;

pub mod event;
pub mod results;

// TODO This should be a parameter of the simulation.
const NB_INTERVALS: usize = 1500;

/// A leg of a trip.
#[derive(Clone, Debug)]
pub struct Leg {
    /// Id used when writing the results of the leg.
    pub(crate) id: MetroId,
    /// Type of the leg (road or virtual).
    pub(crate) class: LegType,
    /// Time spent at the stopping point of the leg, before starting the next leg (if any).
    pub(crate) stopping_time: NonNegativeSeconds,
    /// Travel utility for this specific leg (a function of the travel time for this leg).
    pub(crate) travel_utility: TravelUtility,
    /// Schedule utility at the stopping point (a function of the arrival time at the stopping
    /// point).
    pub(crate) schedule_utility: ScheduleUtility,
}

impl Leg {
    /// Creates a new [Leg].
    pub fn new(
        id: i64,
        class: LegType,
        stopping_time: NonNegativeSeconds,
        travel_utility: TravelUtility,
        schedule_utility: ScheduleUtility,
    ) -> Self {
        Self {
            id: MetroId::from(id),
            class,
            stopping_time,
            travel_utility,
            schedule_utility,
        }
    }

    /// Creates a `Leg` from input values.
    ///
    /// Returns an error if some values are invalid.
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn from_values(
        id: MetroId,
        class_type: Option<&str>,
        class_origin: Option<OriginalNodeId>,
        class_destination: Option<OriginalNodeId>,
        class_vehicle: Option<MetroId>,
        class_route: Option<Vec<OriginalEdgeId>>,
        class_travel_time: Option<f64>,
        stopping_time: Option<f64>,
        constant_utility: Option<f64>,
        alpha: Option<f64>,
        travel_utility_one: Option<f64>,
        travel_utility_two: Option<f64>,
        travel_utility_three: Option<f64>,
        travel_utility_four: Option<f64>,
        schedule_utility_type: Option<&str>,
        schedule_utility_tstar: Option<f64>,
        schedule_utility_beta: Option<f64>,
        schedule_utility_gamma: Option<f64>,
        schedule_utility_delta: Option<f64>,
    ) -> Result<Self> {
        let stopping_time = NonNegativeSeconds::try_from(stopping_time.unwrap_or(0.0))
            .context("Value `stopping_time` does not satisfy the constraints")?;
        let class = match class_type {
            Some("Road") => {
                let origin = class_origin.ok_or_else(|| {
                    anyhow!("Value `class.origin` is mandatory when `class.type` is `\"Road\"`")
                })?;
                let destination = class_destination.ok_or_else(|| {
                    anyhow!(
                        "Value `class.destination` is mandatory when `class.type` is `\"Road\"`"
                    )
                })?;
                let vehicle = class_vehicle.ok_or_else(|| {
                    anyhow!("Value `class.vehicle` is mandatory when `class.type` is `\"Road\"`")
                })?;
                LegType::Road(RoadLeg {
                    origin,
                    destination,
                    vehicle,
                    route: class_route,
                })
            }
            Some("Virtual") => {
                // We ensure that the travel time is a non-negative value before putting it in the
                // TTF as a AnySeconds.
                let tt = NonNegativeSeconds::try_from(class_travel_time.unwrap_or(0.0))
                    .context("Value `travel_time` does not satisfy the constraints")?;
                LegType::Virtual(TTF::Constant(AnySeconds::from(tt)))
            }
            Some(s) => bail!("Unknown value for `class.type`: {s}"),
            None => bail!("Value `class.type` is mandatory"),
        };
        let travel_utility = TravelUtility::from_values(
            constant_utility,
            alpha,
            travel_utility_one,
            travel_utility_two,
            travel_utility_three,
            travel_utility_four,
        )
        .context("Failed to create travel utility")?;
        let schedule_utility = ScheduleUtility::from_values(
            schedule_utility_type,
            schedule_utility_tstar,
            schedule_utility_beta,
            schedule_utility_gamma,
            schedule_utility_delta,
        )
        .context("Failed to create schedule utility")?;
        Ok(Leg {
            id,
            class,
            stopping_time,
            travel_utility,
            schedule_utility,
        })
    }

    /// Returns the travel and schedule utility of the leg, given the departure time and arrival
    /// time.
    fn get_utility_decomposition(
        &self,
        departure_time: NonNegativeSeconds,
        travel_time: NonNegativeSeconds,
    ) -> (Utility, Utility) {
        (
            self.travel_utility.get_travel_utility(travel_time),
            self.schedule_utility
                .get_utility(departure_time + travel_time),
        )
    }

    /// Returns the utility of the leg, given the departure time and travel time.
    fn get_utility_at(
        &self,
        departure_time: NonNegativeSeconds,
        travel_time: NonNegativeSeconds,
    ) -> Utility {
        let (u0, u1) = self.get_utility_decomposition(departure_time, travel_time);
        u0 + u1
    }

    /// Returns an initialized [LegResults] representing a virtual leg, given the expected departure
    /// time and arrival time.
    fn init_virtual_leg_results(&self) -> LegResults {
        LegResults {
            id: self.id,
            departure_time: NonNegativeSeconds::NAN,
            arrival_time: NonNegativeSeconds::NAN,
            travel_utility: Utility::NAN,
            schedule_utility: Utility::NAN,
            class: LegTypeResults::Virtual,
            departure_time_shift: None,
        }
    }

    /// Returns an initialized [LegResults] representing a road leg, given the expected departure
    /// time, the expected arrival time, the global free-flow travel time, and, optionally, the
    /// route, length and route free-flow travel time.
    fn init_road_leg_results(
        &self,
        departure_time: NonNegativeSeconds,
        arrival_time: NonNegativeSeconds,
        route: Option<Vec<EdgeIndex>>,
        length: Option<NonNegativeMeters>,
        route_free_flow_travel_time: Option<NonNegativeSeconds>,
        global_free_flow_travel_time: NonNegativeSeconds,
    ) -> LegResults {
        LegResults {
            id: self.id,
            departure_time: NonNegativeSeconds::NAN,
            arrival_time: NonNegativeSeconds::NAN,
            travel_utility: Utility::NAN,
            schedule_utility: Utility::NAN,
            class: LegTypeResults::Road(RoadLegResults::new(
                departure_time,
                arrival_time,
                route,
                length,
                route_free_flow_travel_time,
                global_free_flow_travel_time,
            )),
            departure_time_shift: None,
        }
    }
}

/// Enum for the different classes of legs.
#[derive(Clone, Debug, EnumAsInner)]
pub enum LegType {
    /// A leg with travel on the road.
    Road(RoadLeg),
    /// A virtual leg, with a fixed TTF, independent from the road network.
    Virtual(TTF<AnySeconds>),
}

/// A leg of a trip on the road network.
#[derive(Clone, Debug)]
pub struct RoadLeg {
    /// Origin node of the leg.
    pub(crate) origin: OriginalNodeId,
    /// Destination node of the leg.
    pub(crate) destination: OriginalNodeId,
    /// Vehicle used for the leg.
    pub(crate) vehicle: MetroId,
    /// Route to be followed by the vehicle to connect `origin` to `destination`.
    ///
    /// If `None`, the fastest route is chosen.
    pub(crate) route: Option<Vec<OriginalEdgeId>>,
}

impl RoadLeg {
    /// Creates a new [RoadLeg].
    pub fn new(origin: i64, destination: i64, vehicle: i64) -> Self {
        Self {
            origin: MetroId::Integer(origin),
            destination: MetroId::Integer(destination),
            vehicle: MetroId::Integer(vehicle),
            route: None,
        }
    }
}

/// Representation of the mode of transportation for a trip with one or more legs, consisting in
/// traveling on the road or virtually.
///
/// The trip is a sequence of legs, where each leg contains a travel part (either on the road, with
/// a given origin, destination and vehicle; or virtually, using a given travel-time function) and a
/// stopping part (with a fixed and given stopping time).
///
/// The destination of a leg does not have to be equal to the origin of the following leg, i.e.,
/// the agents are allowed to teleport from one node to another (and even change their vehicle).
///
/// The departure time from origin is the only choice variable (the departure time from any
/// following leg is equal to the arrival time at the stopping point of the previous leg, plus the
/// stopping time of the previous leg).
///
/// The route chosen for each (road) leg of the trip are the fastest route (in term of expected
/// travel time), given the expected departure time from the origin of the leg.
///
/// The arrival time at destination is the arrival time at the stopping point of the last leg, plus
/// the stopping time for this last leg.
///
/// The total trip utility is composed of:
///
/// - A function of departure time from origin: `origin_schedule_utility`.
/// - A function of total travel time of the trip (i.e., the sum of the travel time of each leg,
///   excluding stopping time): `total_travel_utility`.
/// - A function of arrival time at the stopping point for each leg: leg's `schedule_utility`.
/// - A function of travel time for each leg (excluding stopping time): leg's `travel_utility`.
/// - A function of arrival time at destination (which accounts for the stopping time of the last
///   leg): `destination_schedule_utility`.
///
/// When the utility for a given component is not specified, it is assumed to be null.
///
/// In practice, one of `total_travel_utility` or legs' `travel_utility` is usually null but this
/// is not enforced by the model.
#[derive(Clone, Debug)]
pub struct TravelingMode {
    /// Id of the mode, used in the output.
    pub(crate) id: MetroId,
    /// The legs of the trips.
    ///
    /// The full trip consists realizing this legs one after the other.
    pub(crate) legs: Vec<Leg>,
    /// Delay between the departure time of the trip and the start of the first leg.
    pub(crate) origin_delay: NonNegativeSeconds,
    /// Model used for the departure-time choice.
    pub(crate) departure_time_model: DepartureTimeModel,
    /// Total travel utility of the trip (a function of the total travel time of the trip).
    pub(crate) total_travel_utility: TravelUtility,
    /// Schedule utility at origin of the trip (a function of the departure time from origin).
    pub(crate) origin_schedule_utility: ScheduleUtility,
    /// Schedule utility at destination of the trip (a function of the arrival time at
    /// destination).
    pub(crate) destination_schedule_utility: ScheduleUtility,
    /// If `true`, the routes of the trip are computed during the pre-day model (faster).
    /// If `false`, they are computed during the within-day model (which means that the route for
    /// second and after legs is computed using the actual departure time, not the predicted one)..
    pub(crate) pre_compute_route: bool,
    /// Results of the pre-day model for this mode (when the mode is virtual only).
    pub(crate) choice: OnceCell<VirtualOnlyPreDayResults>,
}

impl TravelingMode {
    /// Creates a new [TravelingMode].
    pub fn new(
        id: i64,
        legs: Vec<Leg>,
        origin_delay: NonNegativeSeconds,
        departure_time_model: DepartureTimeModel,
        total_travel_utility: TravelUtility,
        origin_schedule_utility: ScheduleUtility,
        destination_schedule_utility: ScheduleUtility,
    ) -> Self {
        Self {
            id: MetroId::from(id),
            legs,
            origin_delay,
            departure_time_model,
            total_travel_utility,
            origin_schedule_utility,
            destination_schedule_utility,
            pre_compute_route: true,
            choice: OnceCell::new(),
        }
    }

    /// Returns the number of legs.
    pub fn nb_legs(&self) -> usize {
        self.legs.len()
    }

    /// Returns the number of road legs.
    pub fn nb_road_legs(&self) -> usize {
        self.iter_road_legs().count()
    }

    /// Returns the number of virtual legs.
    pub fn nb_virtual_legs(&self) -> usize {
        self.iter_virtual_legs().count()
    }

    /// Iterates over the legs of the trip.
    pub fn iter_legs(&'_ self) -> impl Iterator<Item = &'_ Leg> + '_ {
        self.legs.iter()
    }

    /// Iterates over the road legs of the trip.
    pub fn iter_road_legs(&'_ self) -> impl Iterator<Item = &'_ RoadLeg> + '_ {
        self.legs.iter().filter_map(|leg| {
            if let LegType::Road(road_leg) = &leg.class {
                Some(road_leg)
            } else {
                None
            }
        })
    }

    /// Iterates over the TTFs of the virtual legs of the trip.
    pub fn iter_virtual_legs(&'_ self) -> impl Iterator<Item = &'_ TTF<AnySeconds>> + '_ {
        self.legs.iter().filter_map(|leg| {
            if let LegType::Virtual(ttf) = &leg.class {
                Some(ttf)
            } else {
                None
            }
        })
    }
}

impl TravelingMode {
    /// Creates a `TravelingMode` from input values.
    ///
    /// Returns an error if some values are invalid.
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn from_values(
        id: MetroId,
        origin_delay: Option<f64>,
        dt_choice_type: Option<&str>,
        dt_choice_departure_time: Option<f64>,
        dt_choice_period: Option<Vec<f64>>,
        dt_choice_interval: Option<f64>,
        dt_choice_offset: Option<f64>,
        dt_choice_model_type: Option<&str>,
        dt_choice_model_u: Option<f64>,
        dt_choice_model_mu: Option<f64>,
        dt_choice_model_constants: Option<Vec<f64>>,
        constant_utility: Option<f64>,
        alpha: Option<f64>,
        total_travel_utility_one: Option<f64>,
        total_travel_utility_two: Option<f64>,
        total_travel_utility_three: Option<f64>,
        total_travel_utility_four: Option<f64>,
        origin_utility_type: Option<&str>,
        origin_utility_tstar: Option<f64>,
        origin_utility_beta: Option<f64>,
        origin_utility_gamma: Option<f64>,
        origin_utility_delta: Option<f64>,
        destination_utility_type: Option<&str>,
        destination_utility_tstar: Option<f64>,
        destination_utility_beta: Option<f64>,
        destination_utility_gamma: Option<f64>,
        destination_utility_delta: Option<f64>,
        pre_compute_route: Option<bool>,
        legs: Vec<Leg>,
    ) -> Result<Self> {
        debug_assert!(!legs.is_empty());
        let total_travel_utility = TravelUtility::from_values(
            constant_utility,
            alpha,
            total_travel_utility_one,
            total_travel_utility_two,
            total_travel_utility_three,
            total_travel_utility_four,
        )
        .context("Failed to create total travel utility")?;
        let origin_delay = NonNegativeSeconds::try_from(origin_delay.unwrap_or(0.0))
            .context("Value `origin_delay` does not satisfy the constraints")?;
        let departure_time_model = DepartureTimeModel::from_values(
            dt_choice_type,
            dt_choice_departure_time,
            dt_choice_period,
            dt_choice_interval,
            dt_choice_offset,
            dt_choice_model_type,
            dt_choice_model_u,
            dt_choice_model_mu,
            dt_choice_model_constants,
        )
        .context("Failed to create departure-time choice model")?;
        let origin_schedule_utility = ScheduleUtility::from_values(
            origin_utility_type,
            origin_utility_tstar,
            origin_utility_beta,
            origin_utility_gamma,
            origin_utility_delta,
        )
        .context("Failed to create origin schedule utility")?;
        let destination_schedule_utility = ScheduleUtility::from_values(
            destination_utility_type,
            destination_utility_tstar,
            destination_utility_beta,
            destination_utility_gamma,
            destination_utility_delta,
        )
        .context("Failed to create destination schedule utility")?;
        let pre_compute_route = pre_compute_route.unwrap_or(true);
        Ok(TravelingMode {
            id,
            origin_delay,
            departure_time_model,
            total_travel_utility,
            origin_schedule_utility,
            destination_schedule_utility,
            pre_compute_route,
            legs,
            choice: OnceCell::new(),
        })
    }
}

// Type for the TTFs of the legs of a trip.
//
// The TTFs can be either owned or be references.
type LegTTFs<'a> = Vec<LegTTF<'a>>;

struct LegTTF<'a>(Either<&'a TTF<AnySeconds>, TTF<AnySeconds>>);

impl Deref for LegTTF<'_> {
    type Target = TTF<AnySeconds>;
    fn deref(&self) -> &Self::Target {
        match &self.0 {
            Either::Left(referenced) => referenced,
            Either::Right(_) => self.0.as_ref().unwrap_right(),
        }
    }
}

impl TravelingMode {
    /// Returns a Vec of TTFs, corresponding to the TTF of each leg given the road-network skims.
    ///
    /// Returns an error if the road-network skims are invalid or if a leg is not feasible (the
    /// origin and destination are disconnected).
    fn get_leg_ttfs<'a>(
        &'a self,
        rn_weights: Option<&'a RoadNetworkWeights>,
        rn_skims: Option<&'a RoadNetworkSkims>,
        preprocess_data: Option<&RoadNetworkPreprocessingData>,
    ) -> Result<LegTTFs<'a>> {
        self.legs
            .iter()
            .map(|l| {
                match &l.class {
                    LegType::Road(road_leg) => {
                        let uid = preprocess_data
                            .expect("Found a road leg with no road-network preprocessing data")
                            .get_unique_vehicle_index(road_leg.vehicle);
                        if let Some(input_route) = road_leg.route.as_ref() {
                            // TODO: This code should be at the lower level (in weights or road
                            // network files).
                            let weights = &rn_weights
                                .expect("Found a road leg with no road-network weights")[uid];
                            let mut ttf = TTF::default();
                            for edge in input_route {
                                ttf = ttf.link(
                                    weights
                                        .weights()
                                        .get(edge)
                                        .ok_or_else(|| anyhow!("Invalid edge id: {}", edge))
                                        .with_context(|| {
                                            format!(
                                                "Invalid route given as input for alternative {}",
                                                self.id
                                            )
                                        })?,
                                );
                            }
                            Ok(LegTTF(Either::Right(ttf)))
                        } else {
                            let skims = rn_skims
                                .expect("Found a road leg with no road-network skims")[uid]
                                .as_ref()
                                .ok_or_else(|| {
                                    anyhow!("No skims were computed for the vehicle of this leg")
                                })?;
                            skims
                                .profile_query(road_leg.origin, road_leg.destination)?
                                .ok_or_else(|| {
                                    // No route from origin to destination.
                                    anyhow!(
                                    "No route on road network from origin {:?} to destination {:?}",
                                    road_leg.origin,
                                    road_leg.destination,
                                )
                                })
                                .map(|ttf| LegTTF(Either::Left(ttf)))
                        }
                    }
                    LegType::Virtual(ttf) => Ok(LegTTF(Either::Left(ttf))),
                }
            })
            .collect()
    }

    /// Returns the total utility of the trip given the departure time and the legs' TTFs.
    fn get_total_utility(
        &self,
        departure_time: NonNegativeSeconds,
        leg_ttfs: &LegTTFs<'_>,
    ) -> Utility {
        let mut current_time = departure_time + self.origin_delay;
        let mut total_travel_time = NonNegativeSeconds::default();
        let mut total_utility = self.origin_schedule_utility.get_utility(departure_time);
        for (leg_ttf, leg) in leg_ttfs.iter().zip(self.legs.iter()) {
            let travel_time =
                NonNegativeSeconds::try_from(leg_ttf.eval(AnySeconds::from(current_time)))
                    .expect("The travel time is negative");
            let utility = leg.get_utility_at(current_time, travel_time);
            total_utility += utility;
            current_time += travel_time;
            current_time += leg.stopping_time;
            total_travel_time += travel_time;
        }
        total_utility += self
            .total_travel_utility
            .get_travel_utility(total_travel_time);
        total_utility += self.destination_schedule_utility.get_utility(current_time);
        total_utility
    }

    /// Returns the total stopping time of the trip, i.e., the sum of the stopping time for each
    /// leg (plus the delay at origin).
    fn get_total_stopping_time(&self) -> NonNegativeSeconds {
        self.origin_delay
            + self
                .legs
                .iter()
                .map(|l| l.stopping_time)
                .sum::<NonNegativeSeconds>()
    }

    /// Returns a [PwlXYF] that yields the utility for each possible departure time, given the
    /// legs' TTFs.
    fn get_utility_function(
        &self,
        leg_ttfs: &LegTTFs<'_>,
        period: Interval,
    ) -> PwlXYF<AnySeconds, Utility, AnyNum> {
        let interval = period.length() / NB_INTERVALS;
        let tds: Vec<_> = std::iter::successors(Some(period.start()), |x| {
            Some(*x + NonNegativeSeconds::from(interval))
        })
        .take_while(|&x| x <= period.end())
        .collect();
        let mut utilities = vec![Utility::ZERO; tds.len()];
        // Add schedule utility at origin.
        utilities
            .iter_mut()
            .zip(tds.iter())
            .for_each(|(u, &td)| *u += self.origin_schedule_utility.get_utility(td));
        let mut current_times = tds.clone();
        // Add origin delay.
        current_times
            .iter_mut()
            .for_each(|t| *t += self.origin_delay);
        for (leg_ttf, leg) in leg_ttfs.iter().zip(self.legs.iter()) {
            // Add the leg-specific travel-time utility and schedule utility, and update the
            // current times.
            utilities
                .iter_mut()
                .zip(current_times.iter_mut())
                .for_each(|(u, t)| {
                    let tt = NonNegativeSeconds::try_from(leg_ttf.eval(AnySeconds::from(*t)))
                        .expect("The travel time is negative");
                    // Update the current time.
                    *t += tt;
                    // Increase the utility for the associated departure time.
                    *u += leg.travel_utility.get_travel_utility(tt)
                        + leg.schedule_utility.get_utility(*t);
                    // Add the stopping time.
                    *t += leg.stopping_time;
                });
        }
        // Add schedule utility at destination.
        utilities
            .iter_mut()
            .zip(current_times.iter())
            .for_each(|(u, &ta)| *u += self.destination_schedule_utility.get_utility(ta));
        // Add total travel utility (stopping time needs to be excluded).
        utilities
            .iter_mut()
            .zip(current_times)
            .zip(tds)
            .for_each(|((u, ta), td)| {
                // total stopping time is always larger that
                let tot_tt = ta
                    .sub_unchecked(td)
                    .sub_unchecked(self.get_total_stopping_time());
                *u += self.total_travel_utility.get_travel_utility(tot_tt)
            });
        PwlXYF::from_values(utilities, period.start().into(), interval.into())
    }

    /// Returns `true` if the [TravelingMode] is composed of virtual legs only.
    fn is_virtual_only(&self) -> bool {
        self.legs
            .iter()
            .all(|l| matches!(l.class, LegType::Virtual(_)))
    }

    /// Returns the trip results given the departure time from origin, for a virtual-only trip.
    ///
    /// *Panics* if the trip is not virtual only.
    fn get_trip_results_for_virtual_only(
        &self,
        departure_time: NonNegativeSeconds,
        expected_utility: Utility,
    ) -> TripResults {
        assert!(
            self.is_virtual_only(),
            "The function `get_trip_results_for_virtual_only` is only available for virtual only trips"
        );
        let mut leg_results = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time + self.origin_delay;
        let mut utility = self.origin_schedule_utility.get_utility(departure_time);
        let mut total_travel_time = NonNegativeSeconds::ZERO;
        for leg in self.legs.iter() {
            let ttf = if let LegType::Virtual(ttf) = &leg.class {
                ttf
            } else {
                // All legs are virtual here.
                unreachable!()
            };
            // We can assume that the travel time is non-negative since this was checked when
            // importing the virtual leg.
            let travel_time = ttf
                .eval(current_time.into())
                .assume_non_negative_unchecked();
            let arrival_time = current_time + travel_time;
            total_travel_time += travel_time;
            let travel_utility = leg.travel_utility.get_travel_utility(travel_time);
            let schedule_utility = leg.schedule_utility.get_utility(arrival_time);
            let lr = LegResults {
                id: leg.id,
                departure_time: current_time,
                arrival_time: current_time + travel_time,
                travel_utility,
                schedule_utility,
                class: LegTypeResults::Virtual,
                departure_time_shift: None,
            };
            leg_results.push(lr);
            current_time = arrival_time + leg.stopping_time;
            utility += travel_utility + schedule_utility;
        }
        utility += self
            .total_travel_utility
            .get_travel_utility(total_travel_time);
        TripResults {
            legs: leg_results,
            departure_time,
            arrival_time: current_time,
            total_travel_time,
            utility,
            expected_utility,
            virtual_only: true,
            departure_time_shift: None,
        }
    }

    /// Returns the initialized trip results given the departure time from origin.
    ///
    /// Not all values of the trip results are filled. Some values should be filled in the
    /// within-day model.
    fn init_trip_results_without_route(
        &self,
        departure_time: NonNegativeSeconds,
        expected_utility: Utility,
        leg_ttfs: &LegTTFs<'_>,
        preprocess_data: Option<&RoadNetworkPreprocessingData>,
        weights: Option<&RoadNetworkWeights>,
    ) -> TripResults {
        let mut leg_results = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time + self.origin_delay;
        for (leg, leg_ttf) in self.iter_legs().zip(leg_ttfs.iter()) {
            let travel_time = NonNegativeSeconds::try_from(leg_ttf.eval(current_time.into()))
                .expect("The travel time is negative");
            let arrival_time = current_time + travel_time;
            let leg_result = match &leg.class {
                LegType::Road(road_leg) => {
                    let preprocess_data = preprocess_data
                        .expect("Got a road leg without road-network preprocessing data");
                    let uid = preprocess_data.get_unique_vehicle_index(road_leg.vehicle);
                    let (arrival_time, route_opt, global_free_flow_travel_time) =
                        if let Some(input_route) = road_leg.route.as_ref() {
                            // A route is given as input so the route is `pre-computed` anyway.
                            let vehicle_weights = &weights
                                .expect("Got a road leg but there is no road network weights.")
                                [uid];
                            let mut t = current_time;
                            let mut route = Vec::with_capacity(input_route.len());
                            for edge in input_route {
                                t = t + NonNegativeSeconds::try_from(
                                    vehicle_weights.weights()[edge].eval(t.into()),
                                )
                                .expect("The travel time is negative");
                                route.push(crate::network::road_network::edge_index_of(*edge));
                            }
                            let global_free_flow_travel_time =
                                crate::network::road_network::route_free_flow_travel_time(
                                    route.iter().copied(),
                                    road_leg.vehicle,
                                );
                            (t, Some(route), global_free_flow_travel_time)
                        } else {
                            let global_free_flow_travel_time = *preprocess_data
                            .free_flow_travel_times_of_unique_vehicle(uid)
                            .get(&(road_leg.origin, road_leg.destination))
                            .expect(
                                "The free flow travel time of the OD pair has not been computed.",
                            );
                            (arrival_time, None, global_free_flow_travel_time)
                        };
                    leg.init_road_leg_results(
                        current_time,
                        arrival_time,
                        route_opt,
                        None,
                        None,
                        global_free_flow_travel_time,
                    )
                }
                LegType::Virtual(_) => leg.init_virtual_leg_results(),
            };
            leg_results.push(leg_result);
            current_time = arrival_time + leg.stopping_time;
        }
        TripResults::new(leg_results, departure_time, expected_utility, false)
    }

    /// Returns the pre-day choice for this mode.
    ///
    /// If the [TravelingMode] is virtual only, then the pre-day choice is always the same and it
    /// is computed only the first time this function is called.
    pub fn get_pre_day_choice<'a: 'b, 'b>(
        &'a self,
        rn_weights: Option<&'b RoadNetworkWeights>,
        rn_skims: Option<&'b RoadNetworkSkims>,
        preprocess_data: Option<&'b RoadNetworkPreprocessingData>,
        progress_bar: MetroProgressBar,
        alloc: &mut EAAllocation,
    ) -> Result<(Utility, ModeCallback<'b>)> {
        if let Some(choice) = self.choice.get() {
            // The TravelingMode is virtual only and the pre-day choices were already computed.
            return Ok(choice.to_expected_utility_and_mode_callback());
        }
        self.make_pre_day_choice(rn_weights, rn_skims, preprocess_data, progress_bar, alloc)
    }

    /// Computes the pre-day choice for a mode with constant departure time.
    ///
    /// In this case, the profile queries were not computed so the expected utility must be
    /// computed by running earliest-arrival queries or using the input routes.
    fn constant_departure_time_pre_day_choice<'a: 'b, 'b>(
        &'a self,
        departure_time: NonNegativeSeconds,
        rn_weights: Option<&'b RoadNetworkWeights>,
        rn_skims: Option<&'b RoadNetworkSkims>,
        preprocess_data: Option<&'b RoadNetworkPreprocessingData>,
        progress_bar: MetroProgressBar,
        alloc: &mut EAAllocation,
    ) -> Result<(Utility, ModeCallback<'b>)> {
        debug_assert!(self.departure_time_model.is_constant());
        let mut leg_results = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time + self.origin_delay;
        let mut total_travel_time = NonNegativeSeconds::default();
        let mut expected_utility = self.origin_schedule_utility.get_utility(departure_time);
        for leg in self.iter_legs() {
            let (arrival_time, leg_result) = match &leg.class {
                LegType::Road(road_leg) => {
                    let uid = preprocess_data
                        .expect("Got a road leg but there is no road network preprocess data.")
                        .get_unique_vehicle_index(road_leg.vehicle);
                    let (arrival_time, route, global_free_flow_travel_time) =
                        if let Some(input_route) = road_leg.route.as_ref() {
                            // Evaluate the travel time of the input route.
                            let vehicle_weights = &rn_weights
                                .expect("Got a road leg but there is no road network weights.")
                                [uid];
                            let mut t = current_time;
                            let mut route = Vec::with_capacity(input_route.len());
                            for edge in input_route {
                                t = t + NonNegativeSeconds::try_from(
                                    vehicle_weights.weights()[edge].eval(AnySeconds::from(t)),
                                )
                                .expect("The travel time is negative");
                                route.push(crate::network::road_network::edge_index_of(*edge));
                            }
                            let global_free_flow_travel_time =
                                crate::network::road_network::route_free_flow_travel_time(
                                    route.iter().copied(),
                                    road_leg.vehicle,
                                );
                            (t, route, global_free_flow_travel_time)
                        } else {
                            // Run an earliest-arrival time query to get the travel time and fastest
                            // path.
                            // TODO. The route is not needed if pre_compute_route is false, only
                            // the arrival time is needed.
                            let vehicle_skims = rn_skims
                                .expect("Got a road leg but there is no road network skims.")[uid]
                                .as_ref()
                                .expect("Road network skims are empty.");
                            let (arrival_time, route) = get_arrival_time_and_route(
                                road_leg,
                                current_time,
                                vehicle_skims,
                                progress_bar.clone(),
                                alloc,
                            )?;
                            let global_free_flow_travel_time = *preprocess_data
                            .expect("Got a road leg but there is no road network preprocess data.")
                            .free_flow_travel_times_of_unique_vehicle(uid)
                            .get(&(road_leg.origin, road_leg.destination))
                            .expect(
                                "The free flow travel time of the OD pair has not been computed.",
                            );
                            (arrival_time, route, global_free_flow_travel_time)
                        };
                    let leg_result = if self.pre_compute_route {
                        // Compute the route free-flow travel time and length.
                        let length =
                            crate::network::road_network::route_length(route.iter().copied());
                        let route_free_flow_travel_time =
                            crate::network::road_network::route_free_flow_travel_time(
                                route.iter().copied(),
                                road_leg.vehicle,
                            );
                        leg.init_road_leg_results(
                            current_time,
                            arrival_time,
                            Some(route),
                            Some(length),
                            Some(route_free_flow_travel_time),
                            global_free_flow_travel_time,
                        )
                    } else {
                        leg.init_road_leg_results(
                            current_time,
                            arrival_time,
                            None,
                            None,
                            None,
                            global_free_flow_travel_time,
                        )
                    };
                    (arrival_time, leg_result)
                }
                LegType::Virtual(ttf) => (
                    current_time
                        + ttf
                            .eval(AnySeconds::from(current_time))
                            .assume_non_negative_unchecked(),
                    leg.init_virtual_leg_results(),
                ),
            };
            let travel_time = arrival_time.sub_unchecked(current_time);
            expected_utility += leg.get_utility_at(current_time, travel_time);
            total_travel_time += travel_time;
            leg_results.push(leg_result);
            current_time = arrival_time + leg.stopping_time;
        }
        expected_utility += self
            .total_travel_utility
            .get_travel_utility(total_travel_time);
        expected_utility += self.destination_schedule_utility.get_utility(current_time);
        let callback = move |_| {
            Ok(ModeResults::Trip(TripResults::new(
                leg_results,
                departure_time,
                expected_utility,
                false,
            )))
        };
        Ok((expected_utility, Box::new(callback)))
    }

    /// Computes the pre-day choice for this mode.
    ///
    /// Given the expected [RoadNetworkSkims] and the [ScheduleUtility], this returns a tuple with
    /// the expected utility from the departure-time choice model and a [ModeCallback] function.
    ///
    /// The departure time and route chosen are only computed when the callback function is called.
    ///
    /// *Panics* if the function is called with only virtual legs and with a non-empty OnceCell.
    fn make_pre_day_choice<'a: 'b, 'b>(
        &'a self,
        rn_weights: Option<&'b RoadNetworkWeights>,
        rn_skims: Option<&'b RoadNetworkSkims>,
        preprocess_data: Option<&'b RoadNetworkPreprocessingData>,
        progress_bar: MetroProgressBar,
        alloc: &mut EAAllocation,
    ) -> Result<(Utility, ModeCallback<'b>)> {
        if let &DepartureTimeModel::Constant(departure_time) = &self.departure_time_model {
            return self.constant_departure_time_pre_day_choice(
                departure_time,
                rn_weights,
                rn_skims,
                preprocess_data,
                progress_bar,
                alloc,
            );
        }
        let leg_ttfs = self.get_leg_ttfs(rn_weights, rn_skims, preprocess_data)?;
        let (expected_utility, time_callback) = match &self.departure_time_model {
            DepartureTimeModel::Discrete {
                period,
                interval,
                offset,
                choice_model,
            } => {
                let period = period.unwrap_or_else(crate::parameters::period);
                let half_interval = interval.half();
                let dt_values_iter =
                    std::iter::successors(Some(period.start() + half_interval), |t| {
                        Some(*t + *interval)
                    })
                    .take_while(|t| *t < period.end());
                let utilities: Vec<_> = dt_values_iter
                    .map(|td| self.get_total_utility(td, &leg_ttfs))
                    .collect();
                let (chosen_id, expected_utility) =
                    choice_model.get_choice(&utilities).with_context(|| {
                        format!(
                            "Failed to select departure time for alternative {}",
                            self.id
                        )
                    })?;
                let departure_time = NonNegativeSeconds::try_from(clamp(
                    AnySeconds::from(period.start() + half_interval + *interval * chosen_id)
                        + *offset,
                    period.start().into(),
                    period.end().into(),
                ))
                .unwrap();
                let time_callback: Box<dyn FnOnce() -> NonNegativeSeconds> =
                    Box::new(move || departure_time);
                (expected_utility, time_callback)
            }
            DepartureTimeModel::Continuous {
                period: period_opt,
                choice_model,
            } => {
                let period = period_opt.unwrap_or(crate::parameters::period());
                let utilities = self.get_utility_function(&leg_ttfs, period);
                let (time_callback, expected_utility) =
                    choice_model.get_choice(utilities).with_context(|| {
                        format!(
                            "Failed to select departure time for alternative {}",
                            self.id
                        )
                    })?;
                let time_callback: Box<dyn FnOnce() -> NonNegativeSeconds> = Box::new(move || {
                    NonNegativeSeconds::try_from(time_callback())
                        .expect("The travel time is negative")
                });
                (expected_utility, time_callback)
            }
            &DepartureTimeModel::Constant(_) => {
                unreachable!()
            }
        };
        if self.is_virtual_only() {
            let departure_time = time_callback();
            let virtual_results = self
                .choice
                .try_insert(VirtualOnlyPreDayResults {
                    expected_utility,
                    trip_results: self
                        .get_trip_results_for_virtual_only(departure_time, expected_utility),
                })
                .unwrap();
            return Ok(virtual_results.to_expected_utility_and_mode_callback());
        }
        let callback = move |alloc| {
            let departure_time = time_callback();
            if self.pre_compute_route {
                Ok(ModeResults::Trip(self.init_trip_results_with_route(
                    departure_time,
                    expected_utility,
                    preprocess_data,
                    rn_weights,
                    rn_skims,
                    progress_bar,
                    alloc,
                )?))
            } else {
                Ok(ModeResults::Trip(self.init_trip_results_without_route(
                    departure_time,
                    expected_utility,
                    &leg_ttfs,
                    preprocess_data,
                    rn_weights,
                )))
            }
        };
        Ok((expected_utility, Box::new(callback)))
    }

    /// Returns the initialized trip results given the departure time from origin.
    ///
    /// Not all values of the trip results are filled. Some values should be filled in the
    /// within-day model.
    #[expect(clippy::too_many_arguments)]
    fn init_trip_results_with_route(
        &self,
        departure_time: NonNegativeSeconds,
        expected_utility: Utility,
        preprocess_data: Option<&RoadNetworkPreprocessingData>,
        weights: Option<&RoadNetworkWeights>,
        skims: Option<&RoadNetworkSkims>,
        progress_bar: MetroProgressBar,
        alloc: &mut EAAllocation,
    ) -> Result<TripResults> {
        let mut leg_results = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time + self.origin_delay;
        for leg in self.iter_legs() {
            let (arrival_time, leg_result) = match &leg.class {
                LegType::Road(road_leg) => {
                    let uid = preprocess_data
                        .expect("Got a road leg but there is no road network preprocess data.")
                        .get_unique_vehicle_index(road_leg.vehicle);
                    let (arrival_time, route, global_free_flow_travel_time) =
                        if let Some(input_route) = road_leg.route.as_ref() {
                            let vehicle_weights = &weights
                                .expect("Got a road leg but there is no road network weights.")
                                [uid];
                            let mut t = current_time;
                            let mut route = Vec::with_capacity(input_route.len());
                            for edge in input_route {
                                t = t + NonNegativeSeconds::try_from(
                                    vehicle_weights.weights()[edge].eval(AnySeconds::from(t)),
                                )
                                .expect("The travel time is negative");
                                route.push(crate::network::road_network::edge_index_of(*edge));
                            }
                            let global_free_flow_travel_time =
                                crate::network::road_network::route_free_flow_travel_time(
                                    route.iter().copied(),
                                    road_leg.vehicle,
                                );
                            (t, route, global_free_flow_travel_time)
                        } else {
                            let vehicle_skims = skims
                                .expect("Got a road leg but there is no road network skims.")[uid]
                                .as_ref()
                                .expect("Road network skims are empty.");
                            let (arrival_time, route) = get_arrival_time_and_route(
                                road_leg,
                                current_time,
                                vehicle_skims,
                                progress_bar.clone(),
                                alloc,
                            )?;
                            let global_free_flow_travel_time = *preprocess_data
                            .expect("Got a road leg but there is no road network preprocess data.")
                            .free_flow_travel_times_of_unique_vehicle(uid)
                            .get(&(road_leg.origin, road_leg.destination))
                            .expect(
                                "The free flow travel time of the OD pair has not been computed.",
                            );
                            (arrival_time, route, global_free_flow_travel_time)
                        };
                    // Compute the route free-flow travel time and length.
                    let length = crate::network::road_network::route_length(route.iter().copied());
                    let route_free_flow_travel_time =
                        crate::network::road_network::route_free_flow_travel_time(
                            route.iter().copied(),
                            road_leg.vehicle,
                        );
                    let leg_result = leg.init_road_leg_results(
                        current_time,
                        arrival_time,
                        Some(route),
                        Some(length),
                        Some(route_free_flow_travel_time),
                        global_free_flow_travel_time,
                    );
                    (arrival_time, leg_result)
                }
                LegType::Virtual(ttf) => (
                    current_time
                        + ttf
                            .eval(AnySeconds::from(current_time))
                            .assume_non_negative_unchecked(),
                    leg.init_virtual_leg_results(),
                ),
            };
            leg_results.push(leg_result);
            current_time = arrival_time + leg.stopping_time;
        }
        Ok(TripResults::new(
            leg_results,
            departure_time,
            expected_utility,
            false,
        ))
    }
}

/// Expected utility and trip results for a [TravelingMode] with only virtual legs.
#[derive(Clone, Debug)]
pub(crate) struct VirtualOnlyPreDayResults {
    expected_utility: Utility,
    trip_results: TripResults,
}

impl VirtualOnlyPreDayResults {
    /// Returns a tuple with the expected utility and a [ModeCallback].
    fn to_expected_utility_and_mode_callback(&'_ self) -> (Utility, ModeCallback<'_>) {
        let callback = move |_| Ok(ModeResults::Trip(self.trip_results.clone()));
        (self.expected_utility, Box::new(callback))
    }
}

/// Model used to compute the chosen departure time.
#[derive(Clone, Debug, EnumAsInner)]
pub enum DepartureTimeModel {
    /// The departure time is always equal to the given value.
    Constant(NonNegativeSeconds),
    /// The departure time is chosen among a finite number of values.
    Discrete {
        /// Period in which the departure time is chosen.
        ///
        /// If `None`, the simulation period is used.
        period: Option<Interval>,
        /// Time between two departure-time interval.
        interval: NonNegativeSeconds,
        /// Offset time added to the chosen departure-time value (can be negative).
        offset: AnySeconds,
        /// Discrete choice model.
        choice_model: ChoiceModel<Utility>,
    },
    /// The departure time is chosen according to a continuous choice model.
    Continuous {
        /// Period in which the departure time is chosen.
        ///
        /// If `None`, the simulation period is used.
        period: Option<Interval>,
        /// Continuous choice model.
        choice_model: ContinuousChoiceModel,
    },
}

impl DepartureTimeModel {
    /// Returns `true` if the departure-time model requires pre-computing the profile query for the
    /// trips' origin-destination pairs.
    pub(crate) fn requires_profile_query(&self) -> bool {
        match self {
            Self::Constant(_) => false,
            Self::Discrete { .. } => true,
            Self::Continuous { .. } => true,
        }
    }

    #[expect(clippy::too_many_arguments)]
    pub(crate) fn from_values(
        model_type: Option<&str>,
        departure_time: Option<f64>,
        period: Option<Vec<f64>>,
        interval: Option<f64>,
        offset: Option<f64>,
        choice_model_type: Option<&str>,
        choice_model_u: Option<f64>,
        choice_model_mu: Option<f64>,
        choice_model_constants: Option<Vec<f64>>,
    ) -> Result<Self> {
        fn period_as_interval(period: Vec<f64>) -> Result<Interval> {
            match period.len() {
                2 => {
                    Interval::try_from([period[0], period[1]]).context("Value `period` is invalid")
                }
                _ => Err(anyhow!(
                    "Value `period` must be a List with 2 values, got `{:?}`",
                    period
                )),
            }
        }
        match model_type {
            Some("Constant") => {
                let dt = NonNegativeSeconds::try_from(departure_time.ok_or_else(|| {
                    anyhow!("Value `departure_time` is mandatory when `type` is `\"Constant\"`")
                })?)
                .context("Value `departure_time` does not satisfy the constraints")?;
                Ok(Self::Constant(dt))
            }
            Some("Discrete") => {
                let period = period.map(period_as_interval).transpose()?;
                let interval = NonNegativeSeconds::try_from(interval.ok_or_else(|| {
                    anyhow!("Value `interval` is mandatory when `type` is `\"Discrete\"`")
                })?)
                .context("Value `interval` does not satisfy the constraints")?;
                let choice_model = ChoiceModel::from_values(
                    choice_model_type,
                    choice_model_u,
                    choice_model_mu,
                    choice_model_constants,
                )
                .context("Failed to create a discrete choice model")?;
                let offset = AnySeconds::try_from(offset.unwrap_or(0.0))
                    .context("Value `offset` does not satisfy the constraints")?;
                if offset < -AnySeconds::from(interval.half())
                    || offset > AnySeconds::from(interval.half())
                {
                    warn!(
                        "Value `offset` ({}) is larger or smaller than the half interval ({})",
                        f64::from(offset),
                        f64::from(interval.half())
                    );
                }
                Ok(Self::Discrete {
                    period,
                    interval,
                    offset,
                    choice_model,
                })
            }
            Some("Continuous") => {
                let period = period.map(period_as_interval).transpose()?;
                let choice_model = ContinuousChoiceModel::from_values(
                    choice_model_type,
                    choice_model_u,
                    choice_model_mu,
                )
                .context("Failed to create a continuous choice model")?;
                Ok(Self::Continuous {
                    period,
                    choice_model,
                })
            }
            Some(s) => Err(anyhow!("Unknown `type`: {s}")),
            None => Err(anyhow!("Value `type` is mandatory")),
        }
    }
}

/// Run an earliest arrival query on the [RoadNetworkSkim] to get the arrival time and route, for a
/// given origin, destination and departure time.
///
/// Return an error if the destination cannot be reached with the given departure time from origin.
fn get_arrival_time_and_route(
    leg: &RoadLeg,
    departure_time: NonNegativeSeconds,
    skims: &RoadNetworkSkim,
    progress_bar: MetroProgressBar,
    alloc: &mut EAAllocation,
) -> Result<(NonNegativeSeconds, Vec<EdgeIndex>)> {
    if let Some((arrival_time, route)) = skims.earliest_arrival_query(
        leg.origin,
        leg.destination,
        AnySeconds::from(departure_time),
        alloc,
    )? {
        if cfg!(debug_assertions) {
            // Check if there is a loop in the route.
            let n = route.iter().collect::<HashSet<_>>().len();
            if n != route.len() {
                progress_bar.suspend(|| {
                    warn!(
                        "Found a loop in route from {} to {} at time {}",
                        leg.origin, leg.destination, departure_time
                    );
                })
            }
        }
        let arrival_time = NonNegativeSeconds::try_from(arrival_time).with_context(|| {
            format!("Got a negative travel time from the earliest-arrival query: {arrival_time}")
        })?;
        Ok((arrival_time, route))
    } else {
        Err(anyhow!(
            "No route from {:?} to {:?} at departure time {:?}",
            leg.origin,
            leg.destination,
            departure_time,
        ))
    }
}
