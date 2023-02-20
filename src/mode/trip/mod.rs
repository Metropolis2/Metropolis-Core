// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to trips.
use std::collections::BinaryHeap;

use anyhow::{anyhow, Result};
use choice::ContinuousChoiceModel;
use enum_as_inner::EnumAsInner;
use num_traits::{Float, Zero};
use once_cell::sync::OnceCell;
use petgraph::graph::NodeIndex;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::{PwlXYF, TTFNum, TTF};

use self::results::{RoadLegResults, TripResults};
use super::{ModeCallback, ModeResults};
use crate::mode::trip::results::{LegResults, LegTypeResults};
use crate::network::road_network::skim::RoadNetworkSkims;
use crate::network::road_network::vehicle::VehicleIndex;
use crate::network::road_network::RoadNetworkPreprocessingData;
use crate::schedule_utility::ScheduleUtility;
use crate::schema::NodeIndexDef;
use crate::travel_utility::TravelUtility;
use crate::units::{Interval, NoUnit, Time, Utility};

pub mod event;
pub mod results;

/// A leg of a trip.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
pub struct Leg<T> {
    /// Type of the leg (road or virtual).
    pub(crate) class: LegType<T>,
    /// Time spent at the stopping point of the leg, before starting the next leg (if any).
    #[serde(default)]
    pub(crate) stopping_time: Time<T>,
    /// Travel utility for this specific leg (a function of the travel time for this leg).
    #[serde(default)]
    pub(crate) travel_utility: TravelUtility<T>,
    /// Schedule utility at the stopping point (a function of the arrival time at the stopping
    /// point).
    #[serde(default)]
    pub(crate) schedule_utility: ScheduleUtility<T>,
}

impl<T: TTFNum> Leg<T> {
    /// Creates a new [Leg].
    pub fn new(
        class: LegType<T>,
        stopping_time: Time<T>,
        travel_utility: TravelUtility<T>,
        schedule_utility: ScheduleUtility<T>,
    ) -> Self {
        Self {
            class,
            stopping_time,
            travel_utility,
            schedule_utility,
        }
    }

    /// Returns the travel and schedule utility of the leg, given the departure time and arrival
    /// time.
    fn get_utility_decomposition(
        &self,
        departure_time: Time<T>,
        travel_time: Time<T>,
    ) -> (Utility<T>, Utility<T>) {
        (
            self.travel_utility.get_travel_utility(travel_time),
            self.schedule_utility
                .get_utility(departure_time + travel_time),
        )
    }

    /// Returns the utility of the leg, given the departure time and travel time.
    fn get_utility_at(&self, departure_time: Time<T>, travel_time: Time<T>) -> Utility<T> {
        let (u0, u1) = self.get_utility_decomposition(departure_time, travel_time);
        u0 + u1
    }

    /// Returns an initialized [LegResults], given the expected departure time and arrival time for
    /// the leg.
    fn init_leg_results(&self, departure_time: Time<T>, arrival_time: Time<T>) -> LegResults<T> {
        LegResults {
            departure_time: Time::nan(),
            arrival_time: Time::nan(),
            travel_utility: Utility::nan(),
            schedule_utility: Utility::nan(),
            class: self
                .class
                .init_leg_type_results(departure_time, arrival_time),
        }
    }
}

/// Enum for the different classes of legs.
#[derive(Clone, Debug, EnumAsInner, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
#[serde(bound = "T: TTFNum")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
pub enum LegType<T> {
    /// A leg with travel on the road.
    Road(RoadLeg),
    /// A virtual leg, with a fixed TTF, independent from the road network.
    Virtual(TTF<Time<T>>),
}

impl<T: TTFNum> LegType<T> {
    /// Returns an initialized [LegTypeResults], given the expected departure time and arrival time
    /// for the leg.
    fn init_leg_type_results(
        &self,
        departure_time: Time<T>,
        arrival_time: Time<T>,
    ) -> LegTypeResults<T> {
        match self {
            Self::Road(_) => {
                LegTypeResults::Road(RoadLegResults::new(departure_time, arrival_time))
            }
            Self::Virtual(_) => LegTypeResults::Virtual,
        }
    }
}

/// A leg of a trip on the road network.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub struct RoadLeg {
    /// Origin node of the leg.
    #[schemars(with = "NodeIndexDef")]
    pub(crate) origin: NodeIndex,
    /// Destination node of the leg.
    #[schemars(with = "NodeIndexDef")]
    pub(crate) destination: NodeIndex,
    /// Vehicle used for the leg.
    pub(crate) vehicle: VehicleIndex,
}

impl RoadLeg {
    /// Creates a new [RoadLeg].
    pub fn new(origin: NodeIndex, destination: NodeIndex, vehicle: VehicleIndex) -> Self {
        Self {
            origin,
            destination,
            vehicle,
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
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
pub struct TravelingMode<T> {
    /// The legs of the trips.
    ///
    /// The full trip consists realizing this legs one after the other.
    #[validate(length(min = 1))]
    pub(crate) legs: Vec<Leg<T>>,
    /// Delay between the departure time of the trip and the start of the first leg.
    #[serde(default)]
    pub(crate) origin_delay: Time<T>,
    /// Model used for the departure-time choice.
    pub(crate) departure_time_model: DepartureTimeModel<T>,
    /// Total travel utility of the trip (a function of the total travel time of the trip).
    #[serde(default)]
    pub(crate) total_travel_utility: TravelUtility<T>,
    /// Schedule utility at origin of the trip (a function of the departure time from origin).
    #[serde(default)]
    pub(crate) origin_schedule_utility: ScheduleUtility<T>,
    /// Schedule utility at destination of the trip (a function of the arrival time at
    /// destination).
    #[serde(default)]
    pub(crate) destination_schedule_utility: ScheduleUtility<T>,
    /// Results of the pre-day model for this mode (when the mode is virtual only).
    #[serde(skip)]
    pub(crate) choice: OnceCell<VirtualOnlyPreDayResults<T>>,
}

impl<T> TravelingMode<T> {
    /// Creates a new [TravelingMode].
    pub fn new(
        legs: Vec<Leg<T>>,
        origin_delay: Time<T>,
        departure_time_model: DepartureTimeModel<T>,
        total_travel_utility: TravelUtility<T>,
        origin_schedule_utility: ScheduleUtility<T>,
        destination_schedule_utility: ScheduleUtility<T>,
    ) -> Self {
        Self {
            legs,
            origin_delay,
            departure_time_model,
            total_travel_utility,
            origin_schedule_utility,
            destination_schedule_utility,
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
    pub fn iter_legs(&'_ self) -> impl Iterator<Item = &'_ Leg<T>> + '_ {
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
    pub fn iter_virtual_legs(&'_ self) -> impl Iterator<Item = &'_ TTF<Time<T>>> + '_ {
        self.legs.iter().filter_map(|leg| {
            if let LegType::Virtual(ttf) = &leg.class {
                Some(ttf)
            } else {
                None
            }
        })
    }
}

impl<T: TTFNum> TravelingMode<T> {
    /// Returns a Vec of TTFs, corresponding to the TTF of each leg given the road-network skims.
    ///
    /// Returns an error if the road-network skims are invalid or if a leg is not feasible (the
    /// origin and destination are disconnected).
    fn get_leg_ttfs<'a>(
        &'a self,
        rn_skims: Option<&'a RoadNetworkSkims<T>>,
        preprocess_data: Option<&RoadNetworkPreprocessingData<T>>,
    ) -> Result<Vec<&'a TTF<Time<T>>>> {
        self.legs
            .iter()
            .map(|l| {
                match &l.class {
                    LegType::Road(road_leg) => {
                        let skims = rn_skims.expect("Found a road leg with no road-network skims")
                            [preprocess_data
                                .expect("Found a road leg with no road-network preprocessing data")
                                .get_unique_vehicle_index(road_leg.vehicle)]
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
                    }
                    LegType::Virtual(ttf) => Ok(ttf),
                }
            })
            .collect()
    }

    /// Returns the total utility of the trip given the departure time and the legs' TTFs.
    fn get_total_utility(&self, departure_time: Time<T>, leg_ttfs: &[&TTF<Time<T>>]) -> Utility<T> {
        let mut current_time = departure_time + self.origin_delay;
        let mut total_travel_time = Time::default();
        let mut total_utility = self.origin_schedule_utility.get_utility(departure_time);
        for (leg_ttf, leg) in leg_ttfs.iter().zip(self.legs.iter()) {
            let travel_time = leg_ttf.eval(current_time);
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

    /// Returns the global travel-time function of the trip, within a given time period, with all
    /// necessary breakpoints to compute utility.
    ///
    /// In principle, the breakpoints are all departure times where the utility is non-linear.
    ///
    /// The returned travel-time function has a breakpoint for the start and for the end of the
    /// given period.
    pub fn get_global_ttf_with_breakpoints(
        &self,
        leg_ttfs: &[&TTF<Time<T>>],
        period: Interval<T>,
    ) -> TTF<Time<T>> {
        // TODO: Check that everything is fine with the periods.
        let mut breakpoints: BinaryHeap<Time<T>> = BinaryHeap::new();
        // The TTF are linked without simplification so that all breakpoints are kept.
        let mut ttf: TTF<Time<T>> = TTF::default();
        // Add breakpoints for schedule delay at origin.
        breakpoints.extend(self.origin_schedule_utility.iter_breakpoints());
        // Add time delay at origin.
        ttf = ttf.add(self.origin_delay);
        for (leg_ttf, leg) in leg_ttfs.iter().zip(self.legs.iter()) {
            // Add the travel time of the current leg.
            ttf = ttf.link(leg_ttf);
            // Add the breakpoints required for the schedule utility of the leg.
            breakpoints.extend(
                ttf.departure_times_with_arrivals_iter(leg.schedule_utility.iter_breakpoints()),
            );
            // Add the stopping time.
            ttf = ttf.add(leg.stopping_time);
        }
        // Add breakpoints for schedule delay at destination.
        breakpoints.extend(ttf.departure_times_with_arrivals_iter(
            self.destination_schedule_utility.iter_breakpoints(),
        ));
        // Add breakpoints to the TTF.
        ttf.add_x_breakpoints(breakpoints.into_sorted_vec(), period.0);
        // Constrain the TTF to the given period.
        ttf.constrain_to_domain(period.0);
        ttf
    }

    /// Returns the total stopping time of the trip, i.e., the sum of the stopping time for each
    /// leg (plus the delay at origin).
    fn get_total_stopping_time(&self) -> Time<T> {
        self.origin_delay + self.legs.iter().map(|l| l.stopping_time).sum()
    }

    /// Returns a [PwlXYF] that yields the utility for each possible departure time, given the
    /// legs' TTFs.
    fn get_utility_function(
        &self,
        leg_ttfs: &[&TTF<Time<T>>],
        period: Interval<T>,
    ) -> PwlXYF<Time<T>, Utility<T>, NoUnit<T>> {
        let ttf = self.get_global_ttf_with_breakpoints(leg_ttfs, period);

        // Convert the TTF to vectors of departure times and travel times.
        let (tds, tts) = match ttf {
            TTF::Constant(tt) => (period.to_vec(), vec![tt; 2]),
            TTF::Piecewise(pwl_ttf) => {
                let (mut tds, mut tts) = pwl_ttf.into_xs_and_ys();
                debug_assert!(tds[tds.len() - 1].approx_le(&period.end()));
                // Add the end of the period as breakpoint if it does not exist yet.
                if tds[tds.len() - 1].approx_lt(&period.end()) {
                    tds.push(period.end());
                    tts.push(tts[tts.len() - 1]);
                }
                (tds, tts)
            }
        };
        debug_assert!(tds[0].approx_eq(&period.start()));
        debug_assert!(tds[tds.len() - 1].approx_eq(&period.end()));

        let mut utilities = vec![Utility::default(); tds.len()];
        // Add schedule utility at origin.
        utilities
            .iter_mut()
            .zip(tds.iter())
            .for_each(|(u, &td)| *u += self.origin_schedule_utility.get_utility(td));
        // Add total travel utility (stopping time needs to be excluded).
        utilities.iter_mut().zip(tts.iter()).for_each(|(u, &tt)| {
            *u += self
                .total_travel_utility
                .get_travel_utility(tt - self.get_total_stopping_time())
        });
        let mut current_times = tds.clone();
        current_times
            .iter_mut()
            .for_each(|t| *t += self.origin_delay);
        for (leg_ttf, leg) in leg_ttfs.iter().zip(self.legs.iter()) {
            // Add the leg-specific travel-time utility and schedule utility, and update the
            // current times.
            let tt_iter = leg_ttf.iter_eval(current_times.clone().into_iter());
            utilities
                .iter_mut()
                .zip(current_times.iter_mut().zip(tt_iter))
                .for_each(|(u, (t, tt))| {
                    // Update the current time.
                    *t += tt;
                    // Increase the utility for the associated departure time.
                    *u += leg.travel_utility.get_travel_utility(tt)
                        + leg.schedule_utility.get_utility(*t);
                    // Add the stopping time.
                    *t += leg.stopping_time;
                });
        }
        // At this point, current times should be equal to the arrival time at destination.
        debug_assert!(
            current_times
                .iter()
                .zip(tds.iter().zip(tts.iter()))
                .all(|(ct, (&td, &tt))| (td + tt).approx_eq(ct)),
            "Error in time summation\nCurrent times: {current_times:?}\nTDs: {tds:?}\nTTs: {tts:?}"
        );
        // Add schedule utility at destination.
        utilities
            .iter_mut()
            .zip(current_times.iter())
            .for_each(|(u, &ta)| *u += self.destination_schedule_utility.get_utility(ta));
        PwlXYF::from_x_and_y(tds, utilities)
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
        departure_time: Time<T>,
        expected_utility: Utility<T>,
    ) -> TripResults<T> {
        assert!(self.is_virtual_only(), "The function `get_trip_results_for_virtual_only` is only available for virtual only trips");
        let mut leg_results = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time + self.origin_delay;
        let mut utility = self.origin_schedule_utility.get_utility(departure_time);
        let mut total_travel_time = Time::zero();
        for leg in self.legs.iter() {
            let ttf = if let LegType::Virtual(ttf) = &leg.class {
                ttf
            } else {
                // All legs are virtual here.
                unreachable!()
            };
            let travel_time = ttf.eval(current_time);
            let arrival_time = current_time + travel_time;
            total_travel_time += travel_time;
            let lr = LegResults {
                departure_time: current_time,
                arrival_time: current_time + travel_time,
                travel_utility: leg.travel_utility.get_travel_utility(travel_time),
                schedule_utility: leg.schedule_utility.get_utility(arrival_time),
                class: LegTypeResults::Virtual,
            };
            leg_results.push(lr);
            current_time = arrival_time + leg.stopping_time;
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
        }
    }

    /// Returns the initialized trip results given the departure time from origin.
    ///
    /// Not all values of the trip results are filled. Some values should be filled in the
    /// within-day model.
    fn init_trip_results(
        &self,
        departure_time: Time<T>,
        expected_utility: Utility<T>,
        leg_ttfs: &[&TTF<Time<T>>],
    ) -> TripResults<T> {
        let mut leg_results = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time + self.origin_delay;
        for (leg, ttf) in self.legs.iter().zip(leg_ttfs.iter()) {
            let travel_time = ttf.eval(current_time);
            let arrival_time = current_time + travel_time;
            let leg_result = leg.init_leg_results(current_time, arrival_time);
            leg_results.push(leg_result);
            current_time = arrival_time + leg.stopping_time;
        }
        TripResults {
            legs: leg_results,
            departure_time,
            arrival_time: Time::nan(),
            total_travel_time: Time::nan(),
            utility: Utility::nan(),
            expected_utility,
            virtual_only: false,
        }
    }

    /// Returns the pre-day choice for this mode.
    ///
    /// If the [TravelingMode] is virtual only, then the pre-day choice is always the same and it
    /// is computed only the first time this function is called.
    pub fn get_pre_day_choice<'a: 'b, 'b>(
        &'a self,
        rn_skims: Option<&'b RoadNetworkSkims<T>>,
        preprocess_data: Option<&RoadNetworkPreprocessingData<T>>,
    ) -> Result<(Utility<T>, ModeCallback<'b, T>)> {
        if let Some(choice) = self.choice.get() {
            // The TravelingMode is virtual only and the pre-day choices were already computed.
            return Ok(choice.to_expected_utility_and_mode_callback());
        }
        self.make_pre_day_choice(rn_skims, preprocess_data)
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
        rn_skims: Option<&'b RoadNetworkSkims<T>>,
        preprocess_data: Option<&RoadNetworkPreprocessingData<T>>,
    ) -> Result<(Utility<T>, ModeCallback<'b, T>)> {
        let leg_ttfs = self.get_leg_ttfs(rn_skims, preprocess_data)?;
        match &self.departure_time_model {
            &DepartureTimeModel::Constant(departure_time) => {
                let expected_utility = self.get_total_utility(departure_time, &leg_ttfs);
                if self.is_virtual_only() {
                    let virtual_results = self
                        .choice
                        .try_insert(VirtualOnlyPreDayResults {
                            expected_utility,
                            trip_results: self.get_trip_results_for_virtual_only(
                                departure_time,
                                expected_utility,
                            ),
                        })
                        .unwrap();
                    return Ok(virtual_results.to_expected_utility_and_mode_callback());
                }
                let callback = move || {
                    Ok(ModeResults::Trip(self.init_trip_results(
                        departure_time,
                        expected_utility,
                        &leg_ttfs,
                    )))
                };
                Ok((expected_utility, Box::new(callback)))
            }
            DepartureTimeModel::ContinuousChoice {
                period,
                choice_model,
            } => {
                let utilities = self.get_utility_function(&leg_ttfs, *period);
                let (time_callback, expected_utility) = choice_model.get_choice(utilities)?;
                if self.is_virtual_only() {
                    let departure_time = time_callback();
                    let virtual_results = self
                        .choice
                        .try_insert(VirtualOnlyPreDayResults {
                            expected_utility,
                            trip_results: self.get_trip_results_for_virtual_only(
                                departure_time,
                                expected_utility,
                            ),
                        })
                        .unwrap();
                    return Ok(virtual_results.to_expected_utility_and_mode_callback());
                }
                let callback = move || {
                    let departure_time = time_callback();
                    Ok(ModeResults::Trip(self.init_trip_results(
                        departure_time,
                        expected_utility,
                        &leg_ttfs,
                    )))
                };
                Ok((expected_utility, Box::new(callback)))
            }
        }
    }
}

/// Expected utility and trip results for a [TravelingMode] with only virtual legs.
#[derive(Clone, Debug)]
pub(crate) struct VirtualOnlyPreDayResults<T> {
    expected_utility: Utility<T>,
    trip_results: TripResults<T>,
}

impl<T: Copy> VirtualOnlyPreDayResults<T> {
    /// Returns a tuple with the expected utility and a [ModeCallback].
    fn to_expected_utility_and_mode_callback(&'_ self) -> (Utility<T>, ModeCallback<'_, T>) {
        let callback = move || Ok(ModeResults::Trip(self.trip_results.clone()));
        (self.expected_utility, Box::new(callback))
    }
}

/// Model used to compute the chosen departure time.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum DepartureTimeModel<T> {
    /// The departure time is always equal to the given value.
    Constant(Time<T>),
    /// The departure time is chosen according to a continuous choice model.
    ContinuousChoice {
        /// Interval in which the departure time is chosen.
        period: Interval<T>,
        /// Continuous choice model.
        choice_model: ContinuousChoiceModel<NoUnit<T>>,
    },
}
