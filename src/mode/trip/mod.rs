// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to trips.
use anyhow::{anyhow, Result};
use choice::{ChoiceModel, ContinuousChoiceModel};
use enum_as_inner::EnumAsInner;
use hashbrown::HashSet;
use log::warn;
use num_traits::{Float, FromPrimitive, Zero};
use once_cell::sync::OnceCell;
use petgraph::graph::NodeIndex;
use petgraph::prelude::EdgeIndex;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::{PwlXYF, TTFNum, TTF};

use self::results::{RoadLegResults, TripResults};
use super::{ModeCallback, ModeResults};
use crate::mode::trip::results::{LegResults, LegTypeResults};
use crate::network::road_network::skim::{EAAllocation, RoadNetworkSkim, RoadNetworkSkims};
use crate::network::road_network::vehicle::VehicleIndex;
use crate::network::road_network::RoadNetworkPreprocessingData;
use crate::progress_bar::MetroProgressBar;
use crate::schedule_utility::ScheduleUtility;
use crate::schema::NodeIndexDef;
use crate::travel_utility::TravelUtility;
use crate::units::{Interval, NoUnit, Time, Utility};

pub mod event;
pub mod results;

const NB_INTERVALS: usize = 1500;

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
    fn init_leg_results(
        &self,
        departure_time: Time<T>,
        arrival_time: Time<T>,
        route: Option<Vec<EdgeIndex>>,
    ) -> LegResults<T> {
        LegResults {
            departure_time: Time::nan(),
            arrival_time: Time::nan(),
            travel_utility: Utility::nan(),
            schedule_utility: Utility::nan(),
            class: self
                .class
                .init_leg_type_results(departure_time, arrival_time, route),
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
        route: Option<Vec<EdgeIndex>>,
    ) -> LegTypeResults<T> {
        match self {
            Self::Road(_) => {
                LegTypeResults::Road(RoadLegResults::new(departure_time, arrival_time, route))
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

fn default_is_true() -> bool {
    true
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
    /// If `true`, the routes of the trip are computed during the pre-day model (faster).
    /// If `false`, they are computed during the within-day model (which means that the route for
    /// second and after legs is computed using the actual departure time, not the predicted one)..
    #[serde(default = "default_is_true")]
    pub(crate) pre_compute_route: bool,
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
        let interval = period.length() / Time::from_usize(NB_INTERVALS).unwrap();
        let tds: Vec<_> = std::iter::successors(Some(period.start()), |x| Some(*x + interval))
            .take_while(|&x| x <= period.end())
            .collect();

        let mut utilities = vec![Utility::default(); tds.len()];
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
                    let tt = leg_ttf.eval(*t);
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
            .zip(current_times.into_iter())
            .zip(tds.into_iter())
            .for_each(|((u, t), td)| {
                let tot_tt = (t - td) - self.get_total_stopping_time();
                *u += self.total_travel_utility.get_travel_utility(tot_tt)
            });
        PwlXYF::from_values(utilities, period.start(), interval)
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
        for (leg, leg_ttf) in self.iter_legs().zip(leg_ttfs.iter()) {
            let travel_time = leg_ttf.eval(current_time);
            let arrival_time = current_time + travel_time;
            let leg_result = leg.init_leg_results(current_time, arrival_time, None);
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
        preprocess_data: Option<&'b RoadNetworkPreprocessingData<T>>,
        progress_bar: MetroProgressBar,
    ) -> Result<(Utility<T>, ModeCallback<'b, T>)> {
        if let Some(choice) = self.choice.get() {
            // The TravelingMode is virtual only and the pre-day choices were already computed.
            return Ok(choice.to_expected_utility_and_mode_callback());
        }
        self.make_pre_day_choice(rn_skims, preprocess_data, progress_bar)
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
        preprocess_data: Option<&'b RoadNetworkPreprocessingData<T>>,
        progress_bar: MetroProgressBar,
    ) -> Result<(Utility<T>, ModeCallback<'b, T>)> {
        let leg_ttfs = self.get_leg_ttfs(rn_skims, preprocess_data)?;
        let (expected_utility, time_callback) = match &self.departure_time_model {
            &DepartureTimeModel::Constant(departure_time) => {
                let expected_utility = self.get_total_utility(departure_time, &leg_ttfs);
                let time_callback: Box<dyn FnOnce() -> Time<T>> = Box::new(move || departure_time);
                (expected_utility, time_callback)
            }
            DepartureTimeModel::DiscreteChoice {
                values,
                choice_model,
                offset,
            } => {
                let utilities: Vec<_> = values
                    .iter()
                    .map(|&td| self.get_total_utility(td, &leg_ttfs))
                    .collect();
                let (chosen_id, expected_utility) = choice_model.get_choice(&utilities)?;
                let departure_time = values[chosen_id] + *offset;
                let time_callback: Box<dyn FnOnce() -> Time<T>> = Box::new(move || departure_time);
                (expected_utility, time_callback)
            }
            DepartureTimeModel::ContinuousChoice {
                period,
                choice_model,
            } => {
                let utilities = self.get_utility_function(&leg_ttfs, *period);
                let (time_callback, expected_utility) = choice_model.get_choice(utilities)?;
                (expected_utility, time_callback)
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
                    rn_skims,
                    progress_bar,
                    alloc,
                )?))
            } else {
                Ok(ModeResults::Trip(self.init_trip_results(
                    departure_time,
                    expected_utility,
                    &leg_ttfs,
                )))
            }
        };
        Ok((expected_utility, Box::new(callback)))
    }

    /// Returns the initialized trip results given the departure time from origin.
    ///
    /// Not all values of the trip results are filled. Some values should be filled in the
    /// within-day model.
    fn init_trip_results_with_route(
        &self,
        departure_time: Time<T>,
        expected_utility: Utility<T>,
        preprocess_data: Option<&RoadNetworkPreprocessingData<T>>,
        skims: Option<&RoadNetworkSkims<T>>,
        progress_bar: MetroProgressBar,
        alloc: &mut EAAllocation<T>,
    ) -> Result<TripResults<T>> {
        let mut leg_results = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time + self.origin_delay;
        for leg in self.iter_legs() {
            let (arrival_time, route) = match &leg.class {
                LegType::Road(road_leg) => {
                    let uvehicle = preprocess_data
                        .expect("Got a road leg but there is no road network preprocess data.")
                        .unique_vehicles[road_leg.vehicle];
                    let vehicle_skims = skims
                        .expect("Got a road leg but there is no road network skims.")[uvehicle]
                        .as_ref()
                        .expect("Road network skims are empty.");
                    let (arrival_time, route) = get_arrival_time_and_route(
                        road_leg,
                        current_time,
                        vehicle_skims,
                        progress_bar.clone(),
                        alloc,
                    )?;
                    (arrival_time, Some(route))
                }
                LegType::Virtual(ttf) => (current_time + ttf.eval(current_time), None),
            };
            let leg_result = leg.init_leg_results(current_time, arrival_time, route);
            leg_results.push(leg_result);
            current_time = arrival_time + leg.stopping_time;
        }
        Ok(TripResults {
            legs: leg_results,
            departure_time,
            arrival_time: Time::nan(),
            total_travel_time: Time::nan(),
            utility: Utility::nan(),
            expected_utility,
            virtual_only: false,
        })
    }
}

/// Expected utility and trip results for a [TravelingMode] with only virtual legs.
#[derive(Clone, Debug)]
pub(crate) struct VirtualOnlyPreDayResults<T> {
    expected_utility: Utility<T>,
    trip_results: TripResults<T>,
}

impl<T: TTFNum> VirtualOnlyPreDayResults<T> {
    /// Returns a tuple with the expected utility and a [ModeCallback].
    fn to_expected_utility_and_mode_callback(&'_ self) -> (Utility<T>, ModeCallback<'_, T>) {
        let callback = move |_| Ok(ModeResults::Trip(self.trip_results.clone()));
        (self.expected_utility, Box::new(callback))
    }
}

/// Model used to compute the chosen departure time.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum DepartureTimeModel<T> {
    /// The departure time is always equal to the given value.
    Constant(Time<T>),
    /// The departure time is chosen among a finite number of values.
    DiscreteChoice {
        /// Values among which the departure time is chosen.
        values: Vec<Time<T>>,
        /// Discrete choice model.
        choice_model: ChoiceModel<NoUnit<T>>,
        /// Offset time added to the chosen departure-time value (can be negative).
        #[serde(default)]
        #[schemars(default = "default_time_schema")]
        offset: Time<T>,
    },
    /// The departure time is chosen according to a continuous choice model.
    ContinuousChoice {
        /// Interval in which the departure time is chosen.
        period: Interval<T>,
        /// Continuous choice model.
        choice_model: ContinuousChoiceModel<NoUnit<T>>,
    },
}

fn default_time_schema() -> String {
    "0".to_owned()
}

/// Run an earliest arrival query on the [RoadNetworkSkim] to get the arrival time and route, for a
/// given origin, destination and departure time.
///
/// Return an error if the destination cannot be reached with the given departure time from origin.
fn get_arrival_time_and_route<T: TTFNum>(
    leg: &RoadLeg,
    departure_time: Time<T>,
    skims: &RoadNetworkSkim<T>,
    progress_bar: MetroProgressBar,
    alloc: &mut EAAllocation<T>,
) -> Result<(Time<T>, Vec<EdgeIndex>)> {
    if let Some((arrival_time, route)) =
        skims.earliest_arrival_query(leg.origin, leg.destination, departure_time, alloc)?
    {
        if cfg!(debug_assertions) {
            // Check if there is a loop in the route.
            let n = route.iter().collect::<HashSet<_>>().len();
            if n != route.len() {
                progress_bar.suspend(|| {
                    warn!(
                        "Found a loop in route from {} to {} at time {}",
                        leg.origin.index(),
                        leg.destination.index(),
                        departure_time
                    );
                })
            }
        }
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
