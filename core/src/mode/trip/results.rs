// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Structs to store results of road and virtual trips.
use enum_as_inner::EnumAsInner;
use num_traits::{Float, FromPrimitive, Zero};
use petgraph::prelude::EdgeIndex;
use serde::{Deserialize, Serialize};
use ttf::{TTFNum, TTF};

use super::event::{RoadEvent, VehicleEvent};
use super::{Leg, LegType, TravelingMode};
use crate::event::Event;
use crate::mode::ModeIndex;
use crate::network::road_network::preprocess::UniqueVehicles;
use crate::network::road_network::RoadNetworkWeights;
use crate::population::AgentIndex;
use crate::units::{Distribution, Length, NoUnit, Time, Utility};

/// The results for a [LegType::Road].
#[derive(Debug, Clone, PartialEq)]
pub struct RoadLegResults {
    /// The expected route to be taken by the vehicle.
    pub expected_route: Option<Vec<EdgeIndex>>,
    /// The route taken by the vehicle, together with the timings of the events.
    pub route: Vec<RoadEvent>,
    /// Total time spent traveling on an edge.
    pub road_time: Time,
    /// Total time spent waiting at the in-bottleneck of an edge.
    pub in_bottleneck_time: Time,
    /// Total time spent waiting at the out-bottleneck of an edge.
    pub out_bottleneck_time: Time,
    /// Travel time of taking the same route, assuming no congestion.
    pub route_free_flow_travel_time: Time,
    /// Travel time of the fastest no-congestion route between origin and destination of the leg.
    pub global_free_flow_travel_time: Time,
    /// Length of the route taken.
    pub length: Length,
    /// Length of the route taken that was not taken during the previous iteration.
    pub length_diff: Option<Length>,
    /// Expected departure time, in the pre-day model.
    pub pre_exp_departure_time: Time,
    /// Expected arrival time at destination (excluding the stopping time), in the pre-day model.
    pub pre_exp_arrival_time: Time,
    /// Expected arrival time at destination (excluding the stopping time), when leaving origin.
    pub exp_arrival_time: Time,
}

impl RoadLegResults {
    /// Returns the number of edges taken during the leg.
    fn edge_count(&self) -> usize {
        self.route.len()
    }
}

impl RoadLegResults {
    /// Creates a new [RoadLegResults] where only the results known at this time are filled.
    pub fn new(
        departure_time: Time,
        arrival_time: Time,
        expected_route: Option<Vec<EdgeIndex>>,
        length: Option<Length>,
        route_free_flow_travel_time: Option<Time>,
        global_free_flow_travel_time: Time,
    ) -> Self {
        Self {
            expected_route,
            length: length.unwrap_or_else(Length::nan),
            route_free_flow_travel_time: route_free_flow_travel_time.unwrap_or_else(Time::nan),
            global_free_flow_travel_time,
            route: Vec::new(),
            road_time: Time::zero(),
            in_bottleneck_time: Time::zero(),
            out_bottleneck_time: Time::zero(),
            pre_exp_departure_time: departure_time,
            pre_exp_arrival_time: arrival_time,
            length_diff: None,
            exp_arrival_time: Time::nan(),
        }
    }

    /// Clones and resets the road leg results in prevision for a new day.
    pub fn reset(&self) -> Self {
        Self {
            expected_route: None,
            route: Vec::with_capacity(self.route.len()),
            global_free_flow_travel_time: self.global_free_flow_travel_time,
            pre_exp_departure_time: self.pre_exp_departure_time,
            pre_exp_arrival_time: self.pre_exp_arrival_time,
            road_time: Time::zero(),
            in_bottleneck_time: Time::zero(),
            out_bottleneck_time: Time::zero(),
            route_free_flow_travel_time: Time::nan(),
            length: Length::nan(),
            length_diff: None,
            exp_arrival_time: Time::nan(),
        }
    }

    fn with_previous_results(&mut self, previous_results: &Self) {
        self.length_diff = Some(crate::network::road_network::route_length_diff(
            self.route.iter().map(|e| e.edge),
            previous_results.route.iter().map(|e| e.edge),
        ))
    }
}

/// The pre-day results for a [LegType::Road].
#[derive(Debug, Clone, PartialEq)]
pub struct PreDayRoadLegResults {
    /// The sequence of edges expected to be taken by the agent, if it has been computed.
    pub(crate) expected_route: Option<Vec<EdgeIndex>>,
    /// The expected route to be taken by the agent, together with the timings.
    pub route: Vec<RoadEvent>,
    /// Travel time of taking the same route, assuming no congestion.
    pub route_free_flow_travel_time: Time,
    /// Travel time of the fastest no-congestion route between origin and destination of the leg.
    pub global_free_flow_travel_time: Time,
    /// Length of the route taken.
    pub length: Length,
    /// Expected departure time, in the pre-day model.
    pub pre_exp_departure_time: Time,
    /// Expected arrival time at destination (excluding the stopping time), in the pre-day model.
    pub pre_exp_arrival_time: Time,
}

impl From<RoadLegResults> for PreDayRoadLegResults {
    fn from(value: RoadLegResults) -> Self {
        Self {
            expected_route: value.expected_route,
            route: Vec::new(),
            route_free_flow_travel_time: value.route_free_flow_travel_time,
            global_free_flow_travel_time: value.global_free_flow_travel_time,
            length: value.length,
            pre_exp_departure_time: value.pre_exp_departure_time,
            pre_exp_arrival_time: value.pre_exp_arrival_time,
        }
    }
}

/// Results that depend on the leg type (see [LegType]).
#[derive(Debug, Clone, Default, PartialEq, EnumAsInner)]
pub enum LegTypeResults {
    /// The leg is a road leg.
    Road(RoadLegResults),
    /// The leg is a virtual leg.
    Virtual,
    /// Uninitialized leg type results.
    #[default]
    Uninitialized,
}

impl LegTypeResults {
    pub(crate) fn with_previous_results(&mut self, previous_results: &Self) {
        match self {
            Self::Road(road_leg_results) => {
                road_leg_results.with_previous_results(previous_results.as_road().unwrap())
            }
            Self::Virtual => (),
            Self::Uninitialized => unreachable!(),
        }
    }
}

/// Pre-day results that depend on the leg type (see [LegType]).
#[derive(Debug, Clone, PartialEq, EnumAsInner)]
pub enum PreDayLegTypeResults {
    /// The leg is a road leg.
    Road(PreDayRoadLegResults),
    /// The leg is a virtual leg.
    Virtual,
}

impl From<LegTypeResults> for PreDayLegTypeResults {
    fn from(value: LegTypeResults) -> Self {
        match value {
            LegTypeResults::Road(road_leg) => Self::Road(road_leg.into()),
            LegTypeResults::Virtual => Self::Virtual,
            LegTypeResults::Uninitialized => unreachable!(),
        }
    }
}

/// Results specific to a leg of the trip (see [Leg]).
#[derive(Debug, Clone, PartialEq)]
pub struct LegResults {
    /// Id of the leg.
    pub id: usize,
    /// Departure time of the leg.
    pub departure_time: Time,
    /// Arrival time of the leg (before the stopping time).
    pub arrival_time: Time,
    /// Travel utility for this leg.
    pub travel_utility: Utility,
    /// Schedule utility for this leg.
    pub schedule_utility: Utility,
    /// Results specific to the leg's class (road, virtual).
    pub class: LegTypeResults,
    /// Difference between the departure time of the previous and current iteration.
    pub departure_time_shift: Option<Time>,
}

impl LegResults {
    /// Returns the travel time of the leg.
    fn travel_time(&self) -> Time {
        self.arrival_time - self.departure_time
    }

    /// Returns the total utility of the leg (the sum of the travel and schedule utility).
    fn total_utility(&self) -> Utility {
        self.travel_utility + self.schedule_utility
    }

    /// Save the arrival time and utility decomposition of a leg.
    pub fn save_results(&mut self, travel_time: Time, leg: &Leg) {
        debug_assert!(!self.departure_time.is_nan());
        self.arrival_time = self.departure_time + travel_time;
        let (travel_utility, schedule_utility) =
            leg.get_utility_decomposition(self.departure_time, travel_time);
        self.travel_utility = travel_utility;
        self.schedule_utility = schedule_utility;
    }

    pub(crate) fn with_previous_results(&mut self, previous_results: &Self) {
        debug_assert_eq!(self.id, previous_results.id);
        self.departure_time_shift = Some(self.departure_time - previous_results.departure_time);
        self.class.with_previous_results(&previous_results.class);
    }
}

/// Pre-day results specific to a leg of the trip (see [Leg]).
#[derive(Debug, Clone, PartialEq)]
pub struct PreDayLegResults {
    /// Id of the leg.
    pub id: usize,
    /// Results specific to the leg's class (road, virtual).
    pub class: PreDayLegTypeResults,
}

impl From<LegResults> for PreDayLegResults {
    fn from(value: LegResults) -> Self {
        Self {
            id: value.id,
            class: value.class.into(),
        }
    }
}

impl PreDayLegResults {
    fn add_expected_route(
        &mut self,
        leg: &Leg,
        weights: &RoadNetworkWeights,
        unique_vehicles: &UniqueVehicles,
    ) {
        if let PreDayLegTypeResults::Road(road_leg_result) = &mut self.class {
            if let Some(expected_route) = &road_leg_result.expected_route {
                let mut output_route = Vec::with_capacity(expected_route.len());
                let original_vehicle = leg.class.as_road().unwrap().vehicle;
                let vehicle_id = unique_vehicles[original_vehicle];
                let mut current_time = road_leg_result.pre_exp_departure_time;
                for &edge_id in expected_route.iter() {
                    let original_id = crate::network::road_network::original_edge_id_of(edge_id);
                    let road_event = RoadEvent {
                        edge: original_id,
                        entry_time: current_time,
                    };
                    current_time += weights[(vehicle_id, original_id)].eval(current_time);
                    output_route.push(road_event);
                }
                debug_assert!(current_time.approx_eq(&road_leg_result.pre_exp_arrival_time));
                road_leg_result.route = output_route;
                road_leg_result.length =
                    crate::network::road_network::route_length(expected_route.iter().copied());
                road_leg_result.route_free_flow_travel_time =
                    crate::network::road_network::route_free_flow_travel_time(
                        expected_route.iter().copied(),
                        original_vehicle,
                    );
            }
        }
    }
}

/// Struct used to store the results from a [TravelingMode] in the within-day model.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct TripResults {
    /// The results specific to each leg of the trip.
    pub legs: Vec<LegResults>,
    /// Departure time from the origin of the first leg (before the delay time at origin).
    pub departure_time: Time,
    /// Arrival time at the destination of the last leg (after the stopping time).
    pub arrival_time: Time,
    /// Total time spent traveling.
    pub total_travel_time: Time,
    /// (Deterministic) utility resulting from the trip.
    pub utility: Utility,
    /// Expected utility for the trip (from the pre-day model).
    pub expected_utility: Utility,
    /// If `true`, the trip is composed only of virtual legs.
    pub virtual_only: bool,
    /// Difference between the departure time of the previous and current iteration.
    pub departure_time_shift: Option<Time>,
}

impl TripResults {
    pub(crate) fn new(
        legs: Vec<LegResults>,
        departure_time: Time,
        expected_utility: Utility,
        virtual_only: bool,
    ) -> Self {
        Self {
            legs,
            departure_time,
            expected_utility,
            arrival_time: Time::nan(),
            total_travel_time: Time::nan(),
            utility: Utility::nan(),
            virtual_only,
            departure_time_shift: None,
        }
    }
}

impl TripResults {
    /// Returns the departure time of the trip.
    pub fn departure_time(&self) -> Time {
        self.departure_time
    }

    /// Returns the arrival time of the trip.
    pub fn arrival_time(&self) -> Time {
        self.arrival_time
    }

    /// Returns the total travel time of the trip.
    pub fn total_travel_time(&self) -> Time {
        self.total_travel_time
    }

    /// Returns the utility of the trip.
    pub fn utility(&self) -> Utility {
        self.utility
    }

    /// Returns the expected utility of the trip.
    pub fn expected_utility(&self) -> Utility {
        self.expected_utility
    }
}

impl TripResults {
    /// Clones and resets the trip results in prevision for a new day.
    pub fn reset(&self) -> Self {
        if self.virtual_only {
            // Simply clone the results as they will not change (and they would not be computed
            // again anyway).
            self.clone()
        } else {
            let legs = self
                .legs
                .iter()
                .map(|l| LegResults {
                    id: l.id,
                    departure_time: Time::nan(),
                    arrival_time: Time::nan(),
                    travel_utility: Utility::nan(),
                    schedule_utility: Utility::nan(),
                    class: match &l.class {
                        LegTypeResults::Road(road_leg) => LegTypeResults::Road(road_leg.reset()),
                        LegTypeResults::Virtual => LegTypeResults::Virtual,
                        LegTypeResults::Uninitialized => unreachable!(),
                    },
                    departure_time_shift: None,
                })
                .collect();
            Self {
                legs,
                departure_time: self.departure_time,
                arrival_time: Time::nan(),
                total_travel_time: Time::nan(),
                utility: Utility::nan(),
                expected_utility: self.expected_utility,
                virtual_only: false,
                departure_time_shift: None,
            }
        }
    }

    /// Returns `true` if the trip is finished.
    pub fn is_finished(&self) -> bool {
        // When the trip ends, the utility is set to a non NaN value.
        !self.utility.is_nan()
    }

    /// Stores the arrival time and computes additional results for a trip that is finished.
    ///
    /// After a call to this function, all values of the [TripResults] should be filled with some
    /// data.
    pub fn save_results(&mut self, arrival_time: Time, trip: &TravelingMode) {
        self.arrival_time = arrival_time;
        self.total_travel_time = self.legs.iter().map(|l| l.travel_time()).sum();
        let mut total_utility = self
            .legs
            .iter()
            .map(|l| l.travel_utility + l.schedule_utility)
            .sum();
        total_utility += trip
            .total_travel_utility
            .get_travel_utility(self.total_travel_time);
        total_utility += trip
            .origin_schedule_utility
            .get_utility(self.departure_time);
        total_utility += trip
            .destination_schedule_utility
            .get_utility(self.arrival_time);
        self.utility = total_utility;
    }

    /// Returns the initial event associated with the trip.
    ///
    /// Returns `None` if the trip is virtual only.
    pub(crate) fn get_event(
        &self,
        agent_id: AgentIndex,
        mode_id: ModeIndex,
    ) -> Option<Box<dyn Event>> {
        if self.virtual_only {
            None
        } else {
            Some(Box::new(VehicleEvent::new(
                agent_id,
                mode_id,
                self.departure_time,
            )))
        }
    }

    pub(crate) fn with_previous_results(&mut self, previous_results: &Self) {
        self.departure_time_shift = Some(self.departure_time - previous_results.departure_time);
        for (leg_res, prev_leg_res) in self.legs.iter_mut().zip(previous_results.legs.iter()) {
            leg_res.with_previous_results(prev_leg_res);
        }
    }
}

/// Struct used to store the pre-day results for a [TravelingMode].
#[derive(Debug, Default, Clone, PartialEq)]
pub struct PreDayTripResults {
    /// The results specific to each leg of the trip.
    pub legs: Vec<PreDayLegResults>,
    /// Departure time from the origin of the first leg (before the delay time at origin).
    pub departure_time: Time,
    /// Expected utility for the trip (from the pre-day model).
    pub expected_utility: Utility,
}

impl From<TripResults> for PreDayTripResults {
    fn from(value: TripResults) -> Self {
        Self {
            legs: value.legs.into_iter().map(|l| l.into()).collect(),
            departure_time: value.departure_time,
            expected_utility: value.expected_utility,
        }
    }
}

impl PreDayTripResults {
    pub(crate) fn add_expected_route(
        &mut self,
        trip: &TravelingMode,
        weights: &RoadNetworkWeights,
        unique_vehicles: &UniqueVehicles,
    ) {
        for (leg_result, leg) in self.legs.iter_mut().zip(trip.iter_legs()) {
            leg_result.add_expected_route(leg, weights, unique_vehicles);
        }
    }
}

/// Struct to store aggregate results specific to traveling modes of transportation.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AggregateTripResults {
    /// Number of trips taken with a traveling mode of transportation.
    pub count: usize,
    /// Distribution of departure times from origin (before origin delay time).
    pub departure_time: Distribution<Time>,
    /// Distribution of arrival times (after last leg's stopping time).
    pub arrival_time: Distribution<Time>,
    /// Distribution of total travel times (excluding stopping times and origin delay).
    pub travel_time: Distribution<Time>,
    /// Distribution of total utility.
    pub utility: Distribution<Utility>,
    /// Distribution of expected utility (pre-day model).
    pub expected_utility: Distribution<Utility>,
    /// Distribution of departure time shift compared to previous iteration (except for the first
    /// iteration; excluding agents who choose a different mode compared to the previous
    /// iteration).
    pub dep_time_shift: Option<Distribution<Time>>,
    /// Root mean squared distance of departure time compared to the previous iteration (except for
    /// the first iteration; excluding agents who choose a different mode compared to the previous
    /// iteration).
    pub dep_time_rmse: Option<Time>,
    /// Results specific to road legs.
    pub road_leg: Option<AggregateRoadLegResults>,
    /// Results specific to virtual legs.
    pub virtual_leg: Option<AggregateVirtualLegResults>,
}

/// Struct to store aggregate results specific to the road legs.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AggregateRoadLegResults {
    /// Number of road legs taken.
    pub count: usize,
    /// Number of chosen modes with at least one road leg.
    pub mode_count_one: usize,
    /// Number of chosen modes with only road legs.
    pub mode_count_all: usize,
    /// Distribution of the number of road legs per trip.
    pub count_distribution: Distribution<NoUnit>,
    /// Distribution of departure times from leg's origin.
    pub departure_time: Distribution<Time>,
    /// Distribution of arrival times at leg's destination (before the stopping time).
    pub arrival_time: Distribution<Time>,
    /// Distribution of road time (time spent traveling on an edge).
    pub road_time: Distribution<Time>,
    /// Distribution of in-bottleneck time (time spent waiting at the entry bottleneck of an edge).
    pub in_bottleneck_time: Distribution<Time>,
    /// Distribution of out-bottleneck time (time spent waiting at the exit bottleneck of an edge).
    pub out_bottleneck_time: Distribution<Time>,
    /// Distribution of total travel time (excluding stopping time).
    pub travel_time: Distribution<Time>,
    /// Distribution of route free-flow travel times.
    pub route_free_flow_travel_time: Distribution<Time>,
    /// Distribution of global free-flow travel times.
    pub global_free_flow_travel_time: Distribution<Time>,
    /// Distribution of the relative difference between actual travel time and route free-flow
    /// travel time.
    pub route_congestion: Distribution<NoUnit>,
    /// Distribution of the relative difference between actual travel time and global free-flow
    /// travel time.
    pub global_congestion: Distribution<NoUnit>,
    /// Distribution of route length.
    pub length: Distribution<Length>,
    /// Distribution of number of edges taken.
    pub edge_count: Distribution<NoUnit>,
    /// Distribution of leg's utility.
    pub utility: Distribution<Utility>,
    /// Distribution of expected total travel time.
    pub exp_travel_time: Distribution<Time>,
    /// Distribution of relative difference between expected travel time and actual travel time.
    pub exp_travel_time_rel_diff: Distribution<NoUnit>,
    /// Distribution of absolute difference between expected travel time and actual travel time.
    pub exp_travel_time_abs_diff: Distribution<Time>,
    /// Root mean squared difference between expected travel time and actual travel time.
    pub exp_travel_time_diff_rmse: Time,
    /// Distribution of length of the current route that was not used in the previous route.
    pub length_diff: Option<Distribution<Length>>,
}

impl AggregateRoadLegResults {
    /// Returns [AggregateRoadLegResults] from the results of an iteration.
    fn from_agent_results(results: &TripAgentResults<'_>) -> Option<Self> {
        /// Returns a [Distribution] by applying a function over [LegResults] and [RoadLegResults].
        fn get_distribution<V: TTFNum, F>(
            results: &TripAgentResults<'_>,
            func: F,
        ) -> Distribution<V>
        where
            F: Fn(&LegResults, &RoadLegResults) -> V,
        {
            Distribution::from_iterator(results.iter().flat_map(|(_, r)| {
                r.legs
                    .iter()
                    .flat_map(|leg_result| match &leg_result.class {
                        LegTypeResults::Road(road_leg_result) => {
                            Some(func(leg_result, road_leg_result))
                        }
                        _ => None,
                    })
            }))
            .unwrap()
        }
        /// Returns a [Distribution] by applying a function over [LegResults] and [RoadLegResults].
        ///
        /// Only the values which are not NaN are considered.
        fn get_distribution_with_filter<V: TTFNum, F>(
            results: &TripAgentResults<'_>,
            func: F,
        ) -> Option<Distribution<V>>
        where
            F: Fn(&LegResults, &RoadLegResults) -> Option<V>,
        {
            Distribution::from_iterator(results.iter().flat_map(|(_, r)| {
                r.legs
                    .iter()
                    .flat_map(|leg_result| match &leg_result.class {
                        LegTypeResults::Road(road_leg_result) => func(leg_result, road_leg_result),
                        _ => None,
                    })
            }))
        }
        let (count, mode_count_one, mode_count_all) =
            results.iter().fold((0, 0, 0), |acc, (m, _)| {
                let c = m.nb_road_legs();
                let one = (c > 0) as usize;
                let all = (c == m.nb_legs()) as usize;
                (acc.0 + c, acc.1 + one, acc.2 + all)
            });
        if count == 0 {
            // No road leg taken.
            return None;
        }
        let count_distribution = Distribution::from_iterator(results.iter().flat_map(|(m, _)| {
            if m.nb_road_legs() > 0 {
                Some(NoUnit(m.nb_road_legs() as f64))
            } else {
                None
            }
        }))
        .unwrap();
        let departure_time = get_distribution(results, |lr, _| lr.departure_time);
        let arrival_time = get_distribution(results, |lr, _| lr.arrival_time);
        let road_time = get_distribution(results, |_, rlr| rlr.road_time);
        let in_bottleneck_time = get_distribution(results, |_, rlr| rlr.in_bottleneck_time);
        let out_bottleneck_time = get_distribution(results, |_, rlr| rlr.out_bottleneck_time);
        let travel_time = get_distribution(results, |lr, _| lr.travel_time());
        let route_free_flow_travel_time =
            get_distribution(results, |_, rlr| rlr.route_free_flow_travel_time);
        let global_free_flow_travel_time =
            get_distribution(results, |_, rlr| rlr.global_free_flow_travel_time);
        let route_congestion = get_distribution(results, |lr, rlr| {
            if rlr.route_free_flow_travel_time.is_zero() {
                NoUnit::zero()
            } else {
                NoUnit(
                    (lr.travel_time().0 - rlr.route_free_flow_travel_time.0)
                        / rlr.route_free_flow_travel_time.0,
                )
            }
        });
        let global_congestion = get_distribution(results, |lr, rlr| {
            if rlr.global_free_flow_travel_time.is_zero() {
                NoUnit::zero()
            } else {
                NoUnit(
                    (lr.travel_time().0 - rlr.global_free_flow_travel_time.0)
                        / rlr.global_free_flow_travel_time.0,
                )
            }
        });
        let length = get_distribution(results, |_, rlr| rlr.length);
        let edge_count = get_distribution(results, |_, rlr| NoUnit(rlr.edge_count() as f64));
        let utility = get_distribution(results, |lr, _| lr.total_utility());
        let exp_travel_time =
            get_distribution(results, |lr, rlr| rlr.exp_arrival_time - lr.departure_time);
        let exp_travel_time_rel_diff = get_distribution(results, |lr, rlr| {
            let exp_travel_time = rlr.exp_arrival_time - lr.departure_time;
            if exp_travel_time > Time::zero() {
                NoUnit((exp_travel_time - lr.travel_time()).abs().0 / exp_travel_time.0)
            } else {
                NoUnit::zero()
            }
        });
        let exp_travel_time_abs_diff = get_distribution(results, |lr, rlr| {
            let exp_travel_time = rlr.exp_arrival_time - lr.departure_time;
            (exp_travel_time - lr.travel_time()).abs()
        });
        let exp_travel_time_diff_rmse = compute_exp_travel_time_diff_rmse(results);
        let length_diff = get_distribution_with_filter(results, |_, rlr| rlr.length_diff);
        Some(AggregateRoadLegResults {
            count,
            mode_count_one,
            mode_count_all,
            count_distribution,
            departure_time,
            arrival_time,
            road_time,
            in_bottleneck_time,
            out_bottleneck_time,
            travel_time,
            route_free_flow_travel_time,
            global_free_flow_travel_time,
            route_congestion,
            global_congestion,
            length,
            edge_count,
            utility,
            exp_travel_time,
            exp_travel_time_rel_diff,
            exp_travel_time_abs_diff,
            exp_travel_time_diff_rmse,
            length_diff,
        })
    }
}

/// Struct to store aggregate results specific to the virtual legs.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AggregateVirtualLegResults {
    /// Number of virtual legs taken.
    pub count: usize,
    /// Number of chosen modes with at least one virtual leg.
    pub mode_count_one: usize,
    /// Number of chosen modes with only virtual legs.
    pub mode_count_all: usize,
    /// Distribution of the number of virtual legs per trip.
    pub count_distribution: Distribution<NoUnit>,
    /// Distribution of departure times from leg's origin.
    pub departure_time: Distribution<Time>,
    /// Distribution of arrival times at leg's destination (before the stopping time).
    pub arrival_time: Distribution<Time>,
    /// Distribution of total travel time (excluding stopping time).
    pub travel_time: Distribution<Time>,
    /// Distribution of global free-flow travel times.
    pub global_free_flow_travel_time: Distribution<Time>,
    /// Distribution of the relative difference between actual travel time and global free-flow
    /// travel time.
    pub global_congestion: Distribution<NoUnit>,
    /// Distribution of leg's utility.
    pub utility: Distribution<Utility>,
}

impl AggregateVirtualLegResults {
    /// Returns [AggregateVirtualLegResults] from the results of an iteration.
    fn from_agent_results(results: &TripAgentResults<'_>) -> Option<Self> {
        /// Return a [Distribution] by applying a function over [Leg], [TTF] and [LegResults].
        fn get_distribution<V: TTFNum, F>(
            results: &TripAgentResults<'_>,
            func: F,
        ) -> Distribution<V>
        where
            F: Fn(&Leg, &TTF<Time>, &LegResults) -> V,
        {
            Distribution::from_iterator(results.iter().flat_map(|(m, r)| {
                m.legs
                    .iter()
                    .zip(r.legs.iter())
                    .flat_map(|(leg, leg_result)| match (&leg.class, &leg_result.class) {
                        (LegType::Virtual(ttf), LegTypeResults::Virtual) => {
                            Some(func(leg, ttf, leg_result))
                        }
                        _ => None,
                    })
            }))
            .unwrap()
        }
        let (count, mode_count_one, mode_count_all) =
            results.iter().fold((0, 0, 0), |acc, (m, _)| {
                let c = m.nb_virtual_legs();
                let one = (c > 0) as usize;
                let all = (c == m.nb_legs()) as usize;
                (acc.0 + c, acc.1 + one, acc.2 + all)
            });
        if count == 0 {
            // No virtual leg taken.
            return None;
        }
        let count_distribution = Distribution::from_iterator(results.iter().flat_map(|(m, _)| {
            if m.nb_virtual_legs() > 0 {
                Some(NoUnit(m.nb_virtual_legs() as f64))
            } else {
                None
            }
        }))
        .unwrap();
        let departure_time = get_distribution(results, |_, _, lr| lr.departure_time);
        let arrival_time = get_distribution(results, |_, _, lr| lr.arrival_time);
        let travel_time = get_distribution(results, |_, _, lr| lr.travel_time());
        let global_free_flow_travel_time = get_distribution(results, |_, ttf, _| ttf.get_min());
        let global_congestion = get_distribution(results, |_, ttf, lr| {
            NoUnit((lr.travel_time().0 - ttf.get_min().0) / ttf.get_min().0)
        });
        let utility = get_distribution(results, |_, _, lr| lr.total_utility());
        Some(AggregateVirtualLegResults {
            count,
            mode_count_one,
            mode_count_all,
            count_distribution,
            departure_time,
            arrival_time,
            travel_time,
            global_free_flow_travel_time,
            global_congestion,
            utility,
        })
    }
}

/// Shorthand for a Vec to store tuples with, for each agent, the [TravelingMode] and the
/// [TripResults].
pub type TripAgentResults<'a> = Vec<(&'a TravelingMode, &'a TripResults)>;

impl AggregateTripResults {
    /// Returns [AggregateTripResults] from the results of an iteration.
    pub fn from_agent_results(results: TripAgentResults<'_>) -> Self {
        /// Returns a [Distribution] by applying a function over [TravelingMode] and [TripResults].
        fn get_distribution<V: TTFNum, F: Fn(&TravelingMode, &TripResults) -> V>(
            results: &TripAgentResults<'_>,
            func: F,
        ) -> Distribution<V> {
            Distribution::from_iterator(results.iter().map(|(m, r)| func(m, r))).unwrap()
        }
        /// Returns a [Distribution] by applying a function over [TravelingMode] and [TripResults].
        ///
        /// Only the values which are not NaN are considered.
        fn get_distribution_with_filter<
            V: TTFNum,
            F: Fn(&TravelingMode, &TripResults) -> Option<V>,
        >(
            results: &TripAgentResults<'_>,
            func: F,
        ) -> Option<Distribution<V>> {
            Distribution::from_iterator(results.iter().filter_map(|(m, r)| func(m, r)))
        }
        assert!(
            !results.is_empty(),
            "No value to compute aggregate results from"
        );
        let departure_time = get_distribution(&results, |_, r| r.departure_time);
        let arrival_time = get_distribution(&results, |_, r| r.arrival_time);
        let travel_time = get_distribution(&results, |_, r| r.total_travel_time);
        let utility = get_distribution(&results, |_, r| r.utility);
        let expected_utility = get_distribution(&results, |_, r| r.expected_utility);
        let dep_time_shift = get_distribution_with_filter(&results, |_, r| {
            r.departure_time_shift.map(|dts| dts.abs())
        });
        let dep_time_rmse = compute_dep_time_rmse(&results);
        AggregateTripResults {
            count: results.len(),
            departure_time,
            arrival_time,
            travel_time,
            utility,
            expected_utility,
            dep_time_shift,
            dep_time_rmse,
            road_leg: AggregateRoadLegResults::from_agent_results(&results),
            virtual_leg: AggregateVirtualLegResults::from_agent_results(&results),
        }
    }
}

/// Returns the root mean squared error of the agent's departure time from one iteration to
/// another.
///
/// Returns `None` if no agent have results for the previous iteration (first iteration or all
/// agents switched mode).
fn compute_dep_time_rmse(results: &TripAgentResults<'_>) -> Option<Time> {
    let (sum_squared_dist, n) = results
        .iter()
        .filter_map(|(_, res)| res.departure_time_shift.map(|dts| dts.powi(2)))
        .fold((Time::zero(), 0), |(sum, n), squared_dist| {
            (sum + squared_dist, n + 1)
        });
    if n == 0 {
        None
    } else {
        let mean_squared_dist = sum_squared_dist / Time::from_usize(n).unwrap();
        Some(mean_squared_dist.sqrt())
    }
}

/// Returns the root mean squared error of the difference between the agent's travel time and their
/// expected travel time.
fn compute_exp_travel_time_diff_rmse(results: &TripAgentResults<'_>) -> Time {
    let sum_squared_dist = results
        .iter()
        .flat_map(|(_, res)| {
            res.legs.iter().flat_map(|lr| match &lr.class {
                LegTypeResults::Road(rlr) => {
                    let exp_travel_time = rlr.exp_arrival_time - lr.departure_time;
                    Some((exp_travel_time - lr.travel_time()).powi(2))
                }
                _ => None,
            })
        })
        .sum::<Time>();
    let mean_squared_dist = sum_squared_dist / Time::from_usize(results.len()).unwrap();
    mean_squared_dist.sqrt()
}
