// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to modes of transportation with a fixed travel-time function.
use anyhow::Result;
use num_traits::Zero;
use once_cell::sync::OnceCell;
use schemars::JsonSchema;
use serde::{de, Deserialize, Serialize};
use ttf::{NoSimplification, PwlXYF, TTFNum, TTF};

use super::DepartureTimeModel;
use crate::schedule_utility::ScheduleUtility;
use crate::simulation::results::AgentResult;
use crate::travel_utility::TravelUtility;
use crate::units::{Distribution, Interval, NoUnit, Time, Utility};

/// A leg of a trip with a fixed travel-time function.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
pub struct FixedTTFLeg<T> {
    /// Travel-time function from the starting point to the stopping point of the leg.
    ttf: TTF<Time<T>>,
    /// Time spent at the stopping point of the leg, before starting the next leg (if any).
    #[serde(default)]
    stopping_time: Time<T>,
    /// Travel utility for this specific leg (a function of the travel time for this leg).
    #[serde(default)]
    travel_utility: TravelUtility<T>,
    /// Schedule utility at the stopping point (a function of the arrival time at the stopping
    /// point).
    #[serde(default)]
    schedule_utility: ScheduleUtility<T>,
}

impl<T: Default + Zero> Default for FixedTTFLeg<T> {
    fn default() -> Self {
        FixedTTFLeg {
            ttf: Default::default(),
            stopping_time: Default::default(),
            travel_utility: Default::default(),
            schedule_utility: Default::default(),
        }
    }
}

impl<T> FixedTTFLeg<T> {
    /// Creates a new [FixedTTFLeg].
    pub const fn new(
        ttf: TTF<Time<T>>,
        stopping_time: Time<T>,
        travel_utility: TravelUtility<T>,
        schedule_utility: ScheduleUtility<T>,
    ) -> Self {
        FixedTTFLeg {
            ttf,
            stopping_time,
            travel_utility,
            schedule_utility,
        }
    }
}

impl<T: TTFNum> FixedTTFLeg<T> {
    /// Returns the travel time and the total utility of the leg given the departure time from the
    /// starting point.
    ///
    /// The travel time does not include the stopping time.
    fn get_travel_time_and_utility(&self, departure_time: Time<T>) -> (Time<T>, Utility<T>) {
        let travel_time = self.ttf.eval(departure_time);
        let utility = self.get_utility_at(departure_time, travel_time);
        (travel_time, utility)
    }

    /// Returns the utility of the leg, given the departure time and travel time.
    fn get_utility_at(&self, departure_time: Time<T>, travel_time: Time<T>) -> Utility<T> {
        self.travel_utility.get_travel_utility(travel_time)
            + self
                .schedule_utility
                .get_utility(departure_time + travel_time)
    }
}

/// Representation of a mode of transportation with a fixed travel-time function.
///
/// The trip is a sequence of legs, where each leg contains a travel part (with a fixed and given
/// travel-time function) and a stopping part (with a fixed and given stopping time).
///
/// The departure time from origin is the only choice variable (the departure time from any
/// following leg is equal to the arrival time at the stopping point of the previous leg, plus the
/// stopping time of the previous leg.
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
///
/// When the utility for a given component is not specified, it is assumed to be null.
///
/// In practise, one of `total_travel_utility` or legs' `travel_utility` is usually null but this
/// is not enforced by the model.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
#[schemars(example = "crate::schema::example_fixed_ttf_mode")]
pub struct FixedTTFMode<T> {
    /// The legs of the trips, i.e., a list of sub trips with fixed travel-time function, stopping
    /// time and schedule utility.
    ///
    /// The full trip consists in the sequence of the given legs.
    #[serde(deserialize_with = "deser_and_validate_legs")]
    legs: Vec<FixedTTFLeg<T>>,
    /// Model used to choose the departure time of the trip from origin.
    departure_time_model: DepartureTimeModel<T>,
    /// Total travel utility of the trip (a function of the total travel time of the trip).
    #[serde(default)]
    total_travel_utility: TravelUtility<T>,
    /// Schedule utility at origin of the trip (a function of the departure time of the first leg).
    #[serde(default)]
    origin_schedule_utility: ScheduleUtility<T>,
    /// Results of the pre-day model for this mode.
    #[serde(skip)]
    choice: OnceCell<FixedTTFPreDayResults<T>>,
}

/// Results of the pre-day model for a [FixedTTFMode].
#[derive(Clone, Debug)]
struct FixedTTFPreDayResults<T> {
    departure_time: Time<T>,
    expected_utility: Utility<T>,
}

/// Check that the legs of a FixedTTFMode have all the same period.
fn deser_and_validate_legs<'de, T, D>(deserializer: D) -> Result<Vec<FixedTTFLeg<T>>, D::Error>
where
    D: de::Deserializer<'de>,
    T: TTFNum,
{
    let legs: Vec<FixedTTFLeg<T>> = Vec::deserialize(deserializer)?;
    if legs.is_empty() {
        return Err(de::Error::invalid_length(
            0,
            &"At least one leg must be specified",
        ));
    }
    if let Some(period) = legs.iter().find_map(|l| {
        if let TTF::Piecewise(pwl_ttf) = &l.ttf {
            Some(pwl_ttf.period())
        } else {
            None
        }
    }) {
        if legs.iter().any(|l| {
            if let TTF::Piecewise(pwl_ttf) = &l.ttf {
                pwl_ttf.period() != period
            } else {
                false
            }
        }) {
            return Err(de::Error::custom("All legs must have the same period"));
        }
    }
    Ok(legs)
}

impl<T: TTFNum> FixedTTFMode<T> {
    /// Creates a new [FixedTTFMode].
    pub const fn new(
        legs: Vec<FixedTTFLeg<T>>,
        departure_time_model: DepartureTimeModel<T>,
        total_travel_utility: TravelUtility<T>,
        origin_schedule_utility: ScheduleUtility<T>,
    ) -> Self {
        FixedTTFMode {
            legs,
            departure_time_model,
            total_travel_utility,
            origin_schedule_utility,
            choice: OnceCell::new(),
        }
    }

    /// Returns the global travel-time function of the trip, i.e., the travel-time function of
    /// traveling through all the legs in sequence (where the total travel-time function for a leg
    /// is the travel-time function of the leg plus the stopping time).
    pub fn get_global_ttf(&self) -> TTF<Time<T>> {
        let mut ttf = TTF::default();
        for leg in self.legs.iter() {
            ttf = ttf.link(&leg.ttf);
            ttf = ttf.add(leg.stopping_time);
        }
        ttf
    }

    /// Returns the period used by the legs' TTF.
    ///
    /// Returns `None` if all the legs' TTF are constant.
    fn get_leg_period(&self) -> Option<Interval<T>> {
        self.legs.iter().find_map(|l| {
            if let TTF::Piecewise(pwl_ttf) = &l.ttf {
                Some(Interval(*pwl_ttf.period()))
            } else {
                None
            }
        })
    }

    /// Returns the global travel-time function of the trip, within a given time period, with all
    /// necessary breakpoints to compute utility.
    ///
    /// In principle, the breakpoints are all departure times where the utility is non-linear.
    ///
    /// The returned travel-time function has a breakpoint for the start and for the end of the
    /// given period.
    pub fn get_global_ttf_with_breakpoints(&self, period: Interval<T>) -> TTF<Time<T>> {
        let leg_period = self.get_leg_period().unwrap_or(period);
        // The TTF are linked without simplification so that all breakpoints are kept.
        let mut ttf: TTF<Time<T>, NoSimplification> = TTF::default();
        // Add breakpoints for schedule delay at origin.
        ttf.add_x_breakpoints(self.origin_schedule_utility.get_breakpoints(), leg_period.0);
        for leg in self.legs.iter() {
            // Add the travel time of the current leg.
            ttf = ttf.link(&leg.ttf);
            // Add the breakpoints required for the schedule utility of the leg.
            ttf.add_z_breakpoints(leg.schedule_utility.get_breakpoints(), leg_period.0);
            // Add the stopping time.
            ttf = ttf.add(leg.stopping_time);
        }
        // Constrain the TTF to the given period.
        ttf.constrain_to_domain(period.0);
        ttf.with_simplification()
    }

    /// Returns the total utility of the trip given the departure time.
    pub fn get_total_utility(&self, departure_time: Time<T>) -> Utility<T> {
        let mut current_time = departure_time;
        let mut total_travel_time = Time::default();
        let mut utility = self.origin_schedule_utility.get_utility(departure_time);
        for leg in &self.legs {
            let (tt, u) = leg.get_travel_time_and_utility(current_time);
            utility += u;
            // Departure time for next leg.
            current_time += tt + leg.stopping_time;
            total_travel_time += tt;
        }
        utility += self
            .total_travel_utility
            .get_travel_utility(total_travel_time);
        utility
    }

    /// Returns the total stopping time of the trip, i.e., the sum of the stopping time for each
    /// leg.
    fn get_total_stopping_time(&self) -> Time<T> {
        self.legs.iter().map(|l| l.stopping_time).sum()
    }

    /// Returns a [PwlXYF] that yields the utility for each possible departure time.
    pub fn get_utility_function(
        &self,
        period: Interval<T>,
    ) -> PwlXYF<Time<T>, Utility<T>, NoUnit<T>> {
        let ttf = self.get_global_ttf_with_breakpoints(period);

        // Convert the ttf to vectors of departure times and travel times.
        let (tds, tts) = match ttf {
            TTF::Constant(tt) => (period.to_vec(), vec![tt; 2]),
            TTF::Piecewise(pwl_ttf) => pwl_ttf.into_xs_and_ys(),
        };
        debug_assert_eq!(tds[0], period.start());
        debug_assert_eq!(tds[tds.len() - 1], period.end());

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
        for leg in self.legs.iter() {
            // Add the leg-specific travel-time utility and schedule utility, and update the
            // current times.
            let tt_iter = leg.ttf.iter_eval(current_times.clone().into_iter());
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
        debug_assert_eq!(
            current_times,
            tds.iter()
                .zip(tts.iter())
                .map(|(&td, &tt)| td + tt)
                .collect::<Vec<_>>(),
        );
        PwlXYF::from_x_and_y(tds, utilities)
    }

    /// Returns the pre-day choice for this mode.
    ///
    /// The pre-day results are expected to be the same at each iteration (because nothing change)
    /// so they are computed at the first iteration, then we simply need to retrieve them (see
    /// [OnceCell]).
    pub fn get_pre_day_choice(&self) -> Result<(Utility<T>, Time<T>)> {
        let choice = self.choice.get_or_try_init(|| self.make_pre_day_choice())?;
        Ok((choice.expected_utility, choice.departure_time))
    }

    /// Computes the pre-day choice for this mode.
    fn make_pre_day_choice(&self) -> Result<FixedTTFPreDayResults<T>> {
        match &self.departure_time_model {
            &DepartureTimeModel::Constant(departure_time) => {
                let expected_utility = self.get_total_utility(departure_time);
                Ok(FixedTTFPreDayResults {
                    departure_time,
                    expected_utility,
                })
            }
            DepartureTimeModel::ContinuousChoice {
                period,
                choice_model,
            } => {
                let utilities = self.get_utility_function(*period);
                let (time_callback, expected_utility) = choice_model.get_choice(utilities)?;
                let departure_time = (time_callback)();
                Ok(FixedTTFPreDayResults {
                    departure_time,
                    expected_utility,
                })
            }
        }
    }

    /// Returns a vector with the travel time on each leg of the trip, given the departure time
    /// from origin.
    fn get_leg_travel_times_at(&self, departure_time: Time<T>) -> Vec<Time<T>> {
        let mut tts = Vec::with_capacity(self.legs.len());
        let mut current_time = departure_time;
        for leg in self.legs.iter() {
            let tt = leg.ttf.eval(current_time);
            tts.push(tt);
            current_time += tt + leg.stopping_time;
        }
        tts
    }

    /// Returns the total travel time of the trip at the given departure time.
    pub fn get_total_travel_time_at(&self, departure_time: Time<T>) -> Time<T> {
        self.get_leg_travel_times_at(departure_time)
            .into_iter()
            .sum::<Time<T>>()
            + self.get_total_stopping_time()
    }
}

/// Struct to store aggregate results specific to [FixedTTFMode].
#[derive(Debug, Clone, Deserialize, Serialize, JsonSchema)]
pub struct AggregateFixedTTFResults<T> {
    /// Number of trips taken with a FixedTTFMode.
    pub count: usize,
    /// Distribution of departure times.
    pub departure_times: Distribution<Time<T>>,
    /// Distribution of arrival times.
    pub arrival_times: Distribution<Time<T>>,
    /// Distribution of total travel times.
    pub travel_times: Distribution<Time<T>>,
    /// Distribution of total stopping time.
    pub stopping_times: Distribution<Time<T>>,
    /// Distribution of leg-specific travel times.
    pub leg_times: Distribution<Time<T>>,
    /// Distribution of number of legs taken.
    pub leg_counts: Distribution<T>,
    /// Distribution of total utility.
    pub utilities: Distribution<Utility<T>>,
}

impl<T: TTFNum> AggregateFixedTTFResults<T> {
    /// Compute [AggregateFixedTTFResults] from the results of an iteration.
    pub fn from_agent_results(results: Vec<(&FixedTTFMode<T>, &AgentResult<T>)>) -> Self {
        let msg = "Invalid within-day results";
        assert!(!results.is_empty(), "{msg}");
        let departure_times = Distribution::from_iterator(
            results.iter().map(|(_, r)| r.departure_time().expect(msg)),
        )
        .unwrap();
        let arrival_times =
            Distribution::from_iterator(results.iter().map(|(_, r)| r.arrival_time().expect(msg)))
                .unwrap();
        let travel_times =
            Distribution::from_iterator(results.iter().map(|(_, r)| r.travel_time().expect(msg)))
                .unwrap();
        let stopping_times =
            Distribution::from_iterator(results.iter().map(|(m, _)| m.get_total_stopping_time()))
                .unwrap();
        let leg_times = Distribution::from_iterator(results.iter().flat_map(|(m, r)| {
            m.get_leg_travel_times_at(r.departure_time().unwrap())
                .into_iter()
        }))
        .unwrap();
        let leg_counts = Distribution::from_iterator(
            results
                .iter()
                .map(|(m, _)| T::from_usize(m.legs.len()).unwrap()),
        )
        .unwrap();
        let utilities =
            Distribution::from_iterator(results.iter().map(|(_, r)| r.utility().expect(msg)))
                .unwrap();
        AggregateFixedTTFResults {
            count: results.len(),
            departure_times,
            arrival_times,
            travel_times,
            stopping_times,
            leg_times,
            leg_counts,
            utilities,
        }
    }
}

#[cfg(test)]
mod tests {
    use ttf::PwlTTF;

    use super::*;
    use crate::{
        schedule_utility::alpha_beta_gamma::AlphaBetaGammaModel,
        travel_utility::PolynomialFunction, units::ValueOfTime,
    };

    fn get_leg0() -> FixedTTFLeg<f64> {
        let ttf = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
            (Time(0.), Time(5.)),
            (Time(10.), Time(10.)),
            (Time(20.), Time(5.)),
        ]));
        let travel_utility = TravelUtility::Polynomial(PolynomialFunction {
            b: 5.0,
            ..Default::default()
        });
        let schedule_utility = ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(11.), Time(11.), ValueOfTime(1.), ValueOfTime(2.))
                .unwrap(),
        );
        FixedTTFLeg {
            ttf,
            travel_utility,
            schedule_utility,
            stopping_time: Time(5.0),
        }
    }

    fn get_leg1() -> FixedTTFLeg<f64> {
        let ttf = TTF::Constant(Time(5.));
        let travel_utility = TravelUtility::Polynomial(PolynomialFunction {
            a: 1.0,
            ..Default::default()
        });
        let schedule_utility = ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(21.), Time(24.), ValueOfTime(1.), ValueOfTime(2.))
                .unwrap(),
        );
        FixedTTFLeg {
            ttf,
            travel_utility,
            schedule_utility,
            stopping_time: Time::zero(),
        }
    }

    fn get_mode() -> FixedTTFMode<f64> {
        let departure_time_model = DepartureTimeModel::Constant(Time(5.0));
        let total_travel_utility = TravelUtility::Polynomial(PolynomialFunction {
            b: -10.0,
            ..Default::default()
        });
        let origin_schedule_utility = ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(5.), Time(5.), ValueOfTime(1.), ValueOfTime(2.)).unwrap(),
        );
        FixedTTFMode {
            legs: vec![get_leg0(), get_leg1()],
            departure_time_model,
            total_travel_utility,
            origin_schedule_utility,
            choice: OnceCell::new(),
        }
    }

    #[test]
    fn get_travel_time_and_utility_leg_test() {
        let leg = get_leg0();
        // Departure time: 5
        // Travel time: 7.5
        // Arrival time: 5 + 7.5 = 12.5
        // Late-delay: 12.5 - 11.0 = 1.5
        // Schedule utility: 1.5 * -2 = -3
        // Travel utility: 5 * 7.5 = 37.5
        // Total utility: 37.5 - 3 = 34.5
        assert_eq!(
            leg.get_travel_time_and_utility(Time(5.)),
            (Time(7.5), Utility(34.5))
        );
    }

    #[test]
    fn get_utility_at_leg_test() {
        let leg = get_leg0();
        // Departure time: 0
        // Travel time: 5
        // Arrival time: 0 + 5 = 5
        // Early-delay: 11 - 5 = 6
        // Schedule utility: 6 * -1 = -6
        // Travel utility: 5 * 5 = 25
        // Total utility: 25 - 6 = 19
        assert_eq!(leg.get_utility_at(Time(0.), Time(5.)), Utility(19.));
    }

    #[test]
    fn get_global_ttf_test() {
        let mode = get_mode();
        let ttf = TTF::Piecewise(PwlTTF::from_breakpoints(vec![
            (Time(0.), Time(15.)),
            (Time(10.), Time(20.)),
            (Time(20.), Time(15.)),
        ]));
        assert_eq!(mode.get_global_ttf(), ttf);
    }

    #[test]
    fn get_global_ttf_with_breakpoints_test() {
        let mode = get_mode();
        // Breakpoint at td = 5 for schedule utility at origin (with tt = 7.5 + 5 + 5).
        // Breakpoint at td = 4 for schedule utility at stop of leg 1 (with tt = 7 + 5 + 5).
        // Breakpoint at td = 6 for schedule utility at stop of leg 2 (with tt = 8 + 5 + 5).
        // Breakpoint at td = 15 to accomodate for the period (with tt = 7.5 + 5 + 5).
        let ttf = TTF::Piecewise(
            PwlTTF::<Time<f64>, NoSimplification>::from_breakpoints(vec![
                (Time(0.), Time(15.)),
                (Time(4.), Time(17.)),
                (Time(5.), Time(17.5)),
                (Time(6.), Time(18.)),
                (Time(10.), Time(20.)),
                (Time(15.), Time(17.5)),
            ])
            .with_simplification(),
        );
        assert_eq!(
            mode.get_global_ttf_with_breakpoints(Interval([Time(0.), Time(15.)])),
            ttf
        );
    }

    #[test]
    fn get_total_stopping_time_test() {
        let mode = get_mode();
        assert_eq!(mode.get_total_stopping_time(), Time(5.));
    }

    #[test]
    fn get_total_utility_mode_test() {
        let mode = get_mode();
        // Departure time: 2
        // Travel time for leg 0: 6
        // Arrival time at stop 0: 8
        // Stopping time at stop 0: 5
        // Departure time at stop 0: 13
        // Travel time for leg 1: 5
        // Arrival time at stop 1: 18
        assert_eq!(mode.get_total_travel_time_at(Time(2.)), Time(16.));
        // Schedule utility at origin: 3 * -1 = -3
        // Total travel utility: -10 * 11 = -110
        // Travel utility for leg 0: 5 * 6 = 30
        // Schedule utility at stop 0: 3 * -1 = -3
        // Travel utility for leg 1: 1
        // Schedule utility at stop 1: 3 * -1 = -3
        // Total utility: -3 - 110 + 30 - 3 + 1 - 3 = -88
        assert_eq!(mode.get_total_utility(Time(2.)), Utility(-88.));
    }

    #[test]
    fn get_utility_function_test() {
        let mode = get_mode();
        let utilities = PwlXYF::from_breakpoints(vec![
            (Time(2.), mode.get_total_utility(Time(2.))),
            (Time(4.), mode.get_total_utility(Time(4.))),
            (Time(5.), mode.get_total_utility(Time(5.))),
            (Time(6.), mode.get_total_utility(Time(6.))),
        ]);
        assert_eq!(
            mode.get_utility_function(Interval([Time(2.), Time(6.)])),
            utilities
        );
    }
}
