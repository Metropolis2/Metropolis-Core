// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis_core::learning::LearningModel;
use metropolis_core::mode::trip::event::RoadEvent;
use metropolis_core::mode::trip::results::{
    LegResults, LegTypeResults, RoadLegResults, TripResults,
};
use metropolis_core::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis_core::mode::{mode_index, Mode, ModeResults};
use metropolis_core::network::road_network::parameters::RoadNetworkParameters;
use metropolis_core::network::road_network::vehicle::{SpeedFunction, Vehicle};
use metropolis_core::network::road_network::{RoadEdge, RoadNetwork, SpeedDensityFunction};
use metropolis_core::network::{Network, NetworkWeights};
use metropolis_core::parameters::Parameters;
use metropolis_core::population::{agent_index, Agent};
use metropolis_core::schedule_utility::alpha_beta_gamma::AlphaBetaGammaModel;
use metropolis_core::schedule_utility::ScheduleUtility;
use metropolis_core::simulation::results::AgentResult;
use metropolis_core::travel_utility::{PolynomialFunction, TravelUtility};
use metropolis_core::units::{
    Flow, Interval, Lanes, Length, NoUnit, Speed, Time, Utility, ValueOfTime, PCE,
};
use num_traits::Float;
use ttf::{PwlTTF, TTF};

fn init_simulation() {
    // Create a network with 4 nodes and 2 edges.
    // Edge 0: 0 -> 1 (free-flow tt: 1).
    // Edge 1: 2 -> 3 (free-flow tt: 2).
    let edges = vec![
        (
            0,
            1,
            RoadEdge::new(
                0,
                Speed(1.0),
                Length(1.0),
                Lanes(1.0),
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Time(0.),
                true,
            ),
        ),
        (
            2,
            3,
            RoadEdge::new(
                1,
                Speed(1.0),
                Length(2.0),
                Lanes(1.0),
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Time(0.),
                true,
            ),
        ),
    ];
    let v0 = Vehicle::new(
        1,
        Length(1.0),
        PCE(1.0),
        SpeedFunction::Base,
        HashSet::new(),
        HashSet::new(),
    );
    let v1 = Vehicle::new(
        2,
        Length(1.0),
        PCE(1.0),
        SpeedFunction::Multiplicator(NoUnit(0.5)),
        HashSet::new(),
        HashSet::new(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![v0, v1]);
    let network = Network::new(Some(road_network));

    // Create an agent with 4 legs (3 road and 1 virtual).
    let mut agents = Vec::with_capacity(1);
    let leg0 = Leg::new(
        1,
        LegType::Road(RoadLeg::new(0, 1, 1)),
        Time(2.0),
        TravelUtility::Polynomial(PolynomialFunction {
            a: Utility(1.0),
            b: ValueOfTime(-1.0),
            c: ValueOfTime(1.0),
            ..Default::default()
        }),
        ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(5.0), Time(6.0), ValueOfTime(0.5), ValueOfTime(2.0))
                .unwrap(),
        ),
    );
    let leg1 = Leg::new(
        2,
        LegType::Virtual(TTF::Piecewise(PwlTTF::from_values(
            vec![Time(0.), Time(10.), Time(5.)],
            Time(0.),
            Time(10.),
        ))),
        Time(1.0),
        TravelUtility::Polynomial(PolynomialFunction {
            b: ValueOfTime(-1.0),
            ..Default::default()
        }),
        ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(10.0), Time(10.0), ValueOfTime(0.1), ValueOfTime(0.2))
                .unwrap(),
        ),
    );
    let leg2 = Leg::new(
        3,
        LegType::Road(RoadLeg::new(2, 3, 2)),
        Time(1.0),
        TravelUtility::Polynomial(PolynomialFunction {
            a: Utility(5.0),
            ..Default::default()
        }),
        ScheduleUtility::None,
    );
    // 4th leg is a road leg with origin = destination (to test if this case works).
    let leg3 = Leg::new(
        4,
        LegType::Road(RoadLeg::new(2, 2, 2)),
        Time(0.0),
        TravelUtility::default(),
        ScheduleUtility::None,
    );
    let trip = TravelingMode::new(
        1,
        vec![leg0, leg1, leg2, leg3],
        Time(3.0),
        DepartureTimeModel::Constant(Time(0.)),
        TravelUtility::Polynomial(PolynomialFunction {
            c: ValueOfTime(-2.0),
            ..Default::default()
        }),
        ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(1.0), Time(1.0), ValueOfTime(2.0), ValueOfTime(2.0))
                .unwrap(),
        ),
        ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(15.0), Time(15.0), ValueOfTime(2.0), ValueOfTime(2.0))
                .unwrap(),
        ),
    );
    let agent = Agent::new(0, vec![Mode::Trip(trip)], None);
    agents.push(agent);

    let parameters = Parameters {
        period: Interval([Time(0.0), Time(50.0)]),
        learning_model: LearningModel::Exponential(NoUnit(0.0)),
        road_network: Some(RoadNetworkParameters {
            spillback: false,
            max_pending_duration: Time(f64::INFINITY),
            ..Default::default()
        }),
        max_iterations: 1,
        ..Default::default()
    };

    metropolis_core::parameters::init(parameters).unwrap();
    metropolis_core::population::init(agents).unwrap();
    metropolis_core::network::init(network).unwrap();
}

#[test]
fn legs_test() {
    init_simulation();
    let preprocess_data = metropolis_core::simulation::preprocess().unwrap();
    let rn_weights = metropolis_core::network::road_network::free_flow_weights(
        &preprocess_data.network.get_road_network().unwrap(),
    );
    let weights = NetworkWeights::new(Some(rn_weights));
    let results =
        metropolis_core::simulation::run_iteration(weights, None, None, 1, &preprocess_data)
            .unwrap();
    let agent_results = &results.iteration_results.agent_results()[agent_index(0)];

    // Departure time from origin: 0.
    // Departure time from origin of leg 0: 3.
    // Travel time on leg 0: 1.
    // Arrival time to destination of leg 0: 4.
    // Departure time from origin of leg 1: 6.
    // Travel time on leg 1: 6.
    // Arrival time to destination of leg 1: 12.
    // Departure time from origin of leg 2: 13.
    // Travel time on leg 2: 4 (2 fftt with multiplicator of 0.5).
    // Arrival time at destination of leg 2: 17.
    // Departure time from origin of leg 3: 18.
    // Arrival time at destination of leg 3: 18.
    // Arrival time at final destination: 18.
    //
    // Total travel time: 11.
    //
    // Utility for leg 0: (1 + (-1) * 1 + 1 * 1^2) - (5 - 4) * 0.5 = 1 - 0.5 = 0.5.
    // Utility for leg 1: (-1 * 6) - (12 - 10) * 0.2 = -6 - 0.4 = -6.4.
    // Utility for leg 2: 5 + 0 = 5.
    // Utility for leg 3: 0.
    // Origin schedule utility: -(1 - 0) * 2 = -2.
    // Destination schedule utility: -(18 - 15) * 2 = -6.
    // Total travel utility: -2 * 11^2 = -242.
    //
    // Total utility = -250.9.
    let leg0_results = LegResults {
        id: 1,
        departure_time: Time(3.0),
        arrival_time: Time(4.0),
        travel_utility: Utility(1.0),
        schedule_utility: Utility(-0.5),
        departure_time_shift: None,
        class: LegTypeResults::Road(RoadLegResults {
            expected_route: None,
            route: vec![RoadEvent {
                edge: 0,
                entry_time: Time(3.0),
            }],
            road_time: Time(1.0),
            in_bottleneck_time: Time(0.0),
            out_bottleneck_time: Time(0.0),
            route_free_flow_travel_time: Time(1.0),
            global_free_flow_travel_time: Time(1.0),
            length: Length(1.0),
            length_diff: None,
            pre_exp_departure_time: Time(3.0),
            pre_exp_arrival_time: Time(4.0),
            exp_arrival_time: Time(4.0),
        }),
    };
    let leg1_results = LegResults {
        id: 2,
        departure_time: Time(6.0),
        arrival_time: Time(12.0),
        travel_utility: Utility(-6.0),
        schedule_utility: Utility(-0.4),
        departure_time_shift: None,
        class: LegTypeResults::Virtual,
    };
    let leg2_results = LegResults {
        id: 3,
        departure_time: Time(13.0),
        arrival_time: Time(17.0),
        travel_utility: Utility(5.0),
        schedule_utility: Utility(0.0),
        departure_time_shift: None,
        class: LegTypeResults::Road(RoadLegResults {
            expected_route: None,
            route: vec![RoadEvent {
                edge: 1,
                entry_time: Time(13.0),
            }],
            road_time: Time(4.0),
            in_bottleneck_time: Time(0.0),
            out_bottleneck_time: Time(0.0),
            route_free_flow_travel_time: Time(4.0),
            global_free_flow_travel_time: Time(4.0),
            length: Length(2.0),
            length_diff: None,
            pre_exp_departure_time: Time(13.0),
            pre_exp_arrival_time: Time(17.0),
            exp_arrival_time: Time(17.0),
        }),
    };
    let leg3_results = LegResults {
        id: 4,
        departure_time: Time(18.0),
        arrival_time: Time(18.0),
        travel_utility: Utility(0.0),
        schedule_utility: Utility(0.0),
        departure_time_shift: None,
        class: LegTypeResults::Road(RoadLegResults {
            expected_route: None,
            route: vec![],
            road_time: Time(0.0),
            in_bottleneck_time: Time(0.0),
            out_bottleneck_time: Time(0.0),
            route_free_flow_travel_time: Time(0.0),
            global_free_flow_travel_time: Time(0.0),
            length: Length(0.0),
            length_diff: None,
            pre_exp_departure_time: Time(18.0),
            pre_exp_arrival_time: Time(18.0),
            exp_arrival_time: Time(18.0),
        }),
    };
    let expected_agent_results = AgentResult::new(
        0,
        1,
        mode_index(0),
        Utility(-250.9),
        ModeResults::Trip(TripResults {
            legs: vec![leg0_results, leg1_results, leg2_results, leg3_results],
            departure_time: Time(0.0),
            arrival_time: Time(18.0),
            total_travel_time: Time(11.0),
            utility: Utility(-250.9),
            expected_utility: Utility(-250.9),
            virtual_only: false,
            departure_time_shift: None,
        }),
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[0],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[0],
        "Problem with leg 0"
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[1],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[1],
        "Problem with leg 1"
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[2],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[2],
        "Problem with leg 2"
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[3],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[3],
        "Problem with leg 3"
    );

    assert_eq!(agent_results, &expected_agent_results);
}
