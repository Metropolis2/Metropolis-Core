// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis::agent::{agent_index, Agent};
use metropolis::learning::LearningModel;
use metropolis::mode::trip::event::RoadEvent;
use metropolis::mode::trip::results::{LegResults, LegTypeResults, RoadLegResults, TripResults};
use metropolis::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis::mode::{mode_index, Mode, ModeResults};
use metropolis::network::road_network::vehicle::{vehicle_index, SpeedFunction, Vehicle};
use metropolis::network::road_network::{
    RoadEdge, RoadNetwork, RoadNetworkParameters, SpeedDensityFunction,
};
use metropolis::network::{Network, NetworkParameters};
use metropolis::parameters::Parameters;
use metropolis::schedule_utility::alpha_beta_gamma::AlphaBetaGammaModel;
use metropolis::schedule_utility::ScheduleUtility;
use metropolis::simulation::results::AgentResult;
use metropolis::simulation::Simulation;
use metropolis::stop::StopCriterion;
use metropolis::travel_utility::{PolynomialFunction, TravelUtility};
use metropolis::units::{Flow, Interval, Length, Speed, Time, Utility, ValueOfTime, PCE};
use num_traits::Float;
use ttf::{PwlTTF, TTF};

fn get_simulation() -> Simulation<f64> {
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
                1,
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
                1,
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Time(0.),
                true,
            ),
        ),
    ];
    let v0 = Vehicle::new(
        Length(1.0),
        PCE(1.0),
        SpeedFunction::Base,
        HashSet::new(),
        HashSet::new(),
    );
    let v1 = Vehicle::new(
        Length(1.0),
        PCE(1.0),
        SpeedFunction::Multiplicator(0.5),
        HashSet::new(),
        HashSet::new(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![v0, v1]);
    let network = Network::new(Some(road_network));

    // Create an agent with 4 legs (3 road and 1 virtual).
    let mut agents = Vec::with_capacity(1);
    let leg0 = Leg::new(
        1,
        LegType::Road(RoadLeg::new(0, 1, vehicle_index(0))),
        Time(2.0),
        TravelUtility::Polynomial(PolynomialFunction {
            a: 1.0,
            b: -1.0,
            c: 1.0,
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
            b: -1.0,
            ..Default::default()
        }),
        ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(Time(10.0), Time(10.0), ValueOfTime(0.1), ValueOfTime(0.2))
                .unwrap(),
        ),
    );
    let leg2 = Leg::new(
        3,
        LegType::Road(RoadLeg::new(2, 3, vehicle_index(1))),
        Time(1.0),
        TravelUtility::Polynomial(PolynomialFunction {
            a: 5.0,
            ..Default::default()
        }),
        ScheduleUtility::None,
    );
    // 4th leg is a road leg with origin = destination (to test if this case works).
    let leg3 = Leg::new(
        4,
        LegType::Road(RoadLeg::new(2, 2, vehicle_index(1))),
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
            c: -2.0,
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
        learning_model: LearningModel::Exponential(0.0),
        stopping_criteria: vec![StopCriterion::MaxIteration(1)],
        network: NetworkParameters {
            road_network: Some(RoadNetworkParameters {
                contraction: Default::default(),
                recording_interval: Time(1.0),
                approximation_bound: Time(0.0),
                max_pending_duration: Time(f64::INFINITY),
                spillback: false,
                algorithm_type: Default::default(),
            }),
        },
        init_iteration_counter: 1,
        update_ratio: 1.0,
        random_seed: None,
        nb_threads: 0,
        saving_format: Default::default(),
    };

    Simulation::new(agents, network, parameters)
}

#[test]
fn legs_test() {
    let simulation = get_simulation();
    let preprocess_data = simulation.preprocess().unwrap();
    let weights = simulation
        .get_network()
        .get_free_flow_weights(&preprocess_data.network);
    let results = simulation
        .run_iteration(weights, None, None, 1, &preprocess_data)
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
        class: LegTypeResults::Virtual,
    };
    let leg2_results = LegResults {
        id: 3,
        departure_time: Time(13.0),
        arrival_time: Time(17.0),
        travel_utility: Utility(5.0),
        schedule_utility: Utility(0.0),
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
        class: LegTypeResults::Road(RoadLegResults {
            expected_route: None,
            route: vec![],
            road_time: Time(0.0),
            in_bottleneck_time: Time(0.0),
            out_bottleneck_time: Time(0.0),
            route_free_flow_travel_time: Time(0.0),
            global_free_flow_travel_time: Time(0.0),
            length: Length(0.0),
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
