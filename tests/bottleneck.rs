// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis::agent::Agent;
use metropolis::learning::{ExponentialLearningModel, LearningModel};
use metropolis::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis::mode::Mode;
use metropolis::network::road_network::vehicle::{vehicle_index, SpeedFunction, Vehicle};
use metropolis::network::road_network::{RoadEdge, RoadNetwork, SpeedDensityFunction};
use metropolis::network::Network;
use metropolis::parameters::Parameters;
use metropolis::schedule_utility::ScheduleUtility;
use metropolis::simulation::Simulation;
use metropolis::stop::StopCriterion;
use metropolis::travel_utility::TravelUtility;
use metropolis::units::{Flow, Interval, Length, Speed, Time, PCE};
use petgraph::graph::{edge_index, node_index, DiGraph};
use ttf::{TTFNum, TTF};

fn get_simulation() -> Simulation<f64> {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 3., 4., 5., 10., 21.];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, dt) in departure_times.into_iter().enumerate() {
        let leg = Leg::new(
            LegType::Road(RoadLeg::new(node_index(0), node_index(1), vehicle_index(0))),
            Time::default(),
            TravelUtility::default(),
            ScheduleUtility::None,
        );
        let trip = TravelingMode::new(
            vec![leg],
            Time::default(),
            DepartureTimeModel::Constant(Time(dt)),
            TravelUtility::default(),
            ScheduleUtility::None,
            ScheduleUtility::None,
        );
        let agent = Agent::new(i, vec![Mode::Trip(trip)], None);
        agents.push(agent);
    }

    // Create a 1-road network that has an in-bottleneck with a capacity of 1 vehicle each 2 seconds
    // and an out-bottleneck with a capacity of 1 vehicle each 4 seconds.
    let graph = DiGraph::from_edges(&[(
        0,
        1,
        RoadEdge::new(
            Speed(1.0),
            Length(1.0),
            1,
            SpeedDensityFunction::FreeFlow,
            Flow(0.5),
            Flow(0.25),
            false,
            Time(0.),
        ),
    )]);
    let vehicle = Vehicle::new(
        Length(1.0),
        PCE(1.0),
        SpeedFunction::Base,
        HashSet::new(),
        HashSet::new(),
    );
    let road_network = RoadNetwork::new(graph, vec![vehicle]);
    let network = Network::new(Some(road_network));

    let parameters = Parameters {
        period: Interval([Time(0.0), Time(50.0)]),
        learning_model: LearningModel::Exponential(ExponentialLearningModel::new(0.0)),
        stopping_criteria: vec![StopCriterion::MaxIteration(1)],
        ..Default::default()
    };

    Simulation::new(agents, network, parameters)
}

#[test]
fn bottleneck_test() {
    let simulation = get_simulation();
    let preprocess_data = simulation.preprocess().unwrap();
    let weights = simulation
        .get_network()
        .get_free_flow_weights(&preprocess_data.network);
    let results = simulation
        .run_iteration(&weights, None, 1, &preprocess_data)
        .unwrap();
    let agent_results = results.iteration_results.agent_results();

    // Departure times: 0, 3, 4, 5, 10, 21.
    // In-bottleneck exit times: 0, 3, 5, 7, 10, 21.
    // Travel time on the road segment is always 1 second.
    // Out-bottleneck entry times: 1, 4, 6, 8, 11, 22.
    // Arrival times: 1, 5, 9, 13, 17, 22.

    // Entry / Exit times for the entry bottleneck.
    // 0 -> 0
    // 3 -> 3
    // 4 -> 5
    // 5 -> 7
    // 7 -> 7 (virtual)
    // 10 -> 10
    // 21 -> 21
    // Waiting times:
    // 0 -> 0
    // 3 -> 0
    // 4 -> 1
    // 5 -> 2
    // 7 -> 0
    // 10 -> 0
    // 21 -> 0

    // Entry / Exit times for the exit bottleneck.
    // 0 -> 0 (virtual)
    // 1 -> 1
    // 4 -> 5
    // 6 -> 9
    // 8 -> 13
    // 11 -> 17
    // 17 -> 17 (virtual)
    // 22 -> 22
    // Waiting times:
    // 0 -> 0
    // 1 -> 0
    // 4 -> 1
    // 6 -> 3
    // 8 -> 5
    // 11 -> 6
    // 17 -> 0
    // 22 -> 0

    let expected_arrival_times = vec![1., 5., 9., 13., 17., 22.];
    for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
        let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
        assert_eq!(
            ta,
            Time(exp_ta),
            "Expected arrival time: {:?}\nAgent result: {:?}",
            exp_ta,
            agent_res
        );
    }

    let weights = results
        .iteration_results
        .network_weights()
        .get_road_network()
        .unwrap();
    let edge_weight = &weights[(0, edge_index(0))];
    let TTF::Piecewise(ttf) = edge_weight else {
        panic!("TTF should be piecewise");
    };
    assert_eq!(
        ttf.period(),
        &[Time(0.), Time(50.)],
        "The period of the TTF should be equal to the period of the simulation"
    );
    // With departure time 0.0, the waiting time for the in-bottleneck is 0.0.
    // With departure time 1.0, the waiting time for the out-bottleneck is 0.0.
    let actual = ttf.eval(Time(0.));
    let expected = Time(0. + 1. + 0.);
    assert!(
        actual.approx_eq(&expected),
        "Invalid expected travel time when leaving at time 0.0: {actual:?} != {expected:?}"
    );
    // With departure time 3.0, the waiting time for the in-bottleneck is 0.0.
    // With departure time 4.0, the waiting time for the out-bottleneck is 1.0.
    let actual = ttf.eval(Time(3.));
    let expected = Time(0. + 1. + 1.);
    assert!(
        actual.approx_eq(&expected),
        "Invalid expected travel time when leaving at time 3.0: {actual:?} != {expected:?}"
    );
    // With departure time 6, the waiting time for the in-bottleneck is 1.
    // With departure time 6 + 1 + 1 = 8, the waiting time for the out-bottleneck is 5.
    let actual = ttf.eval(Time(6.));
    let expected = Time(1. + 1. + 5.);
    assert!(
        actual.approx_eq(&expected),
        "Invalid expected travel time when leaving at time 6.0: {actual:?} != {expected:?}"
    );
    // With departure time 13, the waiting time for the in-bottleneck is 0.
    // With departure time 14, the waiting time for the out-bottleneck is 3.
    let actual = ttf.eval(Time(13.));
    let expected = Time(0. + 1. + 3.);
    assert!(
        actual.approx_eq(&expected),
        "Invalid expected travel time when leaving at time 13.0: {actual:?} != {expected:?}"
    );
}
