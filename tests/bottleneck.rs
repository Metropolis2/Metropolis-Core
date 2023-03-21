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
use metropolis::network::road_network::{
    RoadEdge, RoadNetwork, RoadNetworkParameters, SpeedDensityFunction,
};
use metropolis::network::{Network, NetworkParameters};
use metropolis::parameters::Parameters;
use metropolis::schedule_utility::ScheduleUtility;
use metropolis::simulation::Simulation;
use metropolis::stop::StopCriterion;
use metropolis::travel_utility::TravelUtility;
use metropolis::units::{Flow, Interval, Length, Speed, Time, PCE};
use petgraph::graph::{edge_index, node_index, DiGraph};
use ttf::TTF;

fn get_simulation(overtaking: bool) -> Simulation<f64> {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 3., 4., 5., 10., 21.];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, dt) in departure_times.into_iter().enumerate() {
        let leg = Leg::new(
            LegType::Road(RoadLeg::new(node_index(0), node_index(2), vehicle_index(0))),
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

    // Create a road network with 2 edges, with capacities 1 vehicle each 2 seconds and 1 vehicle
    // each 4 seconds, respectively.
    // Travel time is 1 second free-flow.
    let graph = DiGraph::from_edges(&[
        (
            0,
            1,
            RoadEdge::new(
                Speed(1.0),
                Length(1.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow(0.5),
                Time(0.),
                overtaking,
            ),
        ),
        (
            1,
            2,
            RoadEdge::new(
                Speed(1.0),
                Length(1.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow(0.25),
                Time(0.),
                overtaking,
            ),
        ),
    ]);
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
        network: NetworkParameters {
            road_network: Some(RoadNetworkParameters {
                contraction: Default::default(),
                recording_interval: Time(1.0),
                max_pending_duration: Time(f64::INFINITY),
                spillback: false,
            }),
        },
        init_iteration_counter: 1,
        update_ratio: 1.0,
        random_seed: None,
        nb_threads: 0,
    };

    Simulation::new(agents, network, parameters)
}

#[test]
fn bottleneck_no_overtaking_test() {
    let simulation = get_simulation(false);
    let preprocess_data = simulation.preprocess().unwrap();
    let weights = simulation
        .get_network()
        .get_free_flow_weights(&preprocess_data.network);
    let results = simulation
        .run_iteration(&weights, None, 1, &preprocess_data)
        .unwrap();
    let agent_results = results.iteration_results.agent_results();

    // Departure times: 0, 3, 4, 5, 10, 21.
    // Edge 1 entry times: 0, 3, 5, 7, 10, 21.
    // Travel time on edge 1 is always 1 second.
    // Edge 1 exit reached: 1, 4, 6, 8, 11, 22.
    // Edge 1 exit times: 1, 5, 7, 11, 15, 22.
    // Edge 2 entry times: 1, 5, 9, 13, 17, 22.
    // Travel time on edge 2 is always 1 second.
    // Arrival times: 2, 6, 10, 14, 18, 23.
    //
    // Total travel times: 2, 3, 6, 9, 8, 2.

    let expected_arrival_times = vec![2., 6., 10., 14., 18., 23.];
    for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
        let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
        assert_eq!(ta, Time(exp_ta), "Agent result: {:?}", agent_res);
    }

    let expected_in_bottleneck_times = vec![0., 1., 3., 4., 2., 0.];
    for (agent_res, &exp_t) in agent_results
        .iter()
        .zip(expected_in_bottleneck_times.iter())
    {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .in_bottleneck_time;
        assert_eq!(t, Time(exp_t), "Agent result: {:?}", agent_res);
    }

    let expected_travel_times = vec![2., 2., 2., 2., 2., 2.];
    for (agent_res, &exp_t) in agent_results.iter().zip(expected_travel_times.iter()) {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .road_time;
        assert_eq!(t, Time(exp_t), "Agent result: {:?}", agent_res);
    }

    let expected_out_bottleneck_times = vec![0., 0., 1., 3., 4., 0.];
    for (agent_res, &exp_t) in agent_results
        .iter()
        .zip(expected_out_bottleneck_times.iter())
    {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .out_bottleneck_time;
        assert_eq!(t, Time(exp_t), "Agent result: {:?}", agent_res);
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
        (Time(0.), Time(50.)),
        "The period of the TTF should be equal to the period of the simulation"
    );
}

#[test]
fn bottleneck_overtaking_test() {
    let simulation = get_simulation(true);
    let preprocess_data = simulation.preprocess().unwrap();
    let weights = simulation
        .get_network()
        .get_free_flow_weights(&preprocess_data.network);
    let results = simulation
        .run_iteration(&weights, None, 1, &preprocess_data)
        .unwrap();
    let agent_results = results.iteration_results.agent_results();

    // Departure times: 0, 3, 4, 5, 10, 21.
    // Edge 1 entry times: 0, 3, 5, 7, 10, 21.
    // Travel time on edge 1 is always 1 second.
    // Edge 1 exit reached: 1, 4, 6, 8, 11, 22.
    // Edge 1 exit times: 1, 4, 6, 8, 11, 22.
    // Edge 2 entry times: 1, 5, 9, 13, 17, 22.
    // Travel time on edge 2 is always 1 second.
    // Arrival times: 2, 6, 10, 14, 18, 23.
    //
    // Total travel times: 2, 3, 6, 9, 8, 2.

    let expected_arrival_times = vec![2., 6., 10., 14., 18., 23.];
    for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
        let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
        assert_eq!(ta, Time(exp_ta), "Agent result: {:?}", agent_res);
    }

    let expected_in_bottleneck_times = vec![0., 1., 4., 7., 6., 0.];
    for (agent_res, &exp_t) in agent_results
        .iter()
        .zip(expected_in_bottleneck_times.iter())
    {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .in_bottleneck_time;
        assert_eq!(t, Time(exp_t), "Agent result: {:?}", agent_res);
    }

    let expected_travel_times = vec![2., 2., 2., 2., 2., 2.];
    for (agent_res, &exp_t) in agent_results.iter().zip(expected_travel_times.iter()) {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .road_time;
        assert_eq!(t, Time(exp_t), "Agent result: {:?}", agent_res);
    }

    let expected_out_bottleneck_times = vec![0., 0., 0., 0., 0., 0.];
    for (agent_res, &exp_t) in agent_results
        .iter()
        .zip(expected_out_bottleneck_times.iter())
    {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .out_bottleneck_time;
        assert_eq!(t, Time(exp_t), "Agent result: {:?}", agent_res);
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
        (Time(0.), Time(50.)),
        "The period of the TTF should be equal to the period of the simulation"
    );
}
