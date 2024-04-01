// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis_core::learning::LearningModel;
use metropolis_core::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis_core::mode::Mode;
use metropolis_core::network::road_network::parameters::RoadNetworkParameters;
use metropolis_core::network::road_network::vehicle::{SpeedFunction, Vehicle};
use metropolis_core::network::road_network::{RoadEdge, RoadNetwork, SpeedDensityFunction};
use metropolis_core::network::{Network, NetworkWeights};
use metropolis_core::parameters::Parameters;
use metropolis_core::population::Agent;
use metropolis_core::schedule_utility::ScheduleUtility;
use metropolis_core::travel_utility::TravelUtility;
use metropolis_core::units::{Flow, Interval, Lanes, Length, NoUnit, Speed, Time, PCE};

fn init_simulation() {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 2., 1., 3.];
    let origins = vec![0, 1, 2, 3];
    let destinations = vec![3, 0, 1, 2];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, (dt, (o, d))) in departure_times
        .into_iter()
        .zip(origins.into_iter().zip(destinations.into_iter()))
        .enumerate()
    {
        let leg = Leg::new(
            1,
            LegType::Road(RoadLeg::new(o, d, 1)),
            Time::default(),
            TravelUtility::default(),
            ScheduleUtility::None,
        );
        let trip = TravelingMode::new(
            1,
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

    // Create a road network with 4 edges, with infinite capacities, free-flow travel time of 5
    // seconds and length of 5 meters.
    let edges = vec![
        (
            0,
            1,
            RoadEdge::new(
                0,
                Speed(1.0),
                Length(5.0),
                Lanes(1.0),
                SpeedDensityFunction::FreeFlow,
                Flow(f64::INFINITY),
                Time(0.),
                true,
            ),
        ),
        (
            1,
            2,
            RoadEdge::new(
                1,
                Speed(1.0),
                Length(5.0),
                Lanes(1.0),
                SpeedDensityFunction::FreeFlow,
                Flow(f64::INFINITY),
                Time(0.),
                true,
            ),
        ),
        (
            2,
            3,
            RoadEdge::new(
                2,
                Speed(1.0),
                Length(5.0),
                Lanes(1.0),
                SpeedDensityFunction::FreeFlow,
                Flow(f64::INFINITY),
                Time(0.),
                true,
            ),
        ),
        (
            3,
            0,
            RoadEdge::new(
                3,
                Speed(1.0),
                Length(5.0),
                Lanes(1.0),
                SpeedDensityFunction::FreeFlow,
                Flow(f64::INFINITY),
                Time(0.),
                true,
            ),
        ),
    ];
    // Vehicles are 6 meters long: 1 vehicle is enough to block an edge.
    let vehicle = Vehicle::new(
        1,
        Length(6.0),
        PCE(1.0),
        SpeedFunction::Base,
        HashSet::new(),
        HashSet::new(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![vehicle]);
    let network = Network::new(Some(road_network));

    let parameters = Parameters {
        period: Interval([Time(0.0), Time(50.0)]),
        learning_model: LearningModel::Exponential(NoUnit(0.0)),
        road_network: Some(RoadNetworkParameters {
            spillback: true,
            max_pending_duration: Time(10.0),
            backward_wave_speed: None,
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
fn gridlock_test() {
    init_simulation();
    let preprocess_data = metropolis_core::simulation::preprocess().unwrap();
    let rn_weights = metropolis_core::network::road_network::free_flow_weights(
        &preprocess_data.network.get_road_network().unwrap(),
    );
    let weights = NetworkWeights::new(Some(rn_weights));
    let results =
        metropolis_core::simulation::run_iteration(weights, None, None, 1, &preprocess_data)
            .unwrap();
    let agent_results = results.iteration_results.agent_results();

    // Departure times: 0, 2, 1, 3.
    //
    // Arrival times at end of first edge: 5, 7, 6, 8.
    //
    // Vehicle 1 is released at time 15 (10 seconds after being pending).
    // This triggers the release of all vehicles, at the same time.
    //
    // They all reach the second edge of their trip at time 15 + 5 = 20.
    //
    // Vehicle 1 is a phantom so there is no gridlock to enter the third edge.
    //
    // They all reached their destination at time 25.

    let expected_arrival_times = vec![25., 25., 25., 25.];
    for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
        let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
        assert_eq!(ta, Time(exp_ta), "Agent result: {:?}", agent_res);
    }

    let expected_in_bottleneck_times = vec![10., 8., 9., 7.];
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

    let expected_travel_times = vec![15., 15., 15., 15.];
    for (agent_res, &exp_t) in agent_results.iter().zip(expected_travel_times.iter()) {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .road_time;
        assert_eq!(t, Time(exp_t), "Agent result: {:?}", agent_res);
    }

    let expected_out_bottleneck_times = vec![0., 0., 0., 0.];
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
}
