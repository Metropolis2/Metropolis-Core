// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis::agent::Agent;
use metropolis::learning::LearningModel;
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
use metropolis::units::{Flow, Interval, Lanes, Length, Speed, Time, PCE};

fn get_simulation() -> Simulation<f64> {
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
            LegType::Road(RoadLeg::new(o, d, vehicle_index(0))),
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
        Length(6.0),
        PCE(1.0),
        SpeedFunction::Base,
        HashSet::new(),
        HashSet::new(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![vehicle]);
    let network = Network::new(Some(road_network));

    let parameters = Parameters {
        input_files: Default::default(),
        output_directory: Default::default(),
        period: Interval([Time(0.0), Time(50.0)]),
        learning_model: LearningModel::Exponential(0.0),
        stopping_criteria: vec![StopCriterion::MaxIteration(1)],
        network: NetworkParameters {
            road_network: Some(RoadNetworkParameters {
                contraction: Default::default(),
                recording_interval: Time(1.0),
                approximation_bound: Time(0.0),
                spillback: true,
                backward_wave_speed: None,
                max_pending_duration: Time(10.0),
                constrain_inflow: true,
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
fn gridlock_test() {
    let simulation = get_simulation();
    let preprocess_data = simulation.preprocess().unwrap();
    let weights = simulation.get_network().get_free_flow_weights(
        simulation.get_parameters().period,
        &simulation.get_parameters().network,
        &preprocess_data.network,
    );
    let results = simulation
        .run_iteration(weights, None, None, 1, &preprocess_data)
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
