// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis_core::agent::Agent;
use metropolis_core::learning::LearningModel;
use metropolis_core::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis_core::mode::Mode;
use metropolis_core::network::road_network::preprocess::unique_vehicle_index;
use metropolis_core::network::road_network::vehicle::{SpeedFunction, Vehicle};
use metropolis_core::network::road_network::{
    RoadEdge, RoadNetwork, RoadNetworkParameters, SpeedDensityFunction,
};
use metropolis_core::network::Network;
use metropolis_core::parameters::Parameters;
use metropolis_core::schedule_utility::ScheduleUtility;
use metropolis_core::simulation::Simulation;
use metropolis_core::travel_utility::TravelUtility;
use metropolis_core::units::{Flow, Interval, Lanes, Length, Speed, Time, PCE};
use ttf::TTF;

fn get_simulation() -> Simulation<f64> {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 7., 5., 6., 9., 30.];
    let origins = vec![0, 1, 0, 0, 0, 0];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, (dt, o)) in departure_times
        .into_iter()
        .zip(origins.into_iter())
        .enumerate()
    {
        let leg = Leg::new(
            1,
            LegType::Road(RoadLeg::new(o, 2, 1)),
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

    // Create a road network with 2 edges, with infinite capacities, free-flow travel time of 10
    // seconds and length of 10 meters.
    let edges = vec![
        (
            0,
            1,
            RoadEdge::new(
                0,
                Speed(1.0),
                Length(10.0),
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
                Length(10.0),
                Lanes(1.0),
                SpeedDensityFunction::FreeFlow,
                Flow(f64::INFINITY),
                Time(0.),
                true,
            ),
        ),
    ];
    // Vehicles are 6 meters long: 2 vehicles are enough to block an edge.
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
        input_files: Default::default(),
        output_directory: Default::default(),
        period: Interval([Time(0.0), Time(50.0)]),
        learning_model: LearningModel::Exponential(0.0),
        road_network: Some(RoadNetworkParameters {
            contraction: Default::default(),
            recording_interval: Time(1.0),
            approximation_bound: Time(0.0),
            max_pending_duration: Time(f64::INFINITY),
            spillback: true,
            backward_wave_speed: None,
            constrain_inflow: true,
            algorithm_type: Default::default(),
        }),
        init_iteration_counter: 1,
        max_iterations: 1,
        update_ratio: 1.0,
        random_seed: None,
        nb_threads: 0,
        saving_format: Default::default(),
        only_compute_decisions: false,
    };

    Simulation::new(agents, network, parameters)
}

#[test]
fn spillback_test() {
    let simulation = get_simulation();
    let preprocess_data = simulation.preprocess().unwrap();
    let weights = simulation.get_network().get_free_flow_weights(
        simulation.get_parameters().period,
        simulation.get_parameters().road_network.as_ref(),
        &preprocess_data.network,
    );
    let results = simulation
        .run_iteration(weights, None, None, 1, &preprocess_data)
        .unwrap();
    let agent_results = results.iteration_results.agent_results();

    // Departure times: 0, 7, 5, 6, 9, 30.
    // Origins: 0, 1, 0, 0, 0, 0.
    // Edge 1 entry times: 0, NA, 5, 10, 15, 30.
    // Travel time on edge 1 is always 10 second.
    // Edge 1 exit reached: 10, NA, 15, 20, 25, 40.
    // Edge 2 entry times: 10, 7, 17, 20, 27, 40.
    // Travel time on edge 2 is always 10 second.
    // Arrival times: 20, 17, 27, 30, 37, 50.
    //
    // Edge 1 is full from 5 to 10, then from 10 to 15, then from 15 to 20.
    // Edge 2 is full from 10 to 17, then from 17 to 20, then from 20 to 27, then from 27 to 30.
    //
    // Total travel times: 20, 10, 22, 24, 28, 20.

    let expected_arrival_times = vec![20., 17., 27., 30., 37., 50.];
    for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
        let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
        assert_eq!(ta, Time(exp_ta), "Agent result: {:?}", agent_res);
    }

    let expected_in_bottleneck_times = vec![0., 0., 2., 4., 8., 0.];
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

    let expected_travel_times = vec![20., 10., 20., 20., 20., 20.];
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

    let weights = results.iteration_results.new_exp_weights.clone();
    let weights = weights.road_network().unwrap();
    let uid = unique_vehicle_index(0);
    let edge_weight = &weights[(uid, 0)];
    let TTF::Piecewise(ttf) = edge_weight else {
        panic!("TTF should be piecewise");
    };
    assert_eq!(
        ttf.period(),
        (Time(0.), Time(50.)),
        "The period of the TTF should be equal to the period of the simulation"
    );
}
