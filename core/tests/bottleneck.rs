// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis_core::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis_core::mode::Mode;
use metropolis_core::network::road_network::parameters::RoadNetworkParameters;
use metropolis_core::network::road_network::preprocess::unique_vehicle_index;
use metropolis_core::network::road_network::vehicle::{SpeedFunction, Vehicle};
use metropolis_core::network::road_network::{RoadEdge, RoadNetwork, SpeedDensityFunction};
use metropolis_core::network::{Network, NetworkWeights};
use metropolis_core::parameters::Parameters;
use metropolis_core::population::Agent;
use metropolis_core::schedule_utility::ScheduleUtility;
use metropolis_core::travel_utility::TravelUtility;
use metropolis_core::units::*;
use num_traits::{ConstOne, ConstZero};
use ttf::TTF;

fn init_simulation(overtaking: bool) {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 3., 4., 5., 10., 21.];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, dt) in departure_times.into_iter().enumerate() {
        let leg = Leg::new(
            1,
            LegType::Road(RoadLeg::new(0, 2, 1)),
            NonNegativeSeconds::ZERO,
            TravelUtility::default(),
            ScheduleUtility::None,
        );
        let trip = TravelingMode::new(
            1,
            vec![leg],
            NonNegativeSeconds::ZERO,
            DepartureTimeModel::Constant(NonNegativeSeconds::try_from(dt).unwrap()),
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
    let edges = vec![
        (
            0,
            1,
            RoadEdge::new(
                0,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(1.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                Some(Flow::try_from(0.5).unwrap()),
                NonNegativeSeconds::ZERO,
                overtaking,
            ),
        ),
        (
            1,
            2,
            RoadEdge::new(
                1,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(1.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                Some(Flow::try_from(0.25).unwrap()),
                NonNegativeSeconds::ZERO,
                overtaking,
            ),
        ),
    ];
    let vehicle = Vehicle::new(
        1,
        NonNegativeMeters::try_from(1.0).unwrap(),
        PCE::ONE,
        SpeedFunction::Base,
        HashSet::new(),
        HashSet::new(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![vehicle]);
    let network = Network::new(Some(road_network));

    let parameters = Parameters {
        period: Interval::try_from([0.0, 50.0]).unwrap(),
        road_network: Some(RoadNetworkParameters {
            spillback: false,
            ..Default::default()
        }),
        max_iterations: 1,
        ..Default::default()
    };

    let _ = metropolis_core::parameters::init(parameters);
    let _ = metropolis_core::population::init(agents);
    metropolis_core::network::replace(network);
}

#[test]
fn bottleneck_test() {
    // OVERTAKING = FALSE
    init_simulation(false);
    let preprocess_data = metropolis_core::simulation::preprocess().unwrap();
    let rn_weights = metropolis_core::network::road_network::free_flow_weights(
        &preprocess_data.network.get_road_network().unwrap(),
    );
    let weights = NetworkWeights::new(Some(rn_weights));
    let results =
        metropolis_core::simulation::run_iteration(weights, None, None, 1, &preprocess_data)
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
        assert_eq!(
            ta,
            NonNegativeSeconds::try_from(exp_ta).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
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
        assert_eq!(
            t,
            NonNegativeSeconds::try_from(exp_t).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
    }

    let expected_travel_times = vec![2., 2., 2., 2., 2., 2.];
    for (agent_res, &exp_t) in agent_results.iter().zip(expected_travel_times.iter()) {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .road_time;
        assert_eq!(
            t,
            NonNegativeSeconds::try_from(exp_t).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
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
        assert_eq!(
            t,
            NonNegativeSeconds::try_from(exp_t).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
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
        (
            AnySeconds::try_from(0.).unwrap(),
            AnySeconds::try_from(50.).unwrap()
        ),
        "The period of the TTF should be equal to the period of the simulation"
    );

    // OVERTAKING = TRUE
    init_simulation(true);
    let preprocess_data = metropolis_core::simulation::preprocess().unwrap();
    let rn_weights = metropolis_core::network::road_network::free_flow_weights(
        &preprocess_data.network.get_road_network().unwrap(),
    );
    let weights = NetworkWeights::new(Some(rn_weights));
    let results =
        metropolis_core::simulation::run_iteration(weights, None, None, 1, &preprocess_data)
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
        assert_eq!(
            ta,
            NonNegativeSeconds::try_from(exp_ta).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
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
        assert_eq!(
            t,
            NonNegativeSeconds::try_from(exp_t).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
    }

    let expected_travel_times = vec![2., 2., 2., 2., 2., 2.];
    for (agent_res, &exp_t) in agent_results.iter().zip(expected_travel_times.iter()) {
        let t = agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .road_time;
        assert_eq!(
            t,
            NonNegativeSeconds::try_from(exp_t).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
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
        assert_eq!(
            t,
            NonNegativeSeconds::try_from(exp_t).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
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
        (
            AnySeconds::try_from(0.).unwrap(),
            AnySeconds::try_from(50.).unwrap()
        ),
        "The period of the TTF should be equal to the period of the simulation"
    );
}
