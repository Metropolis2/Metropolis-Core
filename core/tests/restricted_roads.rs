// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Integration test for road restrictions.
use hashbrown::HashSet;
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
use metropolis_core::units::*;
use num_traits::{ConstOne, ConstZero};

fn init_simulation() {
    // Create a network with 4 nodes and two different routes to go from node 0 to node 3.
    // One route (0 -> 1 -> 3) is always faster than the other (0 -> 2 -> 3).
    // Edge 0: 0 -> 1 (tt = 1).
    // Edge 1: 0 -> 2 (tt = 2).
    // Edge 2: 1 -> 3 (tt = 1).
    // Edge 3: 2 -> 3 (tt = 1).
    let id0 = MetroId::Integer(0);
    let id1 = MetroId::Integer(1);
    let id2 = MetroId::Integer(2);
    let id3 = MetroId::Integer(3);
    let edges = vec![
        (
            id0,
            id1,
            RoadEdge::new(
                0,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(1.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                None,
                NonNegativeSeconds::ZERO,
                true,
            ),
        ),
        (
            id0,
            id2,
            RoadEdge::new(
                1,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(2.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                None,
                NonNegativeSeconds::ZERO,
                true,
            ),
        ),
        (
            id1,
            id3,
            RoadEdge::new(
                2,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(1.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                None,
                NonNegativeSeconds::ZERO,
                true,
            ),
        ),
        (
            id2,
            id3,
            RoadEdge::new(
                3,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(1.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                None,
                NonNegativeSeconds::ZERO,
                true,
            ),
        ),
    ];
    // Create 4 identical vehicles types with different road restrictions.
    // Only vehicle type `v0` has acces to edge 2 (and thus to route 0 -> 1 -> 3).
    let v0 = Vehicle::new(
        1,
        NonNegativeMeters::try_from(1.0).unwrap(),
        PCE::ONE,
        SpeedFunction::Base,
        HashSet::new(),
        HashSet::new(),
    );
    let v1 = Vehicle::new(
        2,
        NonNegativeMeters::try_from(1.0).unwrap(),
        PCE::ONE,
        SpeedFunction::Base,
        [id0, id1, id3].into_iter().collect(),
        HashSet::new(),
    );
    let v2 = Vehicle::new(
        3,
        NonNegativeMeters::try_from(1.0).unwrap(),
        PCE::ONE,
        SpeedFunction::Base,
        HashSet::new(),
        [id2].into_iter().collect(),
    );
    // For vehicle type `v3`, only route 0 -> 2 -> 3 is feasible according to allowed edges but
    // only route 0 -> 1 -> 3 is feasible according to restricted edges.
    // As allowed edges take precedence over restricted edges, in practice, only the route 0 -> 2
    // -> 3 is feasible.
    let v3 = Vehicle::new(
        4,
        NonNegativeMeters::try_from(1.0).unwrap(),
        PCE::ONE,
        SpeedFunction::Base,
        [id0, id1, id3].into_iter().collect(),
        [id1].into_iter().collect(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![v0, v1, v2, v3]);
    let network = Network::new(Some(road_network));

    // Create agents with different vehicle types.
    // Agent 0: v0.
    // Agent 1: v1.
    // Agent 2: v2.
    // Agent 3: v3.
    // Agent 4: v4.
    // Agent 5: v0.
    let mut agents = Vec::with_capacity(5);
    for i in 0..5 {
        // Agent id: vehicle id.
        // 0: 1,
        // 1: 2,
        // 2: 3,
        // 3: 4,
        // 4: 1.
        let v = if i == 4 { 1 } else { i + 1 };
        let leg = Leg::new(
            1,
            LegType::Road(RoadLeg::new(0, 3, v)),
            NonNegativeSeconds::ZERO,
            TravelUtility::default(),
            ScheduleUtility::None,
        );
        let trip = TravelingMode::new(
            1,
            vec![leg],
            NonNegativeSeconds::ZERO,
            DepartureTimeModel::Constant(NonNegativeSeconds::ZERO),
            TravelUtility::default(),
            ScheduleUtility::None,
            ScheduleUtility::None,
        );
        let agent = Agent::new(i, vec![Mode::Trip(trip)], None);
        agents.push(agent);
    }

    let parameters = Parameters {
        period: Interval::try_from([0.0, 50.0]).unwrap(),
        road_network: Some(RoadNetworkParameters {
            spillback: false,
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
fn restricted_road_test() {
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

    // An arrival time of 2. means that the route 0 -> 1 -> 3 was taken (only possible for agent
    // 0).
    // An arrival time of 3. means that the route 0 -> 2 -> 3 was taken.
    let expected_arrival_times = vec![2., 3., 3., 3., 2.];
    for (i, (agent_res, &exp_ta)) in agent_results
        .iter()
        .zip(expected_arrival_times.iter())
        .enumerate()
    {
        let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
        assert_eq!(
            ta,
            NonNegativeSeconds::try_from(exp_ta).unwrap(),
            "Agent {} took the incorrect route.\nAgent result: {:?}",
            i,
            agent_res
        );
    }
}
