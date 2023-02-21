// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashSet;
use metropolis::agent::Agent;
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
use num_traits::Float;
use petgraph::graph::{edge_index, node_index, DiGraph};

fn get_simulation() -> Simulation<f64> {
    // Create a network with 4 nodes and two different routes to go from node 0 to node 3.
    // One route (0 -> 1 -> 3) is always faster than the other (0 -> 2 -> 3).
    // Edge 0: 0 -> 1 (tt = 1).
    // Edge 1: 0 -> 2 (tt = 2).
    // Edge 2: 1 -> 3 (tt = 1).
    // Edge 3: 2 -> 3 (tt = 1).
    let graph = DiGraph::from_edges(&[
        (
            0,
            1,
            RoadEdge::new(
                Speed(1.0),
                Length(1.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Flow::infinity(),
                Time(0.),
            ),
        ),
        (
            0,
            2,
            RoadEdge::new(
                Speed(1.0),
                Length(2.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Flow::infinity(),
                Time(0.),
            ),
        ),
        (
            1,
            3,
            RoadEdge::new(
                Speed(1.0),
                Length(1.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Flow::infinity(),
                Time(0.),
            ),
        ),
        (
            2,
            3,
            RoadEdge::new(
                Speed(1.0),
                Length(1.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Flow::infinity(),
                Time(0.),
            ),
        ),
    ]);
    // Create 4 identical vehicles types with different road restrictions.
    // Only vehicle type `v0` has acces to edge 2 (and thus to route 0 -> 1 -> 3).
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
        SpeedFunction::Base,
        [0, 1, 3].into_iter().map(|i| edge_index(i)).collect(),
        HashSet::new(),
    );
    let v2 = Vehicle::new(
        Length(1.0),
        PCE(1.0),
        SpeedFunction::Base,
        HashSet::new(),
        [2].into_iter().map(|i| edge_index(i)).collect(),
    );
    // For vehicle type `v3`, only route 0 -> 2 -> 3 is feasible according to allowed edges but
    // only route 0 -> 1 -> 3 is feasible according to restricted edges.
    // As allowed edges take precedence over restricted edges, in practice, only the route 0 -> 2
    // -> 3 is feasible.
    let v3 = Vehicle::new(
        Length(1.0),
        PCE(1.0),
        SpeedFunction::Base,
        [0, 1, 3].into_iter().map(|i| edge_index(i)).collect(),
        [1].into_iter().map(|i| edge_index(i)).collect(),
    );
    let road_network = RoadNetwork::new(graph, vec![v0, v1, v2, v3]);
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
        let v = if i == 4 {
            vehicle_index(0)
        } else {
            vehicle_index(i)
        };
        let leg = Leg::new(
            LegType::Road(RoadLeg::new(node_index(0), node_index(3), v)),
            Time::default(),
            TravelUtility::default(),
            ScheduleUtility::None,
        );
        let trip = TravelingMode::new(
            vec![leg],
            Time::default(),
            DepartureTimeModel::Constant(Time(0.)),
            TravelUtility::default(),
            ScheduleUtility::None,
            ScheduleUtility::None,
        );
        let agent = Agent::new(i, vec![Mode::Trip(trip)], None);
        agents.push(agent);
    }

    let network_parameters = NetworkParameters {
        road_network: Some(RoadNetworkParameters::from_recording_interval(Time(5.0))),
    };
    let parameters = Parameters {
        period: Interval([Time(0.0), Time(50.0)]),
        network: network_parameters,
        stopping_criteria: vec![StopCriterion::MaxIteration(1)],
        ..Default::default()
    };

    Simulation::new(agents, network, parameters)
}

#[test]
fn restricted_road_test() {
    let simulation = get_simulation();
    let preprocess_data = simulation.preprocess().unwrap();
    let weights = simulation
        .get_network()
        .get_free_flow_weights(&preprocess_data.network);
    let results = simulation
        .run_iteration(&weights, None, 1, &preprocess_data)
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
            Time(exp_ta),
            "Agent {} took the incorrect route.\nAgent result: {:?}",
            i,
            agent_res
        );
    }
}
