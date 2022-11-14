use metropolis::agent::Agent;
use metropolis::learning::{ExponentialLearningModel, LearningModel};
use metropolis::mode::road::{DepartureTimeModel, RoadMode};
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
use ttf::{TTFNum, TTF};

fn get_simulation() -> Simulation<f64> {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 3., 4., 5., 10., 21.];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, dt) in departure_times.into_iter().enumerate() {
        let road = RoadMode::new(
            node_index(0),
            node_index(1),
            vehicle_index(0),
            DepartureTimeModel::Constant(Time(dt)),
            TravelUtility::None,
        );
        let agent = Agent::new(i, vec![Mode::Road(road)], None, ScheduleUtility::None);
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
        ),
    )]);
    let vehicle = Vehicle::new(Length(1.0), PCE(1.0), SpeedFunction::Base);
    let road_network = RoadNetwork::new(graph, vec![vehicle]);
    let network = Network::new(Some(road_network));

    let network_parameters = NetworkParameters {
        road_network: Some(RoadNetworkParameters::from_recording_interval(Time(5.0))),
    };
    let parameters = Parameters::new(
        Interval([Time(0.0), Time(50.0)]),
        network_parameters,
        LearningModel::Exponential(ExponentialLearningModel::new(0.0)),
        vec![StopCriterion::MaxIteration(1)],
        1.0,
        None,
    );

    Simulation::new(agents, network, parameters)
}

#[test]
fn bottleneck_test() {
    let simulation = get_simulation();
    let weights = simulation.get_network().get_free_flow_weights();
    let preprocess_data = simulation.preprocess();
    let results = simulation
        .run_iteration(&weights, None, 1, &preprocess_data)
        .unwrap();
    let agent_results = results.iteration_results.agent_results();

    // Departure times: 0, 3, 4, 5, 10, 21.
    // In-bottleneck exit times: 0, 3, 5, 7, 10, 21.
    // Travel time on the road segment is always 1 second.
    // Out-bottleneck entry times: 1, 4, 6, 8, 11, 22.
    // Arrival times: 1, 5, 9, 13, 17, 22.

    // Exit time from the in-bottleneck given the entry time:
    // Entry time t in (0, 2], exit time 2.
    // Entry time t in (2, 3], exit time t.
    // Entry time t in (3, 4], exit time 5.
    // Entry time t in (4, 5], exit time 7.
    // Entry time t in (5, 9], exit time 9.
    // Entry time t in (9, 10], exit time t.
    // Entry time t in (10, 12], exit time 12.
    // Entry time t in (12, 21], exit time t.
    // Entry time t in (21, 23], exit time 23.
    // Entry time t in (23, 50), exit time t.

    // Average waiting time:
    // For t in (0, 5] : 1.2.
    // For t in (5, 10] : 1.6.
    // For t in (10, 15] : 0.4.
    // For t in (15, 20] : 0.
    // For t in (20, 25] : 0.4.
    // For t in (25, 50) : 0.

    // Exit time from the in-bottleneck given the entry time:
    // Entry time t in (0, 1], exit time t.
    // Entry time t in (1, 4], exit time 5.
    // Entry time t in (4, 6], exit time 9.
    // Entry time t in (6, 8], exit time 13.
    // Entry time t in (8, 11], exit time 17.
    // Entry time t in (11, 21], exit time 21.
    // Entry time t in (21, 22], exit time t.
    // Entry time t in (22, 26], exit time 26.
    // Entry time t in (26, 50], exit time t.

    // Average waiting time:
    // For t in (0, 5] : 2.4.
    // For t in (5, 10] : 6.3.
    // For t in (10, 15] : 7.7.
    // For t in (15, 20] : 3.5.
    // For t in (20, 25] : 1.6.
    // For t in (25, 30] : 0.1.
    // For t in (30, 50) : 0.

    let expected_arrival_times = vec![1., 5., 9., 13., 17., 22.];
    for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
        let ta = agent_res.arrival_time().unwrap();
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
    let edge_weight = &weights[(vehicle_index(0), edge_index(0))];
    let TTF::Piecewise(ttf) = edge_weight else {
        panic!("TTF should be piecewise");
    };
    assert_eq!(
        ttf.period(),
        &[Time(0.), Time(50.)],
        "The period of the TTF should be equal to the period of the simulation"
    );
    // With departure time 0.0, the waiting time for the in-bottleneck is 0.0.
    // With departure time 1.0, the waiting time for the out-bottleneck is (linear interpolation):
    // alpha * 0.0 + (1 - alpha) * 2.4, where alpha = (2.5 - 1.0) / 2.5 = 0.6.
    // It is equal to 0.96.
    let actual = ttf.eval(Time(0.));
    let expected = Time(0. + 1. + 0.96);
    assert!(
        actual.approx_eq(&expected),
        "Invalid expected travel time when leaving at time 0.0: {actual:?} != {expected:?}"
    );
    // With departure time 2.5, the waiting time for the in-bottleneck is 1.2.
    // With departure time 2.5 + 1.2 + 1.0 = 4.7, the waiting time for the out-bottleneck is
    // (linear interpolation): alpha * 2.4 + (1 - alpha) * 6.3, where
    // alpha = (7.5 - 4.7) / 5 = 0.56.
    // It is equal to 4.116.
    let actual = ttf.eval(Time(2.5));
    let expected = Time(1.2 + 1.0 + 4.116);
    assert!(
        actual.approx_eq(&expected),
        "Invalid expected travel time when leaving at time 2.5: {actual:?} != {expected:?}"
    );
    // With departure time 10, the waiting time for the in-bottleneck is 1 (interpolation between
    // 7.5 and 12.5).
    // With departure time 10 + 1 + 1 = 12, the waiting time for the out-bottleneck is
    // (linear interpolation): alpha * 6.3 + (1 - alpha) * 7.7,
    // where alpha = (12.5 - 12) / 5 = 0.1.
    // It is equal to 7.56.
    let actual = ttf.eval(Time(10.));
    let expected = Time(1.0 + 1.0 + 7.56);
    assert!(
        actual.approx_eq(&expected),
        "Invalid expected travel time when leaving at time 10.0: {actual:?} != {expected:?}"
    );
}
