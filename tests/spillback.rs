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
use num_traits::Float;
use petgraph::graph::{node_index, DiGraph};

/// Network is two successive roads:
/// O -> I -> D
/// where O is the origin of all the trips and D is the destination.
///
/// For both road, the length is 20 meters and the free-flow speed is 2 m/s, i.e., the free-flow
/// travel time is 10 seconds.
/// The speed-density function is FreeFlow.
///
/// The road O->I has an exit bottleneck with capacity 1 vehicle / second.
/// The road I->D has an entry bottleneck with capacity 0.5 vehicle / second.
///
/// Vehicles have a length of 8 meters.
fn get_network() -> Network<f64> {
    let graph = DiGraph::from_edges(&[
        (
            0,
            1,
            RoadEdge::new(
                Speed(2.0),
                Length(20.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow::infinity(),
                Flow(1.0),
                true,
            ),
        ),
        (
            1,
            2,
            RoadEdge::new(
                Speed(2.0),
                Length(20.0),
                1,
                SpeedDensityFunction::FreeFlow,
                Flow(0.5),
                Flow::infinity(),
                true,
            ),
        ),
    ]);
    let vehicle = Vehicle::new(Length(8.0), PCE(1.0), SpeedFunction::Base);
    let road_network = RoadNetwork::new(graph, vec![vehicle]);
    Network::new(Some(road_network))
}

fn get_simulation() -> Simulation<f64> {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 1., 2., 3., 4.];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, dt) in departure_times.into_iter().enumerate() {
        let road = RoadMode::new(
            node_index(0),
            node_index(2),
            vehicle_index(0),
            DepartureTimeModel::Constant(Time(dt)),
            TravelUtility::None,
        );
        let agent = Agent::new(i, vec![Mode::Road(road)], None, ScheduleUtility::None);
        agents.push(agent);
    }

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

    Simulation::new(agents, get_network(), parameters)
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

    // Departure times: 0, 1, 2, 3, 4.
    // Entry time on first road: 0, 1, 2, 3, 20.
    // Entry time at first bottleneck: 10, 11, 12, 13, 30.
    // Exit time from first road: 10, 11, 20, 22, 30.
    // Exit time from second road's bottleneck: 10, 12, 20, 22, 30.
    // Arrival times: 20, 22, 30, 32, 40.

    let expected_departure_times = vec![0., 1., 2., 3., 20.];
    let expected_arrival_times = vec![20., 22., 30., 32., 40.];
    for (agent_res, (&exp_td, &exp_ta)) in agent_results.iter().zip(
        expected_departure_times
            .iter()
            .zip(expected_arrival_times.iter()),
    ) {
        let td = agent_res.departure_time().unwrap();
        let ta = agent_res.arrival_time().unwrap();
        assert_eq!(
            td,
            Time(exp_td),
            "Expected departure time: {:?}\nAgent result: {:?}",
            exp_td,
            agent_res
        );
        assert_eq!(
            ta,
            Time(exp_ta),
            "Expected arrival time: {:?}\nAgent result: {:?}",
            exp_ta,
            agent_res
        );
    }
}
