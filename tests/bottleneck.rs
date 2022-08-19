use metropolis::agent::Agent;
use metropolis::learning::LearningModel;
use metropolis::mode::road::{DepartureTimeModel, RoadMode};
use metropolis::mode::Mode;
use metropolis::network::road_network::vehicle::{vehicle_index, SpeedFunction, Vehicle};
use metropolis::network::road_network::{RoadEdge, RoadNetwork, SpeedDensityFunction};
use metropolis::network::{Network, NetworkParameters};
use metropolis::parameters::Parameters;
use metropolis::schedule_utility::ScheduleUtility;
use metropolis::simulation::Simulation;
use metropolis::stop::StopCriterion;
use metropolis::travel_utility::TravelUtility;
use metropolis::units::{Interval, Length, Outflow, Speed, Time, PCE};
use petgraph::graph::{node_index, DiGraph};

fn get_simulation() -> Simulation<f64> {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 3., 4., 5., 10.];
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

    // Create a 1-road network that has a bottleneck with a capacity of 1 vehicle each 2 seconds.
    let graph = DiGraph::from_edges(&[(
        0,
        1,
        RoadEdge::new(
            Speed(10.0),
            Length(0.0),
            1,
            SpeedDensityFunction::FreeFlow,
            Outflow(0.5),
        ),
    )]);
    let vehicle = Vehicle::new(Length(1.0), PCE(1.0), SpeedFunction::Base);
    let road_network = RoadNetwork::new(graph, vec![vehicle]);
    let network = Network::new(Some(road_network));

    let parameters = Parameters::new(
        Interval([Time(0.0), Time(100.0)]),
        NetworkParameters::default(),
        LearningModel::default(),
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
    let skims = simulation
        .get_network()
        .compute_skims(
            &weights,
            &preprocess_data.network,
            &simulation.get_parameters().network,
        )
        .unwrap();
    let results = simulation.run_iteration(&weights, skims, None, 1).unwrap();
    let agent_results = results.agent_results();

    let expected_arrival_times = vec![0., 3., 5., 7., 10.];
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
}
