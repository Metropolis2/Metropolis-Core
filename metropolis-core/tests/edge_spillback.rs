// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Integration test for disabling spillback on a single edge.
use metropolis_core::hash::HashSet;
use metropolis_core::mode::trip::event::SpillbackStatus;
use metropolis_core::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis_core::mode::Mode;
use metropolis_core::network::road_network::parameters::RoadNetworkParameters;
use metropolis_core::network::road_network::vehicle::{SpeedFunction, Vehicle};
use metropolis_core::network::road_network::{RoadEdge, RoadNetwork, SpeedDensityFunction};
use metropolis_core::network::{Network, NetworkWeights};
use metropolis_core::parameters::Parameters;
use metropolis_core::population::{agent_index, Agent};
use metropolis_core::schedule_utility::ScheduleUtility;
use metropolis_core::travel_utility::TravelUtility;
use metropolis_core::units::*;
use num_traits::{ConstOne, ConstZero};

fn edge(id: i64) -> RoadEdge {
    RoadEdge::new(
        id,
        MetersPerSecond::try_from(1.0).unwrap(),
        NonNegativeMeters::try_from(10.0).unwrap(),
        Lanes::try_from(1.0).unwrap(),
        SpeedDensityFunction::FreeFlow,
        None,
        NonNegativeSeconds::ZERO,
        true,
    )
}

/// Same scenario as in the `spillback` test, but spillback is disabled on edge 1.
fn init_simulation() {
    // Create agents with fixed departure times.
    let departure_times = vec![0., 7., 5., 6., 9., 30.];
    let origins = vec![0, 1, 0, 0, 0, 0];
    let mut agents = Vec::with_capacity(departure_times.len());
    for (i, (dt, o)) in departure_times.into_iter().zip(origins).enumerate() {
        let leg = Leg::new(
            1,
            LegType::Road(RoadLeg::new(o, 2, 1)),
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
        let agent = Agent::new(i as i64, vec![Mode::Trip(trip)], None);
        agents.push(agent);
    }

    // Create a road network with 2 edges, with infinite capacities, free-flow travel time of 10
    // seconds and length of 10 meters. Spillback is disabled on edge 1.
    let edges = vec![
        (MetroId::Integer(0), MetroId::Integer(1), edge(0)),
        (
            MetroId::Integer(1),
            MetroId::Integer(2),
            edge(1).with_spillback(false),
        ),
    ];
    // Vehicles are 6 meters long: 2 vehicles are enough to block an edge.
    let vehicle = Vehicle::new(
        1,
        NonNegativeMeters::try_from(6.0).unwrap(),
        PCE::ONE,
        SpeedFunction::Base,
        HashSet::default(),
        HashSet::default(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![vehicle]);
    let network = Network::new(Some(road_network));

    let parameters = Parameters {
        period: Interval::try_from([0.0, 50.0]).unwrap(),
        road_network: Some(RoadNetworkParameters {
            spillback: true,
            max_pending_duration: NonNegativeSeconds::try_from(f64::MAX).unwrap(),
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
fn edge_spillback_test() {
    init_simulation();
    let preprocess_data = metropolis_core::simulation::preprocess().unwrap();
    let rn_weights = metropolis_core::network::road_network::free_flow_weights(
        preprocess_data.network.get_road_network().unwrap(),
    );
    let weights = NetworkWeights::new(Some(rn_weights));
    let results = metropolis_core::simulation::run_iteration(
        weights,
        None,
        None,
        1,
        &preprocess_data,
        &mut Default::default(),
    )
    .unwrap();
    let agent_results = results.iteration_results.agent_results();

    // Departure times: 0, 7, 5, 6, 9, 30.
    // Origins: 0, 1, 0, 0, 0, 0.
    // Edge 0 is full from 5 (agents 0 and 2) to 10 (agent 0 exits), then from 10 (agents 2 and 3)
    // to 15 (agent 2 exits), then from 15 (agents 3 and 4) to 20.
    // Edge 0 entry times: 0, NA, 5, 10, 15, 30.
    // Edge 1 never gets full: vehicles enter it as soon as they exit edge 0.
    // Edge 1 entry times: 10, 7, 15, 20, 25, 40.
    // Arrival times: 20, 17, 25, 30, 35, 50.
    let expected_arrival_times = [20., 17., 25., 30., 35., 50.];
    for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
        let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
        assert_eq!(
            ta,
            NonNegativeSeconds::try_from(exp_ta).unwrap(),
            "Agent result: {:?}",
            agent_res
        );
    }

    // Only agents 3 and 4 face spillback, when entering edge 0.
    for index in 0..6 {
        for event in agent_results[agent_index(index)]
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[0]
            .class
            .as_road()
            .unwrap()
            .route
            .iter()
        {
            let expected = if (index == 3 || index == 4) && event.edge == MetroId::Integer(0) {
                SpillbackStatus::Spillback
            } else {
                SpillbackStatus::NoSpillback
            };
            assert_eq!(
                event.spillback_status, expected,
                "Wrong spillback status for agent {} on edge {}",
                index, event.edge
            );
        }
    }
}
