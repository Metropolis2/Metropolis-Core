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

//! Integration test for running the within-day model several times on the same pre-day results.
use metropolis_core::hash::HashSet;
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
        let agent = Agent::new(i as i64, vec![Mode::Trip(trip)], None);
        agents.push(agent);
    }

    // Create a road network with 2 edges, with capacities 1 vehicle each 2 seconds and 1 vehicle
    // each 4 seconds, respectively.
    // Travel time is 1 second free-flow.
    let edges = vec![
        (
            MetroId::Integer(0),
            MetroId::Integer(1),
            RoadEdge::new(
                0,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(1.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                Some(FlowPerLane::try_from(0.5).unwrap()),
                NonNegativeSeconds::ZERO,
                false,
            ),
        ),
        (
            MetroId::Integer(1),
            MetroId::Integer(2),
            RoadEdge::new(
                1,
                MetersPerSecond::try_from(1.0).unwrap(),
                NonNegativeMeters::try_from(1.0).unwrap(),
                Lanes::try_from(1.0).unwrap(),
                SpeedDensityFunction::FreeFlow,
                Some(FlowPerLane::try_from(0.25).unwrap()),
                NonNegativeSeconds::ZERO,
                false,
            ),
        ),
    ];
    let vehicle = Vehicle::new(
        1,
        NonNegativeMeters::try_from(1.0).unwrap(),
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
fn rerun_within_day_test() {
    init_simulation();
    let preprocess_data = metropolis_core::simulation::preprocess().unwrap();
    let rn_weights = metropolis_core::network::road_network::free_flow_weights(
        preprocess_data.network.get_road_network().unwrap(),
    );
    let weights = NetworkWeights::new(Some(rn_weights));
    let skims = metropolis_core::network::compute_skims(
        &weights,
        &preprocess_data.network,
        &mut Default::default(),
    )
    .unwrap();
    let pre_day_results =
        metropolis_core::simulation::run_pre_day_model(&weights, &skims, &preprocess_data, None, 1)
            .unwrap();
    // The routes are computed in the pre-day model (so the within-day model does not compute them
    // from the skims).
    for agent_res in pre_day_results.iter() {
        assert!(agent_res.mode_results().as_trip().unwrap().legs[0]
            .class
            .as_road()
            .unwrap()
            .expected_route
            .is_some());
    }

    // Run the within-day model twice, each time on a clone of the pre-day results.
    let mut runs = Vec::with_capacity(2);
    for _ in 0..2 {
        let mut agent_results = pre_day_results.clone();
        metropolis_core::simulation::run_within_day_model(
            &mut agent_results,
            &skims,
            &preprocess_data,
            metropolis_core::network::blank_state(),
        )
        .unwrap();
        runs.push(agent_results);
    }

    // Same arrival times as in the bottleneck test.
    let expected_arrival_times = [2., 6., 10., 14., 18., 23.];
    for agent_results in runs.iter() {
        for (agent_res, &exp_ta) in agent_results.iter().zip(expected_arrival_times.iter()) {
            let ta = agent_res.mode_results().as_trip().unwrap().arrival_time();
            assert_eq!(
                ta,
                NonNegativeSeconds::try_from(exp_ta).unwrap(),
                "Agent result: {:?}",
                agent_res
            );
        }
    }
    assert_eq!(*runs[0], *runs[1]);
}
