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

//! Integration test for the road-capacity calibration: the target delays are simulated with known
//! capacities, which the calibration must recover.
use metropolis_core::calibration::parameters::CapacityCalibrationParameters;
use metropolis_core::calibration::TargetRoute;
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

/// True capacity of the categories `A` and `B`, in PCE per second per lane.
const TRUE_CAPACITIES: [f64; 2] = [0.5, 0.15];

/// Initializes a corridor 0 -> 1 -> 2, whose edges have the categories `A` and `B` (with their true
/// capacities as input bottleneck flows), and 40 agents departing from 0 every second, alternately
/// to 1 and to 2.
///
/// The agents going to 1 only cross `A`, so they identify its capacity. The agents going to 2 also
/// cross `B`, where they arrive at the outflow of `A` (in a series of bottlenecks, the total delay
/// only depends on the smallest capacity).
fn init_simulation() {
    let mut agents = Vec::new();
    for i in 0..40 {
        let destination = 1 + i % 2;
        let leg = Leg::new(
            1,
            LegType::Road(RoadLeg::new(0, destination, 1)),
            NonNegativeSeconds::ZERO,
            TravelUtility::default(),
            ScheduleUtility::None,
        );
        let trip = TravelingMode::new(
            1,
            vec![leg],
            NonNegativeSeconds::ZERO,
            DepartureTimeModel::Constant(NonNegativeSeconds::try_from(i as f64).unwrap()),
            TravelUtility::default(),
            ScheduleUtility::None,
            ScheduleUtility::None,
        );
        agents.push(Agent::new(i, vec![Mode::Trip(trip)], None));
    }

    // Free-flow travel time of 1 second on each edge.
    let edge = |id: i64, category: &str, capacity: f64| {
        RoadEdge::new(
            id,
            MetersPerSecond::try_from(1.0).unwrap(),
            NonNegativeMeters::try_from(1.0).unwrap(),
            Lanes::try_from(1.0).unwrap(),
            SpeedDensityFunction::FreeFlow,
            Some(FlowPerLane::try_from(capacity).unwrap()),
            NonNegativeSeconds::ZERO,
            true,
        )
        .with_category(MetroId::from(category))
    };
    let edges = vec![
        (
            MetroId::Integer(0),
            MetroId::Integer(1),
            edge(0, "A", TRUE_CAPACITIES[0]),
        ),
        (
            MetroId::Integer(1),
            MetroId::Integer(2),
            edge(1, "B", TRUE_CAPACITIES[1]),
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
        period: Interval::try_from([0.0, 500.0]).unwrap(),
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

/// Simulates a day with the input bottleneck flows (the true capacities) and returns the trip of
/// each agent as a target route, with its simulated queueing delay.
fn simulated_target_routes() -> Vec<TargetRoute> {
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
    let mut agent_results =
        metropolis_core::simulation::run_pre_day_model(&weights, &skims, &preprocess_data, None, 1)
            .unwrap();
    metropolis_core::simulation::run_within_day_model(
        &mut agent_results,
        &skims,
        &preprocess_data,
        metropolis_core::network::blank_state(),
        true,
    )
    .unwrap();
    agent_results
        .iter()
        .enumerate()
        .map(|(i, agent_res)| {
            let leg = &agent_res.mode_results().as_trip().unwrap().legs[0];
            let road_leg = leg.class.as_road().unwrap();
            let delay = road_leg.in_bottleneck_time + road_leg.out_bottleneck_time;
            TargetRoute::from_values(
                MetroId::Integer(i as i64),
                Some(f64::from(leg.departure_time)),
                Some(f64::from(delay)),
                Some(road_leg.route.iter().map(|e| e.edge).collect()),
            )
            .unwrap()
        })
        .collect()
}

/// Runs the calibration from the given initial capacities of `A` and `B` and returns the
/// calibrated capacities.
fn calibrate(initial_capacities: [f64; 2], target_routes: &[TargetRoute]) -> Vec<f64> {
    let params: CapacityCalibrationParameters = serde_json::from_str(&format!(
        r#"{{"capacities": {{"A": {}, "B": {}}},
        "route_choice": {{"max_iterations": 1}},
        "inner_loop": {{"tolerance": 1e-4, "max_iterations": 20}},
        "outer_loop": {{"patience": 1}}}}"#,
        initial_capacities[0], initial_capacities[1],
    ))
    .unwrap();
    let mut capacities = metropolis_core::calibration::calibrate(&params, target_routes.to_vec())
        .unwrap()
        .capacities;
    capacities.sort_by_key(|(id, _)| id.unwrap().to_string());
    capacities.into_iter().map(|(_, c)| f64::from(c)).collect()
}

#[test]
fn calibration_test() {
    init_simulation();
    let target_routes = simulated_target_routes();
    // The agents queue at `A` and those going to 2 also queue at `B` (the largest delay at `A` is
    // 39 s, for the last agent).
    let max_delay = |path_len: usize| {
        target_routes
            .iter()
            .filter(|r| r.path.len() == path_len)
            .map(|r| f64::from(r.target_delay))
            .fold(0., f64::max)
    };
    assert_eq!(max_delay(1), 38.);
    assert!(max_delay(2) > 60., "{}", max_delay(2));

    // From the true capacities, the surrogate model reproduces the simulated delays exactly, so the
    // capacities do not change.
    let capacities = calibrate(TRUE_CAPACITIES, &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-6, "{capacities:?}");
    }

    // From a wrong guess, the true capacities are recovered.
    let capacities = calibrate([0.4, 0.18], &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-3, "{capacities:?}");
    }
}
