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

//! Integration test for trip chaining.
use hashbrown::HashSet;
use metropolis_core::mode::trip::event::RoadEvent;
use metropolis_core::mode::trip::results::{
    LegResults, LegTypeResults, RoadLegResults, TripResults,
};
use metropolis_core::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use metropolis_core::mode::{mode_index, Mode, ModeResults};
use metropolis_core::network::road_network::parameters::RoadNetworkParameters;
use metropolis_core::network::road_network::vehicle::{SpeedFunction, Vehicle};
use metropolis_core::network::road_network::{RoadEdge, RoadNetwork, SpeedDensityFunction};
use metropolis_core::network::{Network, NetworkWeights};
use metropolis_core::parameters::Parameters;
use metropolis_core::population::{agent_index, Agent};
use metropolis_core::schedule_utility::alpha_beta_gamma::LinearPenaltiesModel;
use metropolis_core::schedule_utility::ScheduleUtility;
use metropolis_core::simulation::results::AgentResult;
use metropolis_core::travel_utility::{PolynomialFunction, TravelUtility};
use metropolis_core::units::*;
use num_traits::{ConstOne, ConstZero};
use ttf::{PwlTTF, TTF};

fn init_simulation() {
    // Create a network with 4 nodes and 2 edges.
    // Edge 0: 0 -> 1 (free-flow tt: 1).
    // Edge 1: 2 -> 3 (free-flow tt: 2).
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
                None,
                NonNegativeSeconds::ZERO,
                true,
            ),
        ),
        (
            MetroId::Integer(2),
            MetroId::Integer(3),
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
    ];
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
        SpeedFunction::Multiplicator(PositiveNum::try_from(0.5).unwrap()),
        HashSet::new(),
        HashSet::new(),
    );
    let road_network = RoadNetwork::from_edges(edges, vec![v0, v1]);
    let network = Network::new(Some(road_network));

    // Create an agent with 4 legs (3 road and 1 virtual).
    let mut agents = Vec::with_capacity(1);
    let leg0 = Leg::new(
        1,
        LegType::Road(RoadLeg::new(0, 1, 1)),
        NonNegativeSeconds::try_from(2.0).unwrap(),
        TravelUtility::Polynomial(PolynomialFunction {
            a: Utility::try_from(1.0).unwrap(),
            b: ValueOfTime::try_from(-1.0).unwrap(),
            c: ValueOfTime::try_from(1.0).unwrap(),
            ..Default::default()
        }),
        ScheduleUtility::LinearPenalties(
            LinearPenaltiesModel::new(
                NonNegativeSeconds::try_from(5.0).unwrap(),
                NonNegativeSeconds::try_from(6.0).unwrap(),
                ValueOfTime::try_from(0.5).unwrap(),
                ValueOfTime::try_from(2.0).unwrap(),
            )
            .unwrap(),
        ),
    );
    let leg1 = Leg::new(
        2,
        LegType::Virtual(TTF::Piecewise(PwlTTF::from_values(
            vec![
                AnySeconds::try_from(0.).unwrap(),
                AnySeconds::try_from(10.).unwrap(),
                AnySeconds::try_from(5.).unwrap(),
            ],
            AnySeconds::try_from(0.).unwrap(),
            AnySeconds::try_from(10.).unwrap(),
        ))),
        NonNegativeSeconds::try_from(1.0).unwrap(),
        TravelUtility::Polynomial(PolynomialFunction {
            b: ValueOfTime::try_from(-1.0).unwrap(),
            ..Default::default()
        }),
        ScheduleUtility::LinearPenalties(
            LinearPenaltiesModel::new(
                NonNegativeSeconds::try_from(10.0).unwrap(),
                NonNegativeSeconds::try_from(10.0).unwrap(),
                ValueOfTime::try_from(0.1).unwrap(),
                ValueOfTime::try_from(0.2).unwrap(),
            )
            .unwrap(),
        ),
    );
    let leg2 = Leg::new(
        3,
        LegType::Road(RoadLeg::new(2, 3, 2)),
        NonNegativeSeconds::try_from(1.0).unwrap(),
        TravelUtility::Polynomial(PolynomialFunction {
            a: Utility::try_from(5.0).unwrap(),
            ..Default::default()
        }),
        ScheduleUtility::None,
    );
    // 4th leg is a road leg with origin = destination (to test if this case works).
    let leg3 = Leg::new(
        4,
        LegType::Road(RoadLeg::new(2, 2, 2)),
        NonNegativeSeconds::try_from(0.0).unwrap(),
        TravelUtility::default(),
        ScheduleUtility::None,
    );
    let trip = TravelingMode::new(
        1,
        vec![leg0, leg1, leg2, leg3],
        NonNegativeSeconds::try_from(3.0).unwrap(),
        DepartureTimeModel::Constant(NonNegativeSeconds::ZERO),
        TravelUtility::Polynomial(PolynomialFunction {
            c: ValueOfTime::try_from(-2.0).unwrap(),
            ..Default::default()
        }),
        ScheduleUtility::LinearPenalties(
            LinearPenaltiesModel::new(
                NonNegativeSeconds::try_from(1.0).unwrap(),
                NonNegativeSeconds::try_from(1.0).unwrap(),
                ValueOfTime::try_from(2.0).unwrap(),
                ValueOfTime::try_from(2.0).unwrap(),
            )
            .unwrap(),
        ),
        ScheduleUtility::LinearPenalties(
            LinearPenaltiesModel::new(
                NonNegativeSeconds::try_from(15.0).unwrap(),
                NonNegativeSeconds::try_from(15.0).unwrap(),
                ValueOfTime::try_from(2.0).unwrap(),
                ValueOfTime::try_from(2.0).unwrap(),
            )
            .unwrap(),
        ),
    );
    let agent = Agent::new(0, vec![Mode::Trip(trip)], None);
    agents.push(agent);

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
fn legs_test() {
    init_simulation();
    let preprocess_data = metropolis_core::simulation::preprocess().unwrap();
    let rn_weights = metropolis_core::network::road_network::free_flow_weights(
        &preprocess_data.network.get_road_network().unwrap(),
    );
    let weights = NetworkWeights::new(Some(rn_weights));
    let results =
        metropolis_core::simulation::run_iteration(weights, None, None, 1, &preprocess_data)
            .unwrap();
    let agent_results = &results.iteration_results.agent_results()[agent_index(0)];

    // Departure time from origin: 0.
    // Departure time from origin of leg 0: 3.
    // Travel time on leg 0: 1.
    // Arrival time to destination of leg 0: 4.
    // Departure time from origin of leg 1: 6.
    // Travel time on leg 1: 6.
    // Arrival time to destination of leg 1: 12.
    // Departure time from origin of leg 2: 13.
    // Travel time on leg 2: 4 (2 fftt with multiplicator of 0.5).
    // Arrival time at destination of leg 2: 17.
    // Departure time from origin of leg 3: 18.
    // Arrival time at destination of leg 3: 18.
    // Arrival time at final destination: 18.
    //
    // Total travel time: 11.
    //
    // Utility for leg 0: (1 + (-1) * 1 + 1 * 1^2) - (5 - 4) * 0.5 = 1 - 0.5 = 0.5.
    // Utility for leg 1: (-1 * 6) - (12 - 10) * 0.2 = -6 - 0.4 = -6.4.
    // Utility for leg 2: 5 + 0 = 5.
    // Utility for leg 3: 0.
    // Origin schedule utility: -(1 - 0) * 2 = -2.
    // Destination schedule utility: -(18 - 15) * 2 = -6.
    // Total travel utility: -2 * 11^2 = -242.
    //
    // Total utility = -250.9.
    let leg0_results = LegResults {
        id: MetroId::Integer(1),
        departure_time: NonNegativeSeconds::try_from(3.0).unwrap(),
        arrival_time: NonNegativeSeconds::try_from(4.0).unwrap(),
        travel_utility: Utility::try_from(1.0).unwrap(),
        schedule_utility: Utility::try_from(-0.5).unwrap(),
        departure_time_shift: None,
        class: LegTypeResults::Road(RoadLegResults {
            expected_route: None,
            route: vec![RoadEvent {
                edge: MetroId::Integer(0),
                entry_time: NonNegativeSeconds::try_from(3.0).unwrap(),
            }],
            road_time: NonNegativeSeconds::try_from(1.0).unwrap(),
            in_bottleneck_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            out_bottleneck_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            route_free_flow_travel_time: NonNegativeSeconds::try_from(1.0).unwrap(),
            global_free_flow_travel_time: NonNegativeSeconds::try_from(1.0).unwrap(),
            length: NonNegativeMeters::try_from(1.0).unwrap(),
            length_diff: None,
            pre_exp_departure_time: NonNegativeSeconds::try_from(3.0).unwrap(),
            pre_exp_arrival_time: NonNegativeSeconds::try_from(4.0).unwrap(),
            exp_arrival_time: NonNegativeSeconds::try_from(4.0).unwrap(),
        }),
    };
    let leg1_results = LegResults {
        id: MetroId::Integer(2),
        departure_time: NonNegativeSeconds::try_from(6.0).unwrap(),
        arrival_time: NonNegativeSeconds::try_from(12.0).unwrap(),
        travel_utility: Utility::try_from(-6.0).unwrap(),
        schedule_utility: Utility::try_from(-0.4).unwrap(),
        departure_time_shift: None,
        class: LegTypeResults::Virtual,
    };
    let leg2_results = LegResults {
        id: MetroId::Integer(3),
        departure_time: NonNegativeSeconds::try_from(13.0).unwrap(),
        arrival_time: NonNegativeSeconds::try_from(17.0).unwrap(),
        travel_utility: Utility::try_from(5.0).unwrap(),
        schedule_utility: Utility::try_from(0.0).unwrap(),
        departure_time_shift: None,
        class: LegTypeResults::Road(RoadLegResults {
            expected_route: None,
            route: vec![RoadEvent {
                edge: MetroId::Integer(1),
                entry_time: NonNegativeSeconds::try_from(13.0).unwrap(),
            }],
            road_time: NonNegativeSeconds::try_from(4.0).unwrap(),
            in_bottleneck_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            out_bottleneck_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            route_free_flow_travel_time: NonNegativeSeconds::try_from(4.0).unwrap(),
            global_free_flow_travel_time: NonNegativeSeconds::try_from(4.0).unwrap(),
            length: NonNegativeMeters::try_from(2.0).unwrap(),
            length_diff: None,
            pre_exp_departure_time: NonNegativeSeconds::try_from(13.0).unwrap(),
            pre_exp_arrival_time: NonNegativeSeconds::try_from(17.0).unwrap(),
            exp_arrival_time: NonNegativeSeconds::try_from(17.0).unwrap(),
        }),
    };
    let leg3_results = LegResults {
        id: MetroId::Integer(4),
        departure_time: NonNegativeSeconds::try_from(18.0).unwrap(),
        arrival_time: NonNegativeSeconds::try_from(18.0).unwrap(),
        travel_utility: Utility::try_from(0.0).unwrap(),
        schedule_utility: Utility::try_from(0.0).unwrap(),
        departure_time_shift: None,
        class: LegTypeResults::Road(RoadLegResults {
            expected_route: None,
            route: vec![],
            road_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            in_bottleneck_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            out_bottleneck_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            route_free_flow_travel_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            global_free_flow_travel_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            length: NonNegativeMeters::try_from(0.0).unwrap(),
            length_diff: None,
            pre_exp_departure_time: NonNegativeSeconds::try_from(18.0).unwrap(),
            pre_exp_arrival_time: NonNegativeSeconds::try_from(18.0).unwrap(),
            exp_arrival_time: NonNegativeSeconds::try_from(18.0).unwrap(),
        }),
    };
    let expected_agent_results = AgentResult::new(
        MetroId::Integer(0),
        MetroId::Integer(1),
        mode_index(0),
        Utility::try_from(-250.9).unwrap(),
        ModeResults::Trip(TripResults {
            legs: vec![leg0_results, leg1_results, leg2_results, leg3_results],
            departure_time: NonNegativeSeconds::try_from(0.0).unwrap(),
            arrival_time: NonNegativeSeconds::try_from(18.0).unwrap(),
            total_travel_time: NonNegativeSeconds::try_from(11.0).unwrap(),
            utility: Utility::try_from(-250.9).unwrap(),
            expected_utility: Utility::try_from(-250.9).unwrap(),
            virtual_only: false,
            departure_time_shift: None,
        }),
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[0],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[0],
        "Problem with leg 0"
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[1],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[1],
        "Problem with leg 1"
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[2],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[2],
        "Problem with leg 2"
    );

    assert_eq!(
        agent_results.mode_results().as_trip().unwrap().legs[3],
        expected_agent_results
            .mode_results()
            .as_trip()
            .unwrap()
            .legs[3],
        "Problem with leg 3"
    );

    assert_eq!(agent_results, &expected_agent_results);
}
