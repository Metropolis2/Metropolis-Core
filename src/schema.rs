// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use choice::{ChoiceModel, ContinuousChoiceModel, LogitModel};
use hashbrown::HashSet;
use petgraph::graph::{EdgeIndex, NodeIndex};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::learning::LearningModel;
use crate::mode::trip::{DepartureTimeModel, Leg, LegType, RoadLeg, TravelingMode};
use crate::mode::Mode;
use crate::network::road_network::vehicle::{vehicle_index, SpeedFunction, Vehicle};
use crate::network::road_network::{
    RoadEdge, RoadNetworkParameters, SpeedDensityFunction, ThreeRegimesSpeedDensityFunction,
};
use crate::network::NetworkParameters;
use crate::parameters::{Parameters, SavingFormat};
use crate::schedule_utility::ScheduleUtility;
use crate::stop::StopCriterion;
use crate::travel_utility::{PolynomialFunction, TravelUtility};
use crate::units::*;
use crate::{agent::Agent, schedule_utility::alpha_beta_gamma::AlphaBetaGammaModel};

#[derive(Clone, Copy, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(remote = "NodeIndex")]
pub struct NodeIndexDef(#[serde(getter = "get_node_index")] usize);

fn get_node_index(node: &NodeIndex) -> usize {
    node.index()
}

impl From<NodeIndexDef> for NodeIndex {
    fn from(def: NodeIndexDef) -> NodeIndex {
        NodeIndex::new(def.0)
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(remote = "EdgeIndex")]
pub struct EdgeIndexDef(#[serde(getter = "get_edge_index")] usize);

fn get_edge_index(edge: &EdgeIndex) -> usize {
    edge.index()
}

impl From<EdgeIndexDef> for EdgeIndex {
    fn from(def: EdgeIndexDef) -> EdgeIndex {
        EdgeIndex::new(def.0)
    }
}

pub(crate) fn example_agent() -> Agent<f64> {
    Agent::new(
        1,
        vec![
            Mode::Constant((1, Utility(1.0))),
            Mode::Trip(example_trip()),
        ],
        Some(ChoiceModel::Logit(LogitModel::new(
            NoUnit(0.5),
            NoUnit(2.0),
        ))),
    )
}

pub(crate) fn example_trip() -> TravelingMode<f64> {
    let leg = Leg::new(
        0,
        LegType::Road(RoadLeg::new(0, 1, vehicle_index(0))),
        Time(600.0),
        TravelUtility::Polynomial(PolynomialFunction {
            b: -0.02,
            ..Default::default()
        }),
        ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(
                Time(100.0),
                Time(100.0),
                ValueOfTime(0.01),
                ValueOfTime(0.04),
            )
            .unwrap(),
        ),
    );
    TravelingMode::new(
        1,
        vec![leg],
        Time(300.0),
        example_departure_time_model(),
        TravelUtility::Polynomial(PolynomialFunction {
            c: 0.001,
            ..Default::default()
        }),
        ScheduleUtility::None,
        ScheduleUtility::None,
    )
}

pub(crate) fn example_departure_time_model() -> DepartureTimeModel<f64> {
    DepartureTimeModel::ContinuousChoice {
        period: Interval([Time(0.0), Time(200.0)]),
        choice_model: ContinuousChoiceModel::Logit(LogitModel::new(NoUnit(0.5), NoUnit(1.0))),
    }
}

pub(crate) fn example_travel_utility() -> TravelUtility<f64> {
    TravelUtility::Polynomial(PolynomialFunction {
        b: -10.,
        ..Default::default()
    })
}

pub(crate) fn example_travel_utility2() -> TravelUtility<f64> {
    TravelUtility::Polynomial(PolynomialFunction {
        b: -5.,
        c: -2.,
        ..Default::default()
    })
}

pub(crate) fn example_schedule_utility() -> ScheduleUtility<f64> {
    ScheduleUtility::AlphaBetaGamma(
        AlphaBetaGammaModel::new(
            Time(7.75 * 3600.0),
            Time(8.25 * 3800.0),
            ValueOfTime(5.0),
            ValueOfTime(20.0),
        )
        .unwrap(),
    )
}

pub(crate) fn example_vehicle() -> Vehicle<f64> {
    Vehicle::new(
        Length(8.0),
        PCE(1.0),
        SpeedFunction::Multiplicator(0.8),
        HashSet::new(),
        HashSet::new(),
    )
}

pub(crate) fn example_vehicle2() -> Vehicle<f64> {
    let func = SpeedFunction::Piecewise(vec![
        [Speed(0.0), Speed(0.0)],
        [Speed(90.0), Speed(90.0)],
        [Speed(130.0), Speed(90.0)],
    ]);
    let restricted_edges = [0, 1].into_iter().collect();
    Vehicle::new(
        Length(20.0),
        PCE(3.0),
        func,
        HashSet::new(),
        restricted_edges,
    )
}

pub(crate) fn example_road_edge() -> RoadEdge<f64> {
    RoadEdge::new(
        1,
        Speed(50.0 / 3.6),
        Length(100.0),
        Lanes(2.0),
        SpeedDensityFunction::ThreeRegimes(ThreeRegimesSpeedDensityFunction::new(
            0.3,
            0.8,
            Speed(10.0 / 3.6),
            2.0,
        )),
        Flow(0.4),
        Time(4.0),
        true,
    )
}

pub(crate) fn example_parameters() -> Parameters<f64> {
    Parameters {
        period: Interval([Time(6.0 * 3600.0), Time(12.0 * 3600.0)]),
        init_iteration_counter: 1,
        network: NetworkParameters {
            road_network: Some(RoadNetworkParameters {
                recording_interval: Time(300.0),
                approximation_bound: Time(1.0),
                spillback: true,
                backward_wave_speed: Some(Speed(4.0)),
                max_pending_duration: Time(30.0),
                constrain_inflow: true,
                algorithm_type: Default::default(),
                contraction: Default::default(),
            }),
        },
        learning_model: LearningModel::Exponential(0.9),
        stopping_criteria: vec![
            StopCriterion::MaxIteration(100),
            StopCriterion::DepartureTime(Time(2.0)),
        ],
        update_ratio: 1.0,
        random_seed: Some(13081996),
        nb_threads: 8,
        saving_format: SavingFormat::JSON,
    }
}
