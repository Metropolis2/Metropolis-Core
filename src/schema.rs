// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use choice::{ChoiceModel, ContinuousChoiceModel, LogitModel};
use hashbrown::HashSet;
use petgraph::graph::{edge_index, EdgeIndex, NodeIndex};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use ttf::{PwlTTF, TTF};

use crate::learning::{ExponentialLearningModel, LearningModel};
use crate::mode::fixed_ttf::{FixedTTFLeg, FixedTTFMode};
use crate::mode::road::RoadMode;
use crate::mode::{DepartureTimeModel, Mode};
use crate::network::road_network::vehicle::{vehicle_index, SpeedFunction, Vehicle};
use crate::network::road_network::{
    RoadEdge, RoadNetworkParameters, SpeedDensityFunction, ThreeRegimesSpeedDensityFunction,
};
use crate::network::NetworkParameters;
use crate::parameters::Parameters;
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
            Mode::Constant(Utility(1.0)),
            Mode::Road(example_road_mode()),
        ],
        Some(ChoiceModel::Logit(LogitModel::new(
            NoUnit(0.5),
            NoUnit(2.0),
        ))),
    )
}

pub(crate) fn example_road_mode() -> RoadMode<f64> {
    RoadMode::new(
        NodeIndex::new(0),
        NodeIndex::new(1),
        vehicle_index(0),
        DepartureTimeModel::ContinuousChoice {
            period: Interval([Time(0.0), Time(24.0 * 3600.0)]),
            choice_model: ContinuousChoiceModel::Logit(LogitModel::new(NoUnit(0.5), NoUnit(4.0))),
        },
        example_travel_utility(),
        ScheduleUtility::None,
        example_schedule_utility(),
    )
}

pub(crate) fn example_fixed_ttf_mode() -> FixedTTFMode<f64> {
    let leg0 = FixedTTFLeg::new(
        TTF::Constant(Time(10.0)),
        Time(5.0),
        TravelUtility::default(),
        ScheduleUtility::None,
    );
    let leg1 = FixedTTFLeg::new(
        TTF::Piecewise(PwlTTF::from_x_and_y(
            vec![Time(0.0), Time(100.0), Time(200.0)],
            vec![Time(10.0), Time(15.0), Time(10.0)],
        )),
        Time(0.0),
        TravelUtility::default(),
        ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(
                Time(120.0),
                Time(120.0),
                ValueOfTime(5.0),
                ValueOfTime(20.0),
            )
            .unwrap(),
        ),
    );
    FixedTTFMode::new(
        vec![leg0, leg1],
        DepartureTimeModel::ContinuousChoice {
            period: Interval([Time(0.0), Time(200.0)]),
            choice_model: ContinuousChoiceModel::Logit(LogitModel::new(NoUnit(0.5), NoUnit(1.0))),
        },
        TravelUtility::Polynomial(PolynomialFunction {
            b: -10.0,
            ..Default::default()
        }),
        ScheduleUtility::None,
    )
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
    let restricted_edges = [edge_index(0), edge_index(1)].into_iter().collect();
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
        Speed(50.0 / 3.6),
        Length(100.0),
        2,
        SpeedDensityFunction::ThreeRegimes(ThreeRegimesSpeedDensityFunction::new(
            0.3,
            0.8,
            Speed(10.0 / 3.6),
            2.0,
        )),
        Flow(0.4),
        Flow(0.4),
        Time(4.0),
    )
}

pub(crate) fn example_parameters() -> Parameters<f64> {
    Parameters::new(
        Interval([Time(6.0 * 3600.0), Time(12.0 * 3600.0)]),
        1,
        NetworkParameters {
            road_network: Some(RoadNetworkParameters::from_recording_interval(Time(60.0))),
        },
        LearningModel::Exponential(ExponentialLearningModel::new(0.9)),
        vec![
            StopCriterion::MaxIteration(100),
            StopCriterion::DepartureTime(Time(2.0), Time(3600.0)),
        ],
        1.0,
        Some(13081996),
    )
}
