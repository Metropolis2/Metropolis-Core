use crate::learning::{ExponentialLearningModel, LearningModel};
use crate::mode::road::{DepartureTimeModel, RoadMode};
use crate::mode::Mode;
use crate::network::road_network::vehicle::{vehicle_index, SpeedFunction, Vehicle};
use crate::network::road_network::{
    RoadEdge, SpeedDensityFunction, ThreeRegimesSpeedDensityFunction,
};
use crate::network::NetworkParameters;
use crate::schedule_utility::ScheduleUtility;
use crate::simulation::parameters::Parameters;
use crate::stop::StopCriterion;
use crate::travel_utility::TravelUtility;
use crate::units::*;
use crate::{agent::Agent, schedule_utility::alpha_beta_gamma::AlphaBetaGammaModel};

use choice::{ChoiceModel, ContinuousChoiceModel, LogitModel};
use petgraph::graph::NodeIndex;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, JsonSchema)]
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

pub fn example_agent() -> Agent<f64> {
    Agent::new(
        1,
        vec![
            Mode::Constant(Utility(1.0)),
            Mode::Road(example_road_mode()),
        ],
        ChoiceModel::Logit(LogitModel::new(NoUnit(0.5), NoUnit(2.0))),
        example_schedule_utility(),
    )
}

pub fn example_road_mode() -> RoadMode<f64> {
    RoadMode::new(
        NodeIndex::new(0),
        NodeIndex::new(1),
        vehicle_index(0),
        DepartureTimeModel::ContinuousChoice {
            period: Interval([Time(0.0), Time(24.0 * 3600.0)]),
            choice_model: ContinuousChoiceModel::Logit(LogitModel::new(NoUnit(0.5), NoUnit(4.0))),
        },
        example_travel_utility(),
    )
}

pub fn example_travel_utility() -> TravelUtility<f64> {
    TravelUtility::Proportional(ValueOfTime(-10.0))
}

pub fn example_travel_utility2() -> TravelUtility<f64> {
    TravelUtility::Quadratic {
        a: ValueOfTime(-5.0),
        b: ValueOfTime(-2.0),
    }
}

pub fn example_schedule_utility() -> ScheduleUtility<f64> {
    ScheduleUtility::AlphaBetaGamma(AlphaBetaGammaModel::new(
        Time(7.75 * 3600.0),
        Time(8.25 * 3800.0),
        ValueOfTime(5.0),
        ValueOfTime(20.0),
        true,
    ))
}

pub fn example_vehicle() -> Vehicle<f64> {
    Vehicle::new(Length(8.0), PCE(1.0), SpeedFunction::Multiplicator(0.8))
}

pub fn example_vehicle2() -> Vehicle<f64> {
    let func = SpeedFunction::Piecewise(vec![
        [Speed(0.0), Speed(0.0)],
        [Speed(90.0), Speed(90.0)],
        [Speed(130.0), Speed(90.0)],
    ]);
    Vehicle::new(Length(20.0), PCE(3.0), func)
}

pub fn example_road_edge() -> RoadEdge<f64> {
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
        Outflow(0.4),
    )
}

pub fn example_parameters() -> Parameters<f64> {
    Parameters::new(
        Interval([Time(6.0 * 3600.0), Time(12.0 * 3600.0)]),
        NetworkParameters::default(),
        LearningModel::Exponential(ExponentialLearningModel::new(0.9)),
        vec![
            StopCriterion::MaxIteration(100),
            StopCriterion::DepartureTime(Time(2.0), Time(3600.0)),
        ],
        1.0,
        Some(13081996),
    )
}
