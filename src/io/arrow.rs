// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Utility functions to work with arrow format.

use std::sync::Arc;

use anyhow::Result;
use arrow::array::{Float64Builder, UInt64Builder};
use arrow::datatypes::{DataType, Field, Schema as ArrowSchema};
use arrow::record_batch::RecordBatch;
use num_traits::ToPrimitive;
use polars::prelude::DataType as PolarsDataType;
use polars::prelude::*;
use smartstring::SmartString;
use ttf::TTFNum;

use crate::mode::trip::results::{LegTypeResults, PreDayLegTypeResults};
use crate::mode::{ModeResults, PreDayModeResults};
use crate::simulation::results::{
    AgentResult, AgentResults, AggregateResults, PreDayAgentResult, PreDayAgentResults,
};

pub trait ToArrow<const J: usize> {
    fn to_arrow(data: Self) -> Result<[RecordBatch; J]>;
    fn names<'a>() -> [&'a str; J];
}

pub trait ToPolars {
    fn to_dataframe(self) -> Result<DataFrame>;
    fn schema() -> Schema;
}

#[derive(Debug, Default)]
struct AgentResultsBuilder {
    // Values at the agent level.
    id: UInt64Builder,
    mode_id: UInt64Builder,
    mode_index: UInt64Builder,
    expected_utility: Float64Builder,
    departure_time: Float64Builder,
    arrival_time: Float64Builder,
    total_travel_time: Float64Builder,
    utility: Float64Builder,
    mode_expected_utility: Float64Builder,
    nb_road_legs: UInt64Builder,
    nb_virtual_legs: UInt64Builder,
    // Values at the leg level.
    leg_agent_id: UInt64Builder,
    leg_id: UInt64Builder,
    leg_index: UInt64Builder,
    leg_departure_time: Float64Builder,
    leg_arrival_time: Float64Builder,
    leg_travel_utility: Float64Builder,
    leg_schedule_utility: Float64Builder,
    leg_road_time: Float64Builder,
    leg_in_bottleneck_time: Float64Builder,
    leg_out_bottleneck_time: Float64Builder,
    leg_route_free_flow_travel_time: Float64Builder,
    leg_global_free_flow_travel_time: Float64Builder,
    leg_length: Float64Builder,
    leg_pre_exp_departure_time: Float64Builder,
    leg_pre_exp_arrival_time: Float64Builder,
    leg_exp_arrival_time: Float64Builder,
    leg_nb_edges: UInt64Builder,
    // Values at the route level.
    route_agent_id: UInt64Builder,
    route_leg_id: UInt64Builder,
    route_leg_index: UInt64Builder,
    route_edge_id: UInt64Builder,
    route_entry_time: Float64Builder,
    route_exit_time: Float64Builder,
}

impl AgentResultsBuilder {
    fn append<T: ToPrimitive>(&mut self, agent_result: AgentResult<T>) {
        self.id.append_value(agent_result.id as u64);
        self.mode_id.append_value(agent_result.mode_id as u64);
        self.mode_index
            .append_value(agent_result.mode_index.index() as u64);
        self.expected_utility
            .append_value(agent_result.expected_utility.to_f64().unwrap());
        if let ModeResults::Trip(trip) = &agent_result.mode_results {
            self.departure_time
                .append_value(trip.departure_time.to_f64().unwrap());
            self.arrival_time
                .append_value(trip.arrival_time.to_f64().unwrap());
            self.total_travel_time
                .append_value(trip.total_travel_time.to_f64().unwrap());
            self.utility.append_value(trip.utility.to_f64().unwrap());
            self.mode_expected_utility
                .append_value(trip.expected_utility.to_f64().unwrap());
            let mut nb_road_legs = 0;
            let mut nb_virtual_legs = 0;
            for (i, leg) in trip.legs.iter().enumerate() {
                self.leg_agent_id.append_value(agent_result.id as u64);
                self.leg_id.append_value(leg.id as u64);
                self.leg_index.append_value(i as u64);
                self.leg_departure_time
                    .append_value(leg.departure_time.to_f64().unwrap());
                self.leg_arrival_time
                    .append_value(leg.arrival_time.to_f64().unwrap());
                self.leg_travel_utility
                    .append_value(leg.travel_utility.to_f64().unwrap());
                self.leg_schedule_utility
                    .append_value(leg.schedule_utility.to_f64().unwrap());
                if let LegTypeResults::Road(road_leg) = &leg.class {
                    nb_road_legs += 1;
                    self.leg_road_time
                        .append_value(road_leg.road_time.to_f64().unwrap());
                    self.leg_in_bottleneck_time
                        .append_value(road_leg.in_bottleneck_time.to_f64().unwrap());
                    self.leg_out_bottleneck_time
                        .append_value(road_leg.out_bottleneck_time.to_f64().unwrap());
                    self.leg_route_free_flow_travel_time
                        .append_value(road_leg.route_free_flow_travel_time.to_f64().unwrap());
                    self.leg_global_free_flow_travel_time
                        .append_value(road_leg.global_free_flow_travel_time.to_f64().unwrap());
                    self.leg_length
                        .append_value(road_leg.length.to_f64().unwrap());
                    self.leg_pre_exp_departure_time
                        .append_value(road_leg.pre_exp_departure_time.to_f64().unwrap());
                    self.leg_pre_exp_arrival_time
                        .append_value(road_leg.pre_exp_arrival_time.to_f64().unwrap());
                    self.leg_exp_arrival_time
                        .append_value(road_leg.exp_arrival_time.to_f64().unwrap());
                    self.leg_nb_edges.append_value(road_leg.route.len() as u64);
                    for window in road_leg.route.windows(2) {
                        let event = &window[0];
                        let next_event = &window[1];
                        self.route_agent_id.append_value(agent_result.id as u64);
                        self.route_leg_id.append_value(leg.id as u64);
                        self.route_leg_index.append_value(i as u64);
                        self.route_edge_id.append_value(event.edge);
                        self.route_entry_time
                            .append_value(event.entry_time.to_f64().unwrap());
                        self.route_exit_time
                            .append_value(next_event.entry_time.to_f64().unwrap());
                    }
                    // The last event is not added by the previous for loop.
                    if let Some(last_event) = road_leg.route.last() {
                        self.route_agent_id.append_value(agent_result.id as u64);
                        self.route_leg_id.append_value(leg.id as u64);
                        self.route_leg_index.append_value(i as u64);
                        self.route_edge_id.append_value(last_event.edge);
                        self.route_entry_time
                            .append_value(last_event.entry_time.to_f64().unwrap());
                        self.route_exit_time
                            .append_value(leg.arrival_time.to_f64().unwrap());
                    }
                } else {
                    nb_virtual_legs += 1;
                    self.leg_road_time.append_null();
                    self.leg_in_bottleneck_time.append_null();
                    self.leg_out_bottleneck_time.append_null();
                    self.leg_route_free_flow_travel_time.append_null();
                    self.leg_global_free_flow_travel_time.append_null();
                    self.leg_length.append_null();
                    self.leg_pre_exp_departure_time.append_null();
                    self.leg_pre_exp_arrival_time.append_null();
                    self.leg_exp_arrival_time.append_null();
                    self.leg_nb_edges.append_null();
                }
            }
            self.nb_road_legs.append_value(nb_road_legs);
            self.nb_virtual_legs.append_value(nb_virtual_legs);
        } else {
            self.departure_time.append_null();
            self.arrival_time.append_null();
            self.total_travel_time.append_null();
            self.utility.append_null();
            self.mode_expected_utility.append_null();
            self.nb_road_legs.append_null();
            self.nb_virtual_legs.append_null();
        }
    }

    fn finish(&mut self) -> Result<[RecordBatch; 3]> {
        let agent_schema = ArrowSchema::new(vec![
            Field::new("id", DataType::UInt64, false),
            Field::new("mode_id", DataType::UInt64, false),
            Field::new("mode_index", DataType::UInt64, false),
            Field::new("expected_utility", DataType::Float64, false),
            Field::new("departure_time", DataType::Float64, true),
            Field::new("arrival_time", DataType::Float64, true),
            Field::new("total_travel_time", DataType::Float64, true),
            Field::new("utility", DataType::Float64, true),
            Field::new("mode_expected_utility", DataType::Float64, true),
            Field::new("nb_road_legs", DataType::UInt64, true),
            Field::new("nb_virtual_legs", DataType::UInt64, true),
        ]);
        let agent_batch = RecordBatch::try_new(
            Arc::new(agent_schema),
            vec![
                Arc::new(self.id.finish()),
                Arc::new(self.mode_id.finish()),
                Arc::new(self.mode_index.finish()),
                Arc::new(self.expected_utility.finish()),
                Arc::new(self.departure_time.finish()),
                Arc::new(self.arrival_time.finish()),
                Arc::new(self.total_travel_time.finish()),
                Arc::new(self.utility.finish()),
                Arc::new(self.mode_expected_utility.finish()),
                Arc::new(self.nb_road_legs.finish()),
                Arc::new(self.nb_virtual_legs.finish()),
            ],
        )?;
        let leg_schema = ArrowSchema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("leg_id", DataType::UInt64, false),
            Field::new("leg_index", DataType::UInt64, false),
            Field::new("departure_time", DataType::Float64, false),
            Field::new("arrival_time", DataType::Float64, false),
            Field::new("travel_utility", DataType::Float64, false),
            Field::new("schedule_utility", DataType::Float64, false),
            Field::new("road_time", DataType::Float64, true),
            Field::new("in_bottleneck_time", DataType::Float64, true),
            Field::new("out_bottleneck_time", DataType::Float64, true),
            Field::new("route_free_flow_travel_time", DataType::Float64, true),
            Field::new("global_free_flow_travel_time", DataType::Float64, true),
            Field::new("length", DataType::Float64, true),
            Field::new("pre_exp_departure_time", DataType::Float64, true),
            Field::new("pre_exp_arrival_time", DataType::Float64, true),
            Field::new("exp_arrival_time", DataType::Float64, true),
            Field::new("nb_edges", DataType::UInt64, true),
        ]);
        let leg_batch = RecordBatch::try_new(
            Arc::new(leg_schema),
            vec![
                Arc::new(self.leg_agent_id.finish()),
                Arc::new(self.leg_id.finish()),
                Arc::new(self.leg_index.finish()),
                Arc::new(self.leg_departure_time.finish()),
                Arc::new(self.leg_arrival_time.finish()),
                Arc::new(self.leg_travel_utility.finish()),
                Arc::new(self.leg_schedule_utility.finish()),
                Arc::new(self.leg_road_time.finish()),
                Arc::new(self.leg_in_bottleneck_time.finish()),
                Arc::new(self.leg_out_bottleneck_time.finish()),
                Arc::new(self.leg_route_free_flow_travel_time.finish()),
                Arc::new(self.leg_global_free_flow_travel_time.finish()),
                Arc::new(self.leg_length.finish()),
                Arc::new(self.leg_pre_exp_departure_time.finish()),
                Arc::new(self.leg_pre_exp_arrival_time.finish()),
                Arc::new(self.leg_exp_arrival_time.finish()),
                Arc::new(self.leg_nb_edges.finish()),
            ],
        )?;
        let route_schema = ArrowSchema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("leg_id", DataType::UInt64, false),
            Field::new("leg_index", DataType::UInt64, false),
            Field::new("edge_id", DataType::UInt64, false),
            Field::new("entry_time", DataType::Float64, false),
            Field::new("exit_time", DataType::Float64, false),
        ]);
        let route_batch = RecordBatch::try_new(
            Arc::new(route_schema),
            vec![
                Arc::new(self.route_agent_id.finish()),
                Arc::new(self.route_leg_id.finish()),
                Arc::new(self.route_leg_index.finish()),
                Arc::new(self.route_edge_id.finish()),
                Arc::new(self.route_entry_time.finish()),
                Arc::new(self.route_exit_time.finish()),
            ],
        )?;
        Ok([agent_batch, leg_batch, route_batch])
    }
}

impl<T: ToPrimitive> ToArrow<3> for AgentResults<T> {
    fn to_arrow(data: AgentResults<T>) -> Result<[RecordBatch; 3]> {
        let mut builder = AgentResultsBuilder::default();
        data.0.into_iter().for_each(|row| builder.append(row));
        builder.finish()
    }
    fn names<'a>() -> [&'a str; 3] {
        ["agent_results", "leg_results", "route_results"]
    }
}

#[derive(Debug, Default)]
struct PreDayAgentResultsBuilder {
    // Values at the agent level.
    id: UInt64Builder,
    mode_id: UInt64Builder,
    mode_index: UInt64Builder,
    expected_utility: Float64Builder,
    departure_time: Float64Builder,
    mode_expected_utility: Float64Builder,
    nb_road_legs: UInt64Builder,
    nb_virtual_legs: UInt64Builder,
    // Values at the leg level.
    leg_agent_id: UInt64Builder,
    leg_id: UInt64Builder,
    leg_index: UInt64Builder,
    leg_route_free_flow_travel_time: Float64Builder,
    leg_global_free_flow_travel_time: Float64Builder,
    leg_length: Float64Builder,
    leg_pre_exp_departure_time: Float64Builder,
    leg_pre_exp_arrival_time: Float64Builder,
    leg_nb_edges: UInt64Builder,
    // Values at the route level.
    route_agent_id: UInt64Builder,
    route_leg_id: UInt64Builder,
    route_leg_index: UInt64Builder,
    route_edge_id: UInt64Builder,
    route_entry_time: Float64Builder,
    route_exit_time: Float64Builder,
}

impl PreDayAgentResultsBuilder {
    fn append<T: ToPrimitive>(&mut self, agent_result: PreDayAgentResult<T>) {
        self.id.append_value(agent_result.id as u64);
        self.mode_id.append_value(agent_result.mode_id as u64);
        self.mode_index
            .append_value(agent_result.mode_index.index() as u64);
        self.expected_utility
            .append_value(agent_result.expected_utility.to_f64().unwrap());
        if let PreDayModeResults::Trip(trip) = &agent_result.mode_results {
            self.departure_time
                .append_value(trip.departure_time.to_f64().unwrap());
            self.mode_expected_utility
                .append_value(trip.expected_utility.to_f64().unwrap());
            let mut nb_road_legs = 0;
            let mut nb_virtual_legs = 0;
            for (i, leg) in trip.legs.iter().enumerate() {
                self.leg_agent_id.append_value(agent_result.id as u64);
                self.leg_id.append_value(leg.id as u64);
                self.leg_index.append_value(i as u64);
                if let PreDayLegTypeResults::Road(road_leg) = &leg.class {
                    nb_road_legs += 1;
                    self.leg_route_free_flow_travel_time
                        .append_value(road_leg.route_free_flow_travel_time.to_f64().unwrap());
                    self.leg_global_free_flow_travel_time
                        .append_value(road_leg.global_free_flow_travel_time.to_f64().unwrap());
                    self.leg_length
                        .append_value(road_leg.length.to_f64().unwrap());
                    self.leg_pre_exp_departure_time
                        .append_value(road_leg.pre_exp_departure_time.to_f64().unwrap());
                    self.leg_pre_exp_arrival_time
                        .append_value(road_leg.pre_exp_arrival_time.to_f64().unwrap());
                    self.leg_nb_edges.append_value(road_leg.route.len() as u64);
                    for window in road_leg.route.windows(2) {
                        let event = &window[0];
                        let next_event = &window[1];
                        self.route_agent_id.append_value(agent_result.id as u64);
                        self.route_leg_id.append_value(leg.id as u64);
                        self.route_leg_index.append_value(i as u64);
                        self.route_edge_id.append_value(event.edge);
                        self.route_entry_time
                            .append_value(event.entry_time.to_f64().unwrap());
                        self.route_exit_time
                            .append_value(next_event.entry_time.to_f64().unwrap());
                    }
                    // The last event is not added by the previous for loop.
                    if let Some(last_event) = road_leg.route.last() {
                        self.route_agent_id.append_value(agent_result.id as u64);
                        self.route_leg_id.append_value(leg.id as u64);
                        self.route_leg_index.append_value(i as u64);
                        self.route_edge_id.append_value(last_event.edge);
                        self.route_entry_time
                            .append_value(last_event.entry_time.to_f64().unwrap());
                        self.route_exit_time
                            .append_value(road_leg.pre_exp_arrival_time.to_f64().unwrap());
                    }
                } else {
                    nb_virtual_legs += 1;
                    self.leg_route_free_flow_travel_time.append_null();
                    self.leg_global_free_flow_travel_time.append_null();
                    self.leg_length.append_null();
                    self.leg_pre_exp_departure_time.append_null();
                    self.leg_pre_exp_arrival_time.append_null();
                    self.leg_nb_edges.append_null();
                }
            }
            self.nb_road_legs.append_value(nb_road_legs);
            self.nb_virtual_legs.append_value(nb_virtual_legs);
        } else {
            self.departure_time.append_null();
            self.mode_expected_utility.append_null();
            self.nb_road_legs.append_null();
            self.nb_virtual_legs.append_null();
        }
    }

    fn finish(&mut self) -> Result<[RecordBatch; 3]> {
        let agent_schema = ArrowSchema::new(vec![
            Field::new("id", DataType::UInt64, false),
            Field::new("mode_id", DataType::UInt64, false),
            Field::new("mode_index", DataType::UInt64, false),
            Field::new("expected_utility", DataType::Float64, false),
            Field::new("departure_time", DataType::Float64, true),
            Field::new("mode_expected_utility", DataType::Float64, true),
            Field::new("nb_road_legs", DataType::UInt64, true),
            Field::new("nb_virtual_legs", DataType::UInt64, true),
        ]);
        let agent_batch = RecordBatch::try_new(
            Arc::new(agent_schema),
            vec![
                Arc::new(self.id.finish()),
                Arc::new(self.mode_id.finish()),
                Arc::new(self.mode_index.finish()),
                Arc::new(self.expected_utility.finish()),
                Arc::new(self.departure_time.finish()),
                Arc::new(self.mode_expected_utility.finish()),
                Arc::new(self.nb_road_legs.finish()),
                Arc::new(self.nb_virtual_legs.finish()),
            ],
        )?;
        let leg_schema = ArrowSchema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("leg_id", DataType::UInt64, false),
            Field::new("leg_index", DataType::UInt64, false),
            Field::new("route_free_flow_travel_time", DataType::Float64, true),
            Field::new("global_free_flow_travel_time", DataType::Float64, true),
            Field::new("length", DataType::Float64, true),
            Field::new("pre_exp_departure_time", DataType::Float64, true),
            Field::new("pre_exp_arrival_time", DataType::Float64, true),
            Field::new("nb_edges", DataType::UInt64, true),
        ]);
        let leg_batch = RecordBatch::try_new(
            Arc::new(leg_schema),
            vec![
                Arc::new(self.leg_agent_id.finish()),
                Arc::new(self.leg_id.finish()),
                Arc::new(self.leg_index.finish()),
                Arc::new(self.leg_route_free_flow_travel_time.finish()),
                Arc::new(self.leg_global_free_flow_travel_time.finish()),
                Arc::new(self.leg_length.finish()),
                Arc::new(self.leg_pre_exp_departure_time.finish()),
                Arc::new(self.leg_pre_exp_arrival_time.finish()),
                Arc::new(self.leg_nb_edges.finish()),
            ],
        )?;
        let route_schema = ArrowSchema::new(vec![
            Field::new("agent_id", DataType::UInt64, false),
            Field::new("leg_id", DataType::UInt64, false),
            Field::new("leg_index", DataType::UInt64, false),
            Field::new("edge_id", DataType::UInt64, false),
            Field::new("entry_time", DataType::Float64, false),
            Field::new("exit_time", DataType::Float64, false),
        ]);
        let route_batch = RecordBatch::try_new(
            Arc::new(route_schema),
            vec![
                Arc::new(self.route_agent_id.finish()),
                Arc::new(self.route_leg_id.finish()),
                Arc::new(self.route_leg_index.finish()),
                Arc::new(self.route_edge_id.finish()),
                Arc::new(self.route_entry_time.finish()),
                Arc::new(self.route_exit_time.finish()),
            ],
        )?;
        Ok([agent_batch, leg_batch, route_batch])
    }
}

impl<T: ToPrimitive> ToArrow<3> for PreDayAgentResults<T> {
    fn to_arrow(data: PreDayAgentResults<T>) -> Result<[RecordBatch; 3]> {
        let mut builder = PreDayAgentResultsBuilder::default();
        data.0.into_iter().for_each(|row| builder.append(row));
        builder.finish()
    }
    fn names<'a>() -> [&'a str; 3] {
        ["agent_results", "leg_results", "route_results"]
    }
}

macro_rules! add_const {
    ($df:ident, $name:expr, $const:expr) => {
        $df.with_column(Series::new($name, &[$const]))?;
    };
}

macro_rules! add_null_const {
    ($df:ident, $name:expr, $type:expr) => {
        $df.with_column(Series::full_null($name, 1, &$type))?;
    };
}

macro_rules! add_distr {
    ($df:ident, $name:expr, $var:expr) => {
        $df.with_column(Series::new(
            concat!($name, "_mean"),
            &[$var.mean().to_f64().unwrap()],
        ))?;
        $df.with_column(Series::new(
            concat!($name, "_std"),
            &[$var.std().to_f64().unwrap()],
        ))?;
        $df.with_column(Series::new(
            concat!($name, "_min"),
            &[$var.min().to_f64().unwrap()],
        ))?;
        $df.with_column(Series::new(
            concat!($name, "_max"),
            &[$var.max().to_f64().unwrap()],
        ))?;
    };
}

macro_rules! add_null_distr {
    ($df:ident, $name:expr) => {
        $df.with_column(Series::full_null(
            concat!($name, "_mean"),
            1,
            &PolarsDataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            concat!($name, "_std"),
            1,
            &PolarsDataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            concat!($name, "_min"),
            1,
            &PolarsDataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            concat!($name, "_max"),
            1,
            &PolarsDataType::Float64,
        ))?;
    };
}

macro_rules! add_null_road_leg_columns {
    ($df:ident) => {
        add_null_const!($df, "road_leg_count", PolarsDataType::UInt64);
        add_null_const!(
            $df,
            "nb_agents_at_least_one_road_leg",
            PolarsDataType::UInt64
        );
        add_null_const!($df, "nb_agents_all_road_legs", PolarsDataType::UInt64);
        add_null_distr!($df, "road_leg_count_by_agent");
        add_null_distr!($df, "road_leg_departure_time");
        add_null_distr!($df, "road_leg_arrival_time");
        add_null_distr!($df, "road_leg_road_time");
        add_null_distr!($df, "road_leg_in_bottleneck_time");
        add_null_distr!($df, "road_leg_out_bottleneck_time");
        add_null_distr!($df, "road_leg_travel_time");
        add_null_distr!($df, "road_leg_route_free_flow_travel_time");
        add_null_distr!($df, "road_leg_global_free_flow_travel_time");
        add_null_distr!($df, "road_leg_route_congestion");
        add_null_distr!($df, "road_leg_global_congestion");
        add_null_distr!($df, "road_leg_length");
        add_null_distr!($df, "road_leg_edge_count");
        add_null_distr!($df, "road_leg_utility");
        add_null_distr!($df, "road_leg_exp_travel_time");
        add_null_distr!($df, "road_leg_exp_travel_time_diff");
        add_null_distr!($df, "road_leg_length_diff");
    };
}

macro_rules! add_null_virtual_leg_columns {
    ($df:ident) => {
        add_null_const!($df, "virtual_leg_count", PolarsDataType::UInt64);
        add_null_const!(
            $df,
            "nb_agents_at_least_one_virtual_leg",
            PolarsDataType::UInt64
        );
        add_null_const!($df, "nb_agents_all_virtual_legs", PolarsDataType::UInt64);
        add_null_distr!($df, "virtual_leg_count_by_agent");
        add_null_distr!($df, "virtual_leg_departure_time");
        add_null_distr!($df, "virtual_leg_arrival_time");
        add_null_distr!($df, "virtual_leg_travel_time");
        add_null_distr!($df, "virtual_leg_global_free_flow_travel_time");
        add_null_distr!($df, "virtual_leg_global_congestion");
        add_null_distr!($df, "virtual_leg_utility");
    };
}

macro_rules! add_distr_to_schema {
    ($schema:ident, $name:expr) => {
        $schema.with_column(
            SmartString::from(concat!($name, "_mean")),
            PolarsDataType::Float64,
        );
        $schema.with_column(
            SmartString::from(concat!($name, "_std")),
            PolarsDataType::Float64,
        );
        $schema.with_column(
            SmartString::from(concat!($name, "_min")),
            PolarsDataType::Float64,
        );
        $schema.with_column(
            SmartString::from(concat!($name, "_max")),
            PolarsDataType::Float64,
        );
    };
}

macro_rules! add_cst_to_schema {
    ($schema:ident, $name:expr, $dtype:expr) => {
        $schema.with_column(SmartString::from($name), $dtype);
    };
}

impl<T: TTFNum> ToPolars for AggregateResults<T> {
    fn to_dataframe(self) -> Result<DataFrame> {
        let mut df = DataFrame::new(vec![Series::new(
            "iteration_counter",
            &[self.iteration_counter],
        )])?;
        add_distr!(df, "surplus", self.surplus);
        if let Some(trip_results) = self.mode_results.trip_modes {
            add_const!(df, "trip_count", trip_results.count as u64);
            add_distr!(df, "trip_departure_time", trip_results.departure_time);
            add_distr!(df, "trip_arrival_time", trip_results.arrival_time);
            add_distr!(df, "trip_travel_time", trip_results.travel_time);
            add_distr!(df, "trip_utility", trip_results.utility);
            add_distr!(df, "trip_expected_utility", trip_results.expected_utility);
            if let Some(dep_time_shift) = trip_results.dep_time_shift {
                add_distr!(df, "trip_dep_time_shift", dep_time_shift);
            } else {
                add_null_distr!(df, "trip_dep_time_shift");
            }
            if let Some(dep_time_rmse) = trip_results.dep_time_rmse {
                add_const!(df, "trip_dep_time_rmse", dep_time_rmse.to_f64().unwrap());
            } else {
                add_null_const!(df, "trip_dep_time_rmse", PolarsDataType::Float64);
            }
            if let Some(road_results) = trip_results.road_leg {
                add_const!(df, "road_leg_count", road_results.count as u64);
                add_const!(
                    df,
                    "nb_agents_at_least_one_road_leg",
                    road_results.mode_count_one as u64
                );
                add_const!(
                    df,
                    "nb_agents_all_road_legs",
                    road_results.mode_count_all as u64
                );
                add_distr!(
                    df,
                    "road_leg_count_by_agent",
                    road_results.count_distribution
                );
                add_distr!(df, "road_leg_departure_time", road_results.departure_time);
                add_distr!(df, "road_leg_arrival_time", road_results.arrival_time);
                add_distr!(df, "road_leg_road_time", road_results.road_time);
                add_distr!(
                    df,
                    "road_leg_in_bottleneck_time",
                    road_results.in_bottleneck_time
                );
                add_distr!(
                    df,
                    "road_leg_out_bottleneck_time",
                    road_results.out_bottleneck_time
                );
                add_distr!(df, "road_leg_travel_time", road_results.travel_time);
                add_distr!(
                    df,
                    "road_leg_route_free_flow_travel_time",
                    road_results.route_free_flow_travel_time
                );
                add_distr!(
                    df,
                    "road_leg_global_free_flow_travel_time",
                    road_results.global_free_flow_travel_time
                );
                add_distr!(
                    df,
                    "road_leg_route_congestion",
                    road_results.route_congestion
                );
                add_distr!(
                    df,
                    "road_leg_global_congestion",
                    road_results.global_congestion
                );
                add_distr!(df, "road_leg_length", road_results.length);
                add_distr!(df, "road_leg_edge_count", road_results.edge_count);
                add_distr!(df, "road_leg_utility", road_results.utility);
                add_distr!(df, "road_leg_exp_travel_time", road_results.exp_travel_time);
                add_distr!(
                    df,
                    "road_leg_exp_travel_time_rel_diff",
                    road_results.exp_travel_time_rel_diff
                );
                add_distr!(
                    df,
                    "road_leg_exp_travel_time_abs_diff",
                    road_results.exp_travel_time_abs_diff
                );
                add_const!(
                    df,
                    "road_leg_exp_travel_time_diff_rmse",
                    road_results.exp_travel_time_diff_rmse.to_f64().unwrap()
                );
                if let Some(length_diff) = road_results.length_diff {
                    add_distr!(df, "road_leg_length_diff", length_diff);
                } else {
                    add_null_distr!(df, "road_leg_length_diff");
                }
            } else {
                add_null_road_leg_columns!(df);
            }
            if let Some(virtual_results) = trip_results.virtual_leg {
                add_const!(df, "virtual_leg_count", virtual_results.count as u64);
                add_const!(
                    df,
                    "nb_agents_at_least_one_virtual_leg",
                    virtual_results.mode_count_one as u64
                );
                add_const!(
                    df,
                    "nb_agents_all_virtual_legs",
                    virtual_results.mode_count_all as u64
                );
                add_distr!(
                    df,
                    "virtual_leg_count_by_agent",
                    virtual_results.count_distribution
                );
                add_distr!(
                    df,
                    "virtual_leg_departure_time",
                    virtual_results.departure_time
                );
                add_distr!(df, "virtual_leg_arrival_time", virtual_results.arrival_time);
                add_distr!(df, "virtual_leg_travel_time", virtual_results.travel_time);
                add_distr!(
                    df,
                    "virtual_leg_global_free_flow_travel_time",
                    virtual_results.global_free_flow_travel_time
                );
                add_distr!(
                    df,
                    "virtual_leg_global_congestion",
                    virtual_results.global_congestion
                );
                add_distr!(df, "virtual_leg_utility", virtual_results.utility);
            } else {
                add_null_virtual_leg_columns!(df);
            }
        } else {
            add_null_const!(df, "trip_count", PolarsDataType::UInt64);
            add_null_distr!(df, "trip_departure_time");
            add_null_distr!(df, "trip_arrival_time");
            add_null_distr!(df, "trip_travel_time");
            add_null_distr!(df, "trip_utility");
            add_null_distr!(df, "trip_expected_utility");
            add_null_road_leg_columns!(df);
            add_null_virtual_leg_columns!(df);
        }
        if let Some(cst_results) = self.mode_results.constant {
            add_const!(df, "constant_count", cst_results.count as u64);
            add_distr!(df, "constant_utility", cst_results.utility);
        } else {
            add_null_const!(df, "constant_count", PolarsDataType::UInt64);
            add_null_distr!(df, "constant_utility");
        }
        if let Some(rmse) = self.sim_road_network_weights_rmse {
            add_const!(df, "sim_road_network_weights_rmse", rmse.to_f64().unwrap());
        } else {
            add_null_distr!(df, "sim_road_network_weights_rmse");
        }
        if let Some(rmse) = self.exp_road_network_weights_rmse {
            add_const!(df, "exp_road_network_weights_rmse", rmse.to_f64().unwrap());
        } else {
            add_null_distr!(df, "exp_road_network_weights_rmse");
        }
        Ok(df)
    }
    fn schema() -> Schema {
        let mut schema = Schema::with_capacity(256);
        add_cst_to_schema!(schema, "iteration_counter", PolarsDataType::UInt32);
        add_distr_to_schema!(schema, "surplus");
        add_cst_to_schema!(schema, "trip_count", PolarsDataType::UInt64);
        add_distr_to_schema!(schema, "trip_departure_time");
        add_distr_to_schema!(schema, "trip_arrival_time");
        add_distr_to_schema!(schema, "trip_travel_time");
        add_distr_to_schema!(schema, "trip_utility");
        add_distr_to_schema!(schema, "trip_expected_utility");
        add_distr_to_schema!(schema, "trip_dep_time_shift");
        add_cst_to_schema!(schema, "trip_dep_time_rmse", PolarsDataType::Float64);
        add_cst_to_schema!(schema, "road_leg_count", PolarsDataType::UInt64);
        add_cst_to_schema!(
            schema,
            "nb_agents_at_least_one_road_leg",
            PolarsDataType::UInt64
        );
        add_cst_to_schema!(schema, "nb_agents_all_road_legs", PolarsDataType::UInt64);
        add_distr_to_schema!(schema, "road_leg_count_by_agent");
        add_distr_to_schema!(schema, "road_leg_departure_time");
        add_distr_to_schema!(schema, "road_leg_arrival_time");
        add_distr_to_schema!(schema, "road_leg_road_time");
        add_distr_to_schema!(schema, "road_leg_in_bottleneck_time");
        add_distr_to_schema!(schema, "road_leg_out_bottleneck_time");
        add_distr_to_schema!(schema, "road_leg_travel_time");
        add_distr_to_schema!(schema, "road_leg_route_free_flow_travel_time");
        add_distr_to_schema!(schema, "road_leg_global_free_flow_travel_time");
        add_distr_to_schema!(schema, "road_leg_route_congestion");
        add_distr_to_schema!(schema, "road_leg_global_congestion");
        add_distr_to_schema!(schema, "road_leg_length");
        add_distr_to_schema!(schema, "road_leg_edge_count");
        add_distr_to_schema!(schema, "road_leg_utility");
        add_distr_to_schema!(schema, "road_leg_exp_travel_time");
        add_distr_to_schema!(schema, "road_leg_exp_travel_time_rel_diff");
        add_distr_to_schema!(schema, "road_leg_exp_travel_time_abs_diff");
        add_cst_to_schema!(
            schema,
            "road_leg_exp_travel_time_diff_rmse",
            PolarsDataType::Float64
        );
        add_distr_to_schema!(schema, "road_leg_length_diff");
        add_cst_to_schema!(schema, "virtual_leg_count", PolarsDataType::UInt64);
        add_cst_to_schema!(
            schema,
            "nb_agents_at_least_one_virtual_leg",
            PolarsDataType::UInt64
        );
        add_cst_to_schema!(schema, "nb_agents_all_virtual_legs", PolarsDataType::UInt64);
        add_distr_to_schema!(schema, "virtual_leg_count_by_agent");
        add_distr_to_schema!(schema, "virtual_leg_departure_time");
        add_distr_to_schema!(schema, "virtual_leg_arrival_time");
        add_distr_to_schema!(schema, "virtual_leg_travel_time");
        add_distr_to_schema!(schema, "virtual_leg_global_free_flow_travel_time");
        add_distr_to_schema!(schema, "virtual_leg_global_congestion");
        add_distr_to_schema!(schema, "virtual_leg_utility");
        add_cst_to_schema!(schema, "constant_count", PolarsDataType::UInt64);
        add_distr_to_schema!(schema, "constant_utility");
        add_cst_to_schema!(
            schema,
            "sim_road_network_weights_rmse",
            PolarsDataType::Float64
        );
        add_cst_to_schema!(
            schema,
            "exp_road_network_weights_rmse",
            PolarsDataType::Float64
        );
        schema
    }
}
