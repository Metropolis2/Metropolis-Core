// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Utility functions to work with arrow format.

use std::sync::Arc;

use anyhow::Result;
use arrow::array::{Float64Builder, UInt64Builder};
use arrow::datatypes::{DataType, Field, Schema};
use arrow::record_batch::RecordBatch;
use num_traits::ToPrimitive;

use crate::mode::trip::results::{LegTypeResults, PreDayLegTypeResults};
use crate::mode::{ModeResults, PreDayModeResults};
use crate::simulation::results::{
    AgentResult, AgentResults, PreDayAgentResult, PreDayAgentResults,
};

pub trait ToArrow<const J: usize> {
    fn to_arrow(data: Self) -> Result<[RecordBatch; J]>;
    fn names<'a>() -> [&'a str; J];
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
        let agent_schema = Schema::new(vec![
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
        let leg_schema = Schema::new(vec![
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
        let route_schema = Schema::new(vec![
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
        let agent_schema = Schema::new(vec![
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
        let leg_schema = Schema::new(vec![
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
        let route_schema = Schema::new(vec![
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
