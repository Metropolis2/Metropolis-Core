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

//! Conversion of the results of the simulation to arrow format.

use std::sync::Arc;

use anyhow::Result;
use arrow::array::{
    ArrayRef, BooleanBuilder, Float64Builder, RecordBatch, UInt32Builder, UInt64Builder,
};
use arrow::datatypes::{DataType, Field, FieldRef, Schema};
use metro_io::write::{finish_batch, IdBuilder, ToArrow};
use ttf::TTF;

use crate::mode::trip::results::{LegTypeResults, PreDayLegTypeResults};
use crate::mode::{ModeResults, PreDayModeResults};
use crate::network::NetworkWeights;
use crate::simulation::results::{
    AgentResult, AgentResults, AggregateResults, PreDayAgentResult, PreDayAgentResults,
    SimulationResults,
};
use crate::units::*;

#[derive(Debug, Default)]
struct AgentResultsBuilder {
    // Values at the agent level.
    id: IdBuilder,
    selected_alt_id: IdBuilder,
    expected_utility: Float64Builder,
    shifted_mode: BooleanBuilder,
    departure_time: Float64Builder,
    arrival_time: Float64Builder,
    total_travel_time: Float64Builder,
    utility: Float64Builder,
    mode_expected_utility: Float64Builder,
    departure_time_shift: Float64Builder,
    nb_road_legs: UInt64Builder,
    nb_virtual_legs: UInt64Builder,
    // Values at the leg level.
    leg_agent_id: IdBuilder,
    leg_id: IdBuilder,
    leg_index: UInt64Builder,
    leg_departure_time: Float64Builder,
    leg_arrival_time: Float64Builder,
    leg_travel_utility: Float64Builder,
    leg_schedule_utility: Float64Builder,
    leg_departure_time_shift: Float64Builder,
    leg_road_time: Float64Builder,
    leg_in_bottleneck_time: Float64Builder,
    leg_out_bottleneck_time: Float64Builder,
    leg_route_free_flow_travel_time: Float64Builder,
    leg_global_free_flow_travel_time: Float64Builder,
    leg_length: Float64Builder,
    leg_length_diff: Float64Builder,
    leg_pre_exp_departure_time: Float64Builder,
    leg_pre_exp_arrival_time: Float64Builder,
    leg_exp_arrival_time: Float64Builder,
    leg_nb_edges: UInt64Builder,
    // Values at the route level.
    route_agent_id: IdBuilder,
    route_leg_id: IdBuilder,
    route_leg_index: UInt64Builder,
    route_edge_id: IdBuilder,
    route_entry_time: Float64Builder,
    route_exit_time: Float64Builder,
    route_spillback: BooleanBuilder,
    route_gridlock: BooleanBuilder,
}

impl AgentResultsBuilder {
    fn append(&mut self, agent_result: &AgentResult) {
        self.id.append_value(agent_result.id);
        self.selected_alt_id.append_value(agent_result.mode_id);
        self.expected_utility
            .append_value(Into::<f64>::into(agent_result.expected_utility));
        self.shifted_mode.append_value(agent_result.shifted_mode);
        match &agent_result.mode_results {
            ModeResults::Trip(trip) => {
                self.departure_time
                    .append_value(Into::<f64>::into(trip.departure_time));
                self.arrival_time
                    .append_value(Into::<f64>::into(trip.arrival_time));
                self.total_travel_time
                    .append_value(Into::<f64>::into(trip.total_travel_time));
                self.utility.append_value(Into::<f64>::into(trip.utility));
                self.mode_expected_utility
                    .append_value(Into::<f64>::into(trip.expected_utility));
                if let Some(dts) = trip.departure_time_shift {
                    self.departure_time_shift
                        .append_value(Into::<f64>::into(dts));
                } else {
                    self.departure_time_shift.append_null()
                }
                let mut nb_road_legs = 0;
                let mut nb_virtual_legs = 0;
                for (i, leg) in trip.legs.iter().enumerate() {
                    self.leg_agent_id.append_value(agent_result.id);
                    self.leg_id.append_value(leg.id);
                    self.leg_index.append_value(i as u64);
                    self.leg_departure_time
                        .append_value(Into::<f64>::into(leg.departure_time));
                    self.leg_arrival_time
                        .append_value(Into::<f64>::into(leg.arrival_time));
                    self.leg_travel_utility
                        .append_value(Into::<f64>::into(leg.travel_utility));
                    self.leg_schedule_utility
                        .append_value(Into::<f64>::into(leg.schedule_utility));
                    if let Some(dts) = leg.departure_time_shift {
                        self.leg_departure_time_shift
                            .append_value(Into::<f64>::into(dts));
                    } else {
                        self.leg_departure_time_shift.append_null();
                    }
                    if let LegTypeResults::Road(road_leg) = &leg.class {
                        nb_road_legs += 1;
                        self.leg_road_time
                            .append_value(Into::<f64>::into(road_leg.road_time));
                        self.leg_in_bottleneck_time
                            .append_value(Into::<f64>::into(road_leg.in_bottleneck_time));
                        self.leg_out_bottleneck_time
                            .append_value(Into::<f64>::into(road_leg.out_bottleneck_time));
                        self.leg_route_free_flow_travel_time
                            .append_value(Into::<f64>::into(road_leg.route_free_flow_travel_time));
                        self.leg_global_free_flow_travel_time
                            .append_value(Into::<f64>::into(road_leg.global_free_flow_travel_time));
                        self.leg_length
                            .append_value(Into::<f64>::into(road_leg.length));
                        if let Some(ld) = road_leg.length_diff {
                            self.leg_length_diff.append_value(Into::<f64>::into(ld));
                        } else {
                            self.leg_length_diff.append_null();
                        }
                        self.leg_pre_exp_departure_time
                            .append_value(Into::<f64>::into(road_leg.pre_exp_departure_time));
                        self.leg_pre_exp_arrival_time
                            .append_value(Into::<f64>::into(road_leg.pre_exp_arrival_time));
                        self.leg_exp_arrival_time
                            .append_value(Into::<f64>::into(road_leg.exp_arrival_time));
                        self.leg_nb_edges.append_value(road_leg.route.len() as u64);
                        for window in road_leg.route.windows(2) {
                            let event = &window[0];
                            let next_event = &window[1];
                            self.route_agent_id.append_value(agent_result.id);
                            self.route_leg_id.append_value(leg.id);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(event.edge);
                            self.route_entry_time
                                .append_value(Into::<f64>::into(event.entry_time));
                            self.route_exit_time
                                .append_value(Into::<f64>::into(next_event.entry_time));
                            self.route_spillback
                                .append_value(event.spillback_status.spillback());
                            self.route_gridlock
                                .append_value(event.spillback_status.gridlock());
                        }
                        // The last event is not added by the previous for loop.
                        if let Some(last_event) = road_leg.route.last() {
                            self.route_agent_id.append_value(agent_result.id);
                            self.route_leg_id.append_value(leg.id);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(last_event.edge);
                            self.route_entry_time
                                .append_value(Into::<f64>::into(last_event.entry_time));
                            self.route_exit_time
                                .append_value(Into::<f64>::into(leg.arrival_time));
                            self.route_spillback
                                .append_value(last_event.spillback_status.spillback());
                            self.route_gridlock
                                .append_value(last_event.spillback_status.gridlock());
                        }
                    } else {
                        nb_virtual_legs += 1;
                        self.leg_road_time.append_null();
                        self.leg_in_bottleneck_time.append_null();
                        self.leg_out_bottleneck_time.append_null();
                        self.leg_route_free_flow_travel_time.append_null();
                        self.leg_global_free_flow_travel_time.append_null();
                        self.leg_length.append_null();
                        self.leg_length_diff.append_null();
                        self.leg_pre_exp_departure_time.append_null();
                        self.leg_pre_exp_arrival_time.append_null();
                        self.leg_exp_arrival_time.append_null();
                        self.leg_nb_edges.append_null();
                    }
                }
                self.nb_road_legs.append_value(nb_road_legs);
                self.nb_virtual_legs.append_value(nb_virtual_legs);
            }
            &ModeResults::Constant(utility) => {
                self.departure_time.append_null();
                self.arrival_time.append_null();
                self.total_travel_time.append_null();
                self.utility.append_value(Into::<f64>::into(utility));
                self.mode_expected_utility
                    .append_value(Into::<f64>::into(utility));
                self.departure_time_shift.append_null();
                self.nb_road_legs.append_null();
                self.nb_virtual_legs.append_null();
            }
        }
    }

    fn finish(&mut self) -> Result<[Option<RecordBatch>; 3]> {
        let agent_batch = finish_batch(vec![
            ("agent_id", &mut self.id, false),
            ("selected_alt_id", &mut self.selected_alt_id, false),
            ("expected_utility", &mut self.expected_utility, false),
            ("shifted_alt", &mut self.shifted_mode, false),
            ("departure_time", &mut self.departure_time, true),
            ("arrival_time", &mut self.arrival_time, true),
            ("total_travel_time", &mut self.total_travel_time, true),
            ("utility", &mut self.utility, true),
            (
                "alt_expected_utility",
                &mut self.mode_expected_utility,
                true,
            ),
            ("departure_time_shift", &mut self.departure_time_shift, true),
            ("nb_road_trips", &mut self.nb_road_legs, true),
            ("nb_virtual_trips", &mut self.nb_virtual_legs, true),
        ])?;
        let leg_batch = finish_batch(vec![
            ("agent_id", &mut self.leg_agent_id, false),
            ("trip_id", &mut self.leg_id, false),
            ("trip_index", &mut self.leg_index, false),
            ("departure_time", &mut self.leg_departure_time, false),
            ("arrival_time", &mut self.leg_arrival_time, false),
            ("travel_utility", &mut self.leg_travel_utility, false),
            ("schedule_utility", &mut self.leg_schedule_utility, false),
            (
                "departure_time_shift",
                &mut self.leg_departure_time_shift,
                true,
            ),
            ("road_time", &mut self.leg_road_time, true),
            ("in_bottleneck_time", &mut self.leg_in_bottleneck_time, true),
            (
                "out_bottleneck_time",
                &mut self.leg_out_bottleneck_time,
                true,
            ),
            (
                "route_free_flow_travel_time",
                &mut self.leg_route_free_flow_travel_time,
                true,
            ),
            (
                "global_free_flow_travel_time",
                &mut self.leg_global_free_flow_travel_time,
                true,
            ),
            ("length", &mut self.leg_length, true),
            ("length_diff", &mut self.leg_length_diff, true),
            (
                "pre_exp_departure_time",
                &mut self.leg_pre_exp_departure_time,
                true,
            ),
            (
                "pre_exp_arrival_time",
                &mut self.leg_pre_exp_arrival_time,
                true,
            ),
            ("exp_arrival_time", &mut self.leg_exp_arrival_time, true),
            ("nb_edges", &mut self.leg_nb_edges, true),
        ])?;
        let route_batch = finish_batch(vec![
            ("agent_id", &mut self.route_agent_id, false),
            ("trip_id", &mut self.route_leg_id, false),
            ("trip_index", &mut self.route_leg_index, false),
            ("edge_id", &mut self.route_edge_id, false),
            ("entry_time", &mut self.route_entry_time, false),
            ("exit_time", &mut self.route_exit_time, false),
            ("spillback", &mut self.route_spillback, false),
            ("gridlock", &mut self.route_gridlock, false),
        ])?;
        Ok([agent_batch, leg_batch, route_batch])
    }
}

impl ToArrow<3> for AgentResults {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 3]> {
        let mut builder = AgentResultsBuilder::default();
        self.0.iter().for_each(|row| builder.append(row));
        builder.finish()
    }
    fn names() -> [&'static str; 3] {
        ["agent_results", "trip_results", "route_results"]
    }
}

#[derive(Debug, Default)]
struct PreDayAgentResultsBuilder {
    // Values at the agent level.
    id: IdBuilder,
    selected_alt_id: IdBuilder,
    expected_utility: Float64Builder,
    departure_time: Float64Builder,
    mode_expected_utility: Float64Builder,
    nb_road_legs: UInt64Builder,
    nb_virtual_legs: UInt64Builder,
    // Values at the leg level.
    leg_agent_id: IdBuilder,
    leg_id: IdBuilder,
    leg_index: UInt64Builder,
    leg_route_free_flow_travel_time: Float64Builder,
    leg_global_free_flow_travel_time: Float64Builder,
    leg_length: Float64Builder,
    leg_pre_exp_departure_time: Float64Builder,
    leg_pre_exp_arrival_time: Float64Builder,
    leg_nb_edges: UInt64Builder,
    // Values at the route level.
    route_agent_id: IdBuilder,
    route_leg_id: IdBuilder,
    route_leg_index: UInt64Builder,
    route_edge_id: IdBuilder,
    route_entry_time: Float64Builder,
    route_exit_time: Float64Builder,
}

impl PreDayAgentResultsBuilder {
    fn append(&mut self, agent_result: &PreDayAgentResult) {
        self.id.append_value(agent_result.id);
        self.selected_alt_id.append_value(agent_result.mode_id);
        self.expected_utility
            .append_value(Into::<f64>::into(agent_result.expected_utility));
        match &agent_result.mode_results {
            PreDayModeResults::Trip(trip) => {
                self.departure_time
                    .append_value(Into::<f64>::into(trip.departure_time));
                self.mode_expected_utility
                    .append_value(Into::<f64>::into(trip.expected_utility));
                let mut nb_road_legs = 0;
                let mut nb_virtual_legs = 0;
                for (i, leg) in trip.legs.iter().enumerate() {
                    self.leg_agent_id.append_value(agent_result.id);
                    self.leg_id.append_value(leg.id);
                    self.leg_index.append_value(i as u64);
                    if let PreDayLegTypeResults::Road(road_leg) = &leg.class {
                        nb_road_legs += 1;
                        self.leg_route_free_flow_travel_time
                            .append_value(Into::<f64>::into(road_leg.route_free_flow_travel_time));
                        self.leg_global_free_flow_travel_time
                            .append_value(Into::<f64>::into(road_leg.global_free_flow_travel_time));
                        self.leg_length
                            .append_value(Into::<f64>::into(road_leg.length));
                        self.leg_pre_exp_departure_time
                            .append_value(Into::<f64>::into(road_leg.pre_exp_departure_time));
                        self.leg_pre_exp_arrival_time
                            .append_value(Into::<f64>::into(road_leg.pre_exp_arrival_time));
                        self.leg_nb_edges.append_value(road_leg.route.len() as u64);
                        for window in road_leg.route.windows(2) {
                            let event = &window[0];
                            let next_event = &window[1];
                            self.route_agent_id.append_value(agent_result.id);
                            self.route_leg_id.append_value(leg.id);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(event.edge);
                            self.route_entry_time
                                .append_value(Into::<f64>::into(event.entry_time));
                            self.route_exit_time
                                .append_value(Into::<f64>::into(next_event.entry_time));
                        }
                        // The last event is not added by the previous for loop.
                        if let Some(last_event) = road_leg.route.last() {
                            self.route_agent_id.append_value(agent_result.id);
                            self.route_leg_id.append_value(leg.id);
                            self.route_leg_index.append_value(i as u64);
                            self.route_edge_id.append_value(last_event.edge);
                            self.route_entry_time
                                .append_value(Into::<f64>::into(last_event.entry_time));
                            self.route_exit_time
                                .append_value(Into::<f64>::into(road_leg.pre_exp_arrival_time));
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
            }
            &PreDayModeResults::Constant(utility) => {
                self.departure_time.append_null();
                self.mode_expected_utility
                    .append_value(Into::<f64>::into(utility));
                self.nb_road_legs.append_null();
                self.nb_virtual_legs.append_null();
            }
        }
    }

    fn finish(&mut self) -> Result<[Option<RecordBatch>; 3]> {
        let agent_batch = finish_batch(vec![
            ("agent_id", &mut self.id, false),
            ("selected_alt_id", &mut self.selected_alt_id, false),
            ("expected_utility", &mut self.expected_utility, false),
            ("departure_time", &mut self.departure_time, true),
            (
                "alt_expected_utility",
                &mut self.mode_expected_utility,
                true,
            ),
            ("nb_road_trips", &mut self.nb_road_legs, true),
            ("nb_virtual_trips", &mut self.nb_virtual_legs, true),
        ])?;
        let leg_batch = finish_batch(vec![
            ("agent_id", &mut self.leg_agent_id, false),
            ("trip_id", &mut self.leg_id, false),
            ("trip_index", &mut self.leg_index, false),
            (
                "route_free_flow_travel_time",
                &mut self.leg_route_free_flow_travel_time,
                true,
            ),
            (
                "global_free_flow_travel_time",
                &mut self.leg_global_free_flow_travel_time,
                true,
            ),
            ("length", &mut self.leg_length, true),
            (
                "pre_exp_departure_time",
                &mut self.leg_pre_exp_departure_time,
                true,
            ),
            (
                "pre_exp_arrival_time",
                &mut self.leg_pre_exp_arrival_time,
                true,
            ),
            ("nb_edges", &mut self.leg_nb_edges, true),
        ])?;
        let route_batch = finish_batch(vec![
            ("agent_id", &mut self.route_agent_id, false),
            ("trip_id", &mut self.route_leg_id, false),
            ("trip_index", &mut self.route_leg_index, false),
            ("edge_id", &mut self.route_edge_id, false),
            ("entry_time", &mut self.route_entry_time, false),
            ("exit_time", &mut self.route_exit_time, false),
        ])?;
        Ok([agent_batch, leg_batch, route_batch])
    }
}

impl ToArrow<3> for PreDayAgentResults {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 3]> {
        let mut builder = PreDayAgentResultsBuilder::default();
        self.0.iter().for_each(|row| builder.append(row));
        builder.finish()
    }
    fn names() -> [&'static str; 3] {
        ["agent_results", "trip_results", "route_results"]
    }
}

#[derive(Debug)]
struct RoadNetworkWeightsBuilder {
    period: Interval,
    interval: PositiveSeconds,
    vehicle_id: IdBuilder,
    edge_id: IdBuilder,
    departure_time: Float64Builder,
    travel_time: Float64Builder,
}

impl RoadNetworkWeightsBuilder {
    fn new(period: Interval, interval: PositiveSeconds) -> Self {
        Self {
            period,
            interval,
            vehicle_id: Default::default(),
            edge_id: Default::default(),
            departure_time: Default::default(),
            travel_time: Default::default(),
        }
    }
}

impl RoadNetworkWeightsBuilder {
    fn append(&mut self, vehicle_id: MetroId, edge_id: MetroId, ttf: &TTF<AnySeconds>) {
        let xs_iter = std::iter::successors(Some(self.period.start()), |&t| {
            Some(t + NonNegativeSeconds::from(self.interval))
        })
        .take_while(|&t| t <= self.period.end());
        for (x, y) in xs_iter.map(|x| (x, ttf.eval(AnySeconds::from(x)))) {
            self.vehicle_id.append_value(vehicle_id);
            self.edge_id.append_value(edge_id);
            self.departure_time.append_value(Into::<f64>::into(x));
            self.travel_time.append_value(Into::<f64>::into(y));
        }
    }

    fn finish(&mut self) -> Result<[Option<RecordBatch>; 1]> {
        Ok([finish_batch(vec![
            ("vehicle_id", &mut self.vehicle_id, false),
            ("edge_id", &mut self.edge_id, false),
            ("departure_time", &mut self.departure_time, false),
            ("travel_time", &mut self.travel_time, true),
        ])?])
    }
}

impl ToArrow<1> for NetworkWeights {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 1]> {
        if let Some(rn_weights) = self.road_network() {
            let mut builder = RoadNetworkWeightsBuilder::new(
                crate::parameters::period(),
                crate::network::road_network::parameters::recording_interval(),
            );
            for vehicle_weights in rn_weights.iter() {
                // NOTE: The weights are stored in a hash map, whose iteration order can vary from
                // one run to another, so we sort them by edge index to get reproducible output.
                let mut weights: Vec<_> = vehicle_weights.weights().iter().collect();
                weights.sort_unstable_by_key(|(edge_id, _)| {
                    crate::network::road_network::edge_index_of(**edge_id)
                });
                for vehicle_id in vehicle_weights.vehicle_ids() {
                    for (edge_id, ttf) in weights.iter() {
                        builder.append(*vehicle_id, **edge_id, ttf);
                    }
                }
            }
            builder.finish()
        } else {
            Ok([None])
        }
    }
    fn names() -> [&'static str; 1] {
        ["edge_ttfs"]
    }
}

/// A typed arrow builder for one column of the `iteration_results` table.
#[derive(Debug)]
enum ColumnBuilder {
    UInt32(UInt32Builder),
    UInt64(UInt64Builder),
    Float64(Float64Builder),
}

impl ColumnBuilder {
    /// Returns the values appended so far as an arrow array.
    fn finish(&mut self) -> ArrayRef {
        match self {
            Self::UInt32(builder) => Arc::new(builder.finish()),
            Self::UInt64(builder) => Arc::new(builder.finish()),
            Self::Float64(builder) => Arc::new(builder.finish()),
        }
    }
}

/// Builder of the `iteration_results` table, with one row per iteration.
///
/// The schema is not declared up-front: it is discovered while the first row is appended and the
/// following rows must then push the exact same columns, in the same order (this is checked with
/// debug assertions). This way, the column list only exists once, so the values and the schema
/// cannot drift apart.
#[derive(Debug, Default)]
struct AggregateResultsBuilder {
    /// Schema of the table, built while the first row is appended.
    fields: Vec<FieldRef>,
    /// One builder per column of the table.
    columns: Vec<ColumnBuilder>,
    /// Index of the column being pushed, reset at the beginning of each row.
    cursor: usize,
}

/// Generates a `push_*` method appending an optional value to the next column of the current row.
macro_rules! push_column {
    ($name:ident, $ty:ty, $variant:ident, $dtype:expr) => {
        fn $name(&mut self, name: &str, value: Option<$ty>) {
            if self.cursor == self.fields.len() {
                // First row: this column is discovered now.
                self.fields.push(Arc::new(Field::new(name, $dtype, true)));
                self.columns
                    .push(ColumnBuilder::$variant(Default::default()));
            }
            debug_assert_eq!(
                self.fields[self.cursor].name(),
                name,
                "Column `{name}` is not pushed at the same position in every row"
            );
            match &mut self.columns[self.cursor] {
                ColumnBuilder::$variant(builder) => builder.append_option(value),
                builder => unreachable!("Column `{name}` has unexpected builder {builder:?}"),
            }
            self.cursor += 1;
        }
    };
}

impl AggregateResultsBuilder {
    push_column!(push_u32, u32, UInt32, DataType::UInt32);
    push_column!(push_u64, u64, UInt64, DataType::UInt64);
    push_column!(push_f64, f64, Float64, DataType::Float64);

    /// Appends the four `_mean`, `_std`, `_min` and `_max` columns of a distribution.
    ///
    /// The four columns are null if the distribution is `None`.
    fn push_distr<T: MetroNonNegativeNum + Into<f64>>(
        &mut self,
        name: &str,
        distr: Option<&Distribution<T>>,
    ) {
        self.push_f64(&format!("{name}_mean"), distr.map(|d| d.mean().into()));
        self.push_f64(&format!("{name}_std"), distr.map(|d| d.std().into()));
        self.push_f64(&format!("{name}_min"), distr.map(|d| d.min().into()));
        self.push_f64(&format!("{name}_max"), distr.map(|d| d.max().into()));
    }

    /// Appends the results of one iteration as a new row.
    fn append(&mut self, results: &AggregateResults) {
        self.cursor = 0;
        self.push_u32("iteration_counter", Some(results.iteration_counter));
        self.push_distr("surplus", Some(&results.surplus));

        let trip = results.mode_results.trip_modes.as_ref();
        self.push_u64("trip_alt_count", trip.map(|t| t.count as u64));
        self.push_distr("alt_departure_time", trip.map(|t| &t.departure_time));
        self.push_distr("alt_arrival_time", trip.map(|t| &t.arrival_time));
        self.push_distr("alt_travel_time", trip.map(|t| &t.travel_time));
        self.push_distr("alt_utility", trip.map(|t| &t.utility));
        self.push_distr("alt_expected_utility", trip.map(|t| &t.expected_utility));
        self.push_distr(
            "alt_dep_time_shift",
            trip.and_then(|t| t.dep_time_shift.as_ref()),
        );
        self.push_f64(
            "alt_dep_time_rmse",
            trip.and_then(|t| t.dep_time_rmse).map(Into::into),
        );

        let road = trip.and_then(|t| t.road_leg.as_ref());
        self.push_u64("road_trip_count", road.map(|r| r.count as u64));
        self.push_u64(
            "nb_agents_at_least_one_road_trip",
            road.map(|r| r.mode_count_one as u64),
        );
        self.push_u64(
            "nb_agents_all_road_trips",
            road.map(|r| r.mode_count_all as u64),
        );
        self.push_distr(
            "road_trip_count_by_agent",
            road.map(|r| &r.count_distribution),
        );
        self.push_distr("road_trip_departure_time", road.map(|r| &r.departure_time));
        self.push_distr("road_trip_arrival_time", road.map(|r| &r.arrival_time));
        self.push_distr("road_trip_road_time", road.map(|r| &r.road_time));
        self.push_distr(
            "road_trip_in_bottleneck_time",
            road.map(|r| &r.in_bottleneck_time),
        );
        self.push_distr(
            "road_trip_out_bottleneck_time",
            road.map(|r| &r.out_bottleneck_time),
        );
        self.push_distr("road_trip_travel_time", road.map(|r| &r.travel_time));
        self.push_distr(
            "road_trip_route_free_flow_travel_time",
            road.map(|r| &r.route_free_flow_travel_time),
        );
        self.push_distr(
            "road_trip_global_free_flow_travel_time",
            road.map(|r| &r.global_free_flow_travel_time),
        );
        self.push_distr(
            "road_trip_route_congestion",
            road.map(|r| &r.route_congestion),
        );
        self.push_distr(
            "road_trip_global_congestion",
            road.map(|r| &r.global_congestion),
        );
        self.push_distr("road_trip_length", road.map(|r| &r.length));
        self.push_distr("road_trip_edge_count", road.map(|r| &r.edge_count));
        self.push_distr("road_trip_utility", road.map(|r| &r.utility));
        self.push_distr(
            "road_trip_exp_travel_time",
            road.map(|r| &r.exp_travel_time),
        );
        self.push_distr(
            "road_trip_exp_travel_time_rel_diff",
            road.map(|r| &r.exp_travel_time_rel_diff),
        );
        self.push_distr(
            "road_trip_exp_travel_time_abs_diff",
            road.map(|r| &r.exp_travel_time_abs_diff),
        );
        self.push_f64(
            "road_trip_exp_travel_time_diff_rmse",
            road.map(|r| r.exp_travel_time_diff_rmse.into()),
        );
        self.push_distr(
            "road_trip_length_diff",
            road.and_then(|r| r.length_diff.as_ref()),
        );

        let virt = trip.and_then(|t| t.virtual_leg.as_ref());
        self.push_u64("virtual_trip_count", virt.map(|v| v.count as u64));
        self.push_u64(
            "nb_agents_at_least_one_virtual_trip",
            virt.map(|v| v.mode_count_one as u64),
        );
        self.push_u64(
            "nb_agents_all_virtual_trips",
            virt.map(|v| v.mode_count_all as u64),
        );
        self.push_distr(
            "virtual_trip_count_by_agent",
            virt.map(|v| &v.count_distribution),
        );
        self.push_distr(
            "virtual_trip_departure_time",
            virt.map(|v| &v.departure_time),
        );
        self.push_distr("virtual_trip_arrival_time", virt.map(|v| &v.arrival_time));
        self.push_distr("virtual_trip_travel_time", virt.map(|v| &v.travel_time));
        self.push_distr(
            "virtual_trip_global_free_flow_travel_time",
            virt.map(|v| &v.global_free_flow_travel_time),
        );
        self.push_distr(
            "virtual_trip_global_congestion",
            virt.map(|v| &v.global_congestion),
        );
        self.push_distr("virtual_trip_utility", virt.map(|v| &v.utility));

        let constant = results.mode_results.constant.as_ref();
        self.push_u64("no_trip_alt_count", constant.map(|c| c.count as u64));
        self.push_distr("constant_utility", constant.map(|c| &c.utility));

        self.push_f64(
            "sim_road_network_cond_rmse",
            results.sim_road_network_weights_rmse.map(Into::into),
        );
        self.push_f64(
            "exp_road_network_cond_rmse",
            results.exp_road_network_weights_rmse.map(Into::into),
        );

        debug_assert_eq!(
            self.cursor,
            self.fields.len(),
            "Not all the columns were pushed for this row"
        );
    }

    /// Returns the appended rows as a [RecordBatch].
    fn finish(&mut self) -> Result<[Option<RecordBatch>; 1]> {
        if self.fields.is_empty() {
            return Ok([None]);
        }
        let schema = Arc::new(Schema::new(std::mem::take(&mut self.fields)));
        let columns: Vec<ArrayRef> = self.columns.iter_mut().map(ColumnBuilder::finish).collect();
        let batch = RecordBatch::try_new(schema, columns)?;
        if batch.num_rows() == 0 {
            Ok([None])
        } else {
            Ok([Some(batch)])
        }
    }
}

impl ToArrow<1> for SimulationResults {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 1]> {
        let mut builder = AggregateResultsBuilder::default();
        for results in self.iterations.iter() {
            builder.append(results);
        }
        builder.finish()
    }
    fn names() -> [&'static str; 1] {
        ["iteration_results"]
    }
}
