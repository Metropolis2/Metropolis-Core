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

//! Utility functions to work with polars library.

use anyhow::Result;
use polars::datatypes::PlSmallStr;
use polars::prelude::*;

use crate::simulation::results::AggregateResults;

pub trait ToPolars {
    fn to_dataframe(self) -> Result<DataFrame>;
    fn schema() -> Schema;
}

macro_rules! add_const {
    ($df:ident, $name:expr, $const:expr) => {
        $df.with_column(Series::new(PlSmallStr::from_str($name), &[$const]))?;
    };
}

macro_rules! add_null_const {
    ($df:ident, $name:expr, $type:expr) => {
        $df.with_column(Series::full_null(PlSmallStr::from_str($name), 1, &$type))?;
    };
}

macro_rules! add_distr {
    ($df:ident, $name:expr, $var:expr) => {
        $df.with_column(Series::new(
            PlSmallStr::from_str(concat!($name, "_mean")),
            &[Into::<f64>::into($var.mean())],
        ))?;
        $df.with_column(Series::new(
            PlSmallStr::from_str(concat!($name, "_std")),
            &[Into::<f64>::into($var.std())],
        ))?;
        $df.with_column(Series::new(
            PlSmallStr::from_str(concat!($name, "_min")),
            &[Into::<f64>::into($var.min())],
        ))?;
        $df.with_column(Series::new(
            PlSmallStr::from_str(concat!($name, "_max")),
            &[Into::<f64>::into($var.max())],
        ))?;
    };
}

macro_rules! add_null_distr {
    ($df:ident, $name:expr) => {
        $df.with_column(Series::full_null(
            PlSmallStr::from_str(concat!($name, "_mean")),
            1,
            &DataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            PlSmallStr::from_str(concat!($name, "_std")),
            1,
            &DataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            PlSmallStr::from_str(concat!($name, "_min")),
            1,
            &DataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            PlSmallStr::from_str(concat!($name, "_max")),
            1,
            &DataType::Float64,
        ))?;
    };
}

macro_rules! add_null_road_leg_columns {
    ($df:ident) => {
        add_null_const!($df, "road_trip_count", DataType::UInt64);
        add_null_const!($df, "nb_agents_at_least_one_road_trip", DataType::UInt64);
        add_null_const!($df, "nb_agents_all_road_trips", DataType::UInt64);
        add_null_distr!($df, "road_trip_count_by_agent");
        add_null_distr!($df, "road_trip_departure_time");
        add_null_distr!($df, "road_trip_arrival_time");
        add_null_distr!($df, "road_trip_road_time");
        add_null_distr!($df, "road_trip_in_bottleneck_time");
        add_null_distr!($df, "road_trip_out_bottleneck_time");
        add_null_distr!($df, "road_trip_travel_time");
        add_null_distr!($df, "road_trip_route_free_flow_travel_time");
        add_null_distr!($df, "road_trip_global_free_flow_travel_time");
        add_null_distr!($df, "road_trip_route_congestion");
        add_null_distr!($df, "road_trip_global_congestion");
        add_null_distr!($df, "road_trip_length");
        add_null_distr!($df, "road_trip_edge_count");
        add_null_distr!($df, "road_trip_utility");
        add_null_distr!($df, "road_trip_exp_travel_time");
        add_null_distr!($df, "road_trip_exp_travel_time_rel_diff");
        add_null_distr!($df, "road_trip_exp_travel_time_abs_diff");
        add_null_const!(
            $df,
            "road_trip_exp_travel_time_diff_rmse",
            DataType::Float64
        );
        add_null_distr!($df, "road_trip_length_diff");
    };
}

macro_rules! add_null_virtual_leg_columns {
    ($df:ident) => {
        add_null_const!($df, "virtual_trip_count", DataType::UInt64);
        add_null_const!($df, "nb_agents_at_least_one_virtual_trip", DataType::UInt64);
        add_null_const!($df, "nb_agents_all_virtual_trips", DataType::UInt64);
        add_null_distr!($df, "virtual_trip_count_by_agent");
        add_null_distr!($df, "virtual_trip_departure_time");
        add_null_distr!($df, "virtual_trip_arrival_time");
        add_null_distr!($df, "virtual_trip_travel_time");
        add_null_distr!($df, "virtual_trip_global_free_flow_travel_time");
        add_null_distr!($df, "virtual_trip_global_congestion");
        add_null_distr!($df, "virtual_trip_utility");
    };
}

macro_rules! add_distr_to_fields {
    ($fields:ident, $name:expr) => {
        $fields.insert(
            PlSmallStr::from_str(concat!($name, "_mean")),
            DataType::Float64,
        );
        $fields.insert(
            PlSmallStr::from_str(concat!($name, "_std")),
            DataType::Float64,
        );
        $fields.insert(
            PlSmallStr::from_str(concat!($name, "_min")),
            DataType::Float64,
        );
        $fields.insert(
            PlSmallStr::from_str(concat!($name, "_max")),
            DataType::Float64,
        );
    };
}

macro_rules! add_cst_to_fields {
    ($fields:ident, $name:expr, $dtype:expr) => {
        $fields.insert(PlSmallStr::from_str($name), $dtype);
    };
}

impl ToPolars for AggregateResults {
    fn to_dataframe(self) -> Result<DataFrame> {
        let mut df = DataFrame::new(vec![Column::new(
            "iteration_counter".into(),
            &[self.iteration_counter],
        )])?;
        add_distr!(df, "surplus", self.surplus);
        if let Some(trip_results) = self.mode_results.trip_modes {
            add_const!(df, "trip_alt_count", trip_results.count as u64);
            add_distr!(df, "alt_departure_time", trip_results.departure_time);
            add_distr!(df, "alt_arrival_time", trip_results.arrival_time);
            add_distr!(df, "alt_travel_time", trip_results.travel_time);
            add_distr!(df, "alt_utility", trip_results.utility);
            add_distr!(df, "alt_expected_utility", trip_results.expected_utility);
            if let Some(dep_time_shift) = trip_results.dep_time_shift {
                add_distr!(df, "alt_dep_time_shift", dep_time_shift);
            } else {
                add_null_distr!(df, "alt_dep_time_shift");
            }
            if let Some(dep_time_rmse) = trip_results.dep_time_rmse {
                add_const!(df, "alt_dep_time_rmse", Into::<f64>::into(dep_time_rmse));
            } else {
                add_null_const!(df, "alt_dep_time_rmse", DataType::Float64);
            }
            if let Some(road_results) = trip_results.road_leg {
                add_const!(df, "road_trip_count", road_results.count as u64);
                add_const!(
                    df,
                    "nb_agents_at_least_one_road_trip",
                    road_results.mode_count_one as u64
                );
                add_const!(
                    df,
                    "nb_agents_all_road_trips",
                    road_results.mode_count_all as u64
                );
                add_distr!(
                    df,
                    "road_trip_count_by_agent",
                    road_results.count_distribution
                );
                add_distr!(df, "road_trip_departure_time", road_results.departure_time);
                add_distr!(df, "road_trip_arrival_time", road_results.arrival_time);
                add_distr!(df, "road_trip_road_time", road_results.road_time);
                add_distr!(
                    df,
                    "road_trip_in_bottleneck_time",
                    road_results.in_bottleneck_time
                );
                add_distr!(
                    df,
                    "road_trip_out_bottleneck_time",
                    road_results.out_bottleneck_time
                );
                add_distr!(df, "road_trip_travel_time", road_results.travel_time);
                add_distr!(
                    df,
                    "road_trip_route_free_flow_travel_time",
                    road_results.route_free_flow_travel_time
                );
                add_distr!(
                    df,
                    "road_trip_global_free_flow_travel_time",
                    road_results.global_free_flow_travel_time
                );
                add_distr!(
                    df,
                    "road_trip_route_congestion",
                    road_results.route_congestion
                );
                add_distr!(
                    df,
                    "road_trip_global_congestion",
                    road_results.global_congestion
                );
                add_distr!(df, "road_trip_length", road_results.length);
                add_distr!(df, "road_trip_edge_count", road_results.edge_count);
                add_distr!(df, "road_trip_utility", road_results.utility);
                add_distr!(
                    df,
                    "road_trip_exp_travel_time",
                    road_results.exp_travel_time
                );
                add_distr!(
                    df,
                    "road_trip_exp_travel_time_rel_diff",
                    road_results.exp_travel_time_rel_diff
                );
                add_distr!(
                    df,
                    "road_trip_exp_travel_time_abs_diff",
                    road_results.exp_travel_time_abs_diff
                );
                add_const!(
                    df,
                    "road_trip_exp_travel_time_diff_rmse",
                    Into::<f64>::into(road_results.exp_travel_time_diff_rmse)
                );
                if let Some(length_diff) = road_results.length_diff {
                    add_distr!(df, "road_trip_length_diff", length_diff);
                } else {
                    add_null_distr!(df, "road_trip_length_diff");
                }
            } else {
                add_null_road_leg_columns!(df);
            }
            if let Some(virtual_results) = trip_results.virtual_leg {
                add_const!(df, "virtual_trip_count", virtual_results.count as u64);
                add_const!(
                    df,
                    "nb_agents_at_least_one_virtual_trip",
                    virtual_results.mode_count_one as u64
                );
                add_const!(
                    df,
                    "nb_agents_all_virtual_trips",
                    virtual_results.mode_count_all as u64
                );
                add_distr!(
                    df,
                    "virtual_trip_count_by_agent",
                    virtual_results.count_distribution
                );
                add_distr!(
                    df,
                    "virtual_trip_departure_time",
                    virtual_results.departure_time
                );
                add_distr!(
                    df,
                    "virtual_trip_arrival_time",
                    virtual_results.arrival_time
                );
                add_distr!(df, "virtual_trip_travel_time", virtual_results.travel_time);
                add_distr!(
                    df,
                    "virtual_trip_global_free_flow_travel_time",
                    virtual_results.global_free_flow_travel_time
                );
                add_distr!(
                    df,
                    "virtual_trip_global_congestion",
                    virtual_results.global_congestion
                );
                add_distr!(df, "virtual_trip_utility", virtual_results.utility);
            } else {
                add_null_virtual_leg_columns!(df);
            }
        } else {
            add_null_const!(df, "trip_alt_count", DataType::UInt64);
            add_null_distr!(df, "alt_departure_time");
            add_null_distr!(df, "alt_arrival_time");
            add_null_distr!(df, "alt_travel_time");
            add_null_distr!(df, "alt_utility");
            add_null_distr!(df, "alt_expected_utility");
            add_null_road_leg_columns!(df);
            add_null_virtual_leg_columns!(df);
        }
        if let Some(cst_results) = self.mode_results.constant {
            add_const!(df, "no_trip_alt_count", cst_results.count as u64);
            add_distr!(df, "constant_utility", cst_results.utility);
        } else {
            add_null_const!(df, "no_trip_alt_count", DataType::UInt64);
            add_null_distr!(df, "constant_utility");
        }
        if let Some(rmse) = self.sim_road_network_weights_rmse {
            add_const!(df, "sim_road_network_cond_rmse", Into::<f64>::into(rmse));
        } else {
            add_null_const!(df, "sim_road_network_cond_rmse", DataType::Float64);
        }
        if let Some(rmse) = self.exp_road_network_weights_rmse {
            add_const!(df, "exp_road_network_cond_rmse", Into::<f64>::into(rmse));
        } else {
            add_null_const!(df, "exp_road_network_cond_rmse", DataType::Float64);
        }
        Ok(df)
    }
    fn schema() -> Schema {
        let mut schema = Schema::with_capacity(256);
        add_cst_to_fields!(schema, "iteration_counter", DataType::UInt32);
        add_distr_to_fields!(schema, "surplus");
        add_cst_to_fields!(schema, "trip_alt_count", DataType::UInt64);
        add_distr_to_fields!(schema, "alt_departure_time");
        add_distr_to_fields!(schema, "alt_arrival_time");
        add_distr_to_fields!(schema, "alt_travel_time");
        add_distr_to_fields!(schema, "alt_utility");
        add_distr_to_fields!(schema, "alt_expected_utility");
        add_distr_to_fields!(schema, "alt_dep_time_shift");
        add_cst_to_fields!(schema, "alt_dep_time_rmse", DataType::Float64);
        add_cst_to_fields!(schema, "road_trip_count", DataType::UInt64);
        add_cst_to_fields!(schema, "nb_agents_at_least_one_road_trip", DataType::UInt64);
        add_cst_to_fields!(schema, "nb_agents_all_road_trips", DataType::UInt64);
        add_distr_to_fields!(schema, "road_trip_count_by_agent");
        add_distr_to_fields!(schema, "road_trip_departure_time");
        add_distr_to_fields!(schema, "road_trip_arrival_time");
        add_distr_to_fields!(schema, "road_trip_road_time");
        add_distr_to_fields!(schema, "road_trip_in_bottleneck_time");
        add_distr_to_fields!(schema, "road_trip_out_bottleneck_time");
        add_distr_to_fields!(schema, "road_trip_travel_time");
        add_distr_to_fields!(schema, "road_trip_route_free_flow_travel_time");
        add_distr_to_fields!(schema, "road_trip_global_free_flow_travel_time");
        add_distr_to_fields!(schema, "road_trip_route_congestion");
        add_distr_to_fields!(schema, "road_trip_global_congestion");
        add_distr_to_fields!(schema, "road_trip_length");
        add_distr_to_fields!(schema, "road_trip_edge_count");
        add_distr_to_fields!(schema, "road_trip_utility");
        add_distr_to_fields!(schema, "road_trip_exp_travel_time");
        add_distr_to_fields!(schema, "road_trip_exp_travel_time_rel_diff");
        add_distr_to_fields!(schema, "road_trip_exp_travel_time_abs_diff");
        add_cst_to_fields!(
            schema,
            "road_trip_exp_travel_time_diff_rmse",
            DataType::Float64
        );
        add_distr_to_fields!(schema, "road_trip_length_diff");
        add_cst_to_fields!(schema, "virtual_trip_count", DataType::UInt64);
        add_cst_to_fields!(
            schema,
            "nb_agents_at_least_one_virtual_trip",
            DataType::UInt64
        );
        add_cst_to_fields!(schema, "nb_agents_all_virtual_trips", DataType::UInt64);
        add_distr_to_fields!(schema, "virtual_trip_count_by_agent");
        add_distr_to_fields!(schema, "virtual_trip_departure_time");
        add_distr_to_fields!(schema, "virtual_trip_arrival_time");
        add_distr_to_fields!(schema, "virtual_trip_travel_time");
        add_distr_to_fields!(schema, "virtual_trip_global_free_flow_travel_time");
        add_distr_to_fields!(schema, "virtual_trip_global_congestion");
        add_distr_to_fields!(schema, "virtual_trip_utility");
        add_cst_to_fields!(schema, "no_trip_alt_count", DataType::UInt64);
        add_distr_to_fields!(schema, "constant_utility");
        add_cst_to_fields!(schema, "sim_road_network_cond_rmse", DataType::Float64);
        add_cst_to_fields!(schema, "exp_road_network_cond_rmse", DataType::Float64);
        schema
    }
}
