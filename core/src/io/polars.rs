// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Utility functions to work with polars library.

use anyhow::Result;
use num_traits::ToPrimitive;
use polars::prelude::*;
use ttf::TTFNum;

use crate::simulation::results::AggregateResults;

pub trait ToPolars {
    fn to_dataframe(self) -> Result<DataFrame>;
    fn schema() -> ArrowSchema;
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
            &DataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            concat!($name, "_std"),
            1,
            &DataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            concat!($name, "_min"),
            1,
            &DataType::Float64,
        ))?;
        $df.with_column(Series::full_null(
            concat!($name, "_max"),
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
        $fields.push(ArrowField::new(
            concat!($name, "_mean"),
            ArrowDataType::Float64,
            true,
        ));
        $fields.push(ArrowField::new(
            concat!($name, "_std"),
            ArrowDataType::Float64,
            true,
        ));
        $fields.push(ArrowField::new(
            concat!($name, "_min"),
            ArrowDataType::Float64,
            true,
        ));
        $fields.push(ArrowField::new(
            concat!($name, "_max"),
            ArrowDataType::Float64,
            true,
        ));
    };
}

macro_rules! add_cst_to_fields {
    ($fields:ident, $name:expr, $dtype:expr) => {
        $fields.push(ArrowField::new($name, $dtype, true));
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
                add_const!(df, "alt_dep_time_rmse", dep_time_rmse.to_f64().unwrap());
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
                    road_results.exp_travel_time_diff_rmse.to_f64().unwrap()
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
            add_const!(df, "sim_road_network_cond_rmse", rmse.to_f64().unwrap());
        } else {
            add_null_const!(df, "sim_road_network_cond_rmse", DataType::Float64);
        }
        if let Some(rmse) = self.exp_road_network_weights_rmse {
            add_const!(df, "exp_road_network_cond_rmse", rmse.to_f64().unwrap());
        } else {
            add_null_const!(df, "exp_road_network_cond_rmse", DataType::Float64);
        }
        Ok(df)
    }
    fn schema() -> ArrowSchema {
        let mut fields = Vec::with_capacity(256);
        add_cst_to_fields!(fields, "iteration_counter", ArrowDataType::UInt32);
        add_distr_to_fields!(fields, "surplus");
        add_cst_to_fields!(fields, "trip_alt_count", ArrowDataType::UInt64);
        add_distr_to_fields!(fields, "alt_departure_time");
        add_distr_to_fields!(fields, "alt_arrival_time");
        add_distr_to_fields!(fields, "alt_travel_time");
        add_distr_to_fields!(fields, "alt_utility");
        add_distr_to_fields!(fields, "alt_expected_utility");
        add_distr_to_fields!(fields, "alt_dep_time_shift");
        add_cst_to_fields!(fields, "alt_dep_time_rmse", ArrowDataType::Float64);
        add_cst_to_fields!(fields, "road_trip_count", ArrowDataType::UInt64);
        add_cst_to_fields!(
            fields,
            "nb_agents_at_least_one_road_trip",
            ArrowDataType::UInt64
        );
        add_cst_to_fields!(fields, "nb_agents_all_road_trips", ArrowDataType::UInt64);
        add_distr_to_fields!(fields, "road_trip_count_by_agent");
        add_distr_to_fields!(fields, "road_trip_departure_time");
        add_distr_to_fields!(fields, "road_trip_arrival_time");
        add_distr_to_fields!(fields, "road_trip_road_time");
        add_distr_to_fields!(fields, "road_trip_in_bottleneck_time");
        add_distr_to_fields!(fields, "road_trip_out_bottleneck_time");
        add_distr_to_fields!(fields, "road_trip_travel_time");
        add_distr_to_fields!(fields, "road_trip_route_free_flow_travel_time");
        add_distr_to_fields!(fields, "road_trip_global_free_flow_travel_time");
        add_distr_to_fields!(fields, "road_trip_route_congestion");
        add_distr_to_fields!(fields, "road_trip_global_congestion");
        add_distr_to_fields!(fields, "road_trip_length");
        add_distr_to_fields!(fields, "road_trip_edge_count");
        add_distr_to_fields!(fields, "road_trip_utility");
        add_distr_to_fields!(fields, "road_trip_exp_travel_time");
        add_distr_to_fields!(fields, "road_trip_exp_travel_time_rel_diff");
        add_distr_to_fields!(fields, "road_trip_exp_travel_time_abs_diff");
        add_cst_to_fields!(
            fields,
            "road_trip_exp_travel_time_diff_rmse",
            ArrowDataType::Float64
        );
        add_distr_to_fields!(fields, "road_trip_length_diff");
        add_cst_to_fields!(fields, "virtual_trip_count", ArrowDataType::UInt64);
        add_cst_to_fields!(
            fields,
            "nb_agents_at_least_one_virtual_trip",
            ArrowDataType::UInt64
        );
        add_cst_to_fields!(fields, "nb_agents_all_virtual_trips", ArrowDataType::UInt64);
        add_distr_to_fields!(fields, "virtual_trip_count_by_agent");
        add_distr_to_fields!(fields, "virtual_trip_departure_time");
        add_distr_to_fields!(fields, "virtual_trip_arrival_time");
        add_distr_to_fields!(fields, "virtual_trip_travel_time");
        add_distr_to_fields!(fields, "virtual_trip_global_free_flow_travel_time");
        add_distr_to_fields!(fields, "virtual_trip_global_congestion");
        add_distr_to_fields!(fields, "virtual_trip_utility");
        add_cst_to_fields!(fields, "no_trip_alt_count", ArrowDataType::UInt64);
        add_distr_to_fields!(fields, "constant_utility");
        add_cst_to_fields!(fields, "sim_road_network_cond_rmse", ArrowDataType::Float64);
        add_cst_to_fields!(fields, "exp_road_network_cond_rmse", ArrowDataType::Float64);
        ArrowSchema::from(fields)
    }
}
