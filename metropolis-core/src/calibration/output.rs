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

//! Output files of the road-capacity calibration.
use std::collections::BTreeMap;

use anyhow::Result;
use arrow::array::{ArrayBuilder, Float64Builder, RecordBatch, UInt64Builder};
use metro_io::json::write_json;
use metro_io::write::{
    finish_batch, write_csv, write_csv_with_prefix, write_parquet, write_parquet_with_prefix,
    IdBuilder, ToArrow,
};
use serde_derive::Serialize;

use super::CalibrationResults;
use crate::parameters::SavingFormat;
use crate::units::{FlowPerLane, MetroId};

/// Saves the results of the capacity calibration in the output directory:
///
/// - `calibrated_factors.json`: the capacity and the calibrated factors, in the format of the
///   `capacity` and `factors` parameters of the calibration;
/// - `next_factors.json`: the capacity and the factors optimized after the last day, in the same
///   format;
/// - `net_cond_next_exp_edge_ttfs.[ext]`: the expected network conditions of the next day, in the
///   format of the `road_network_conditions` input file.
///
/// The last two files allow to resume the calibration (see [super::calibrate]).
/// - `calibrated_edges.[ext]`: the calibrated capacity per lane and bottleneck flow of each edge
///   with factors;
/// - `calibration_days.[ext]`: the diagnostics of each simulated day;
/// - `calibration_delays.[ext]`: the target and predicted delays of each target route.
pub(super) fn save(results: &CalibrationResults) -> Result<()> {
    let output_dir = crate::parameters::output_directory();
    write_json(
        factors_json(results.capacity, &results.factors),
        output_dir,
        "calibrated_factors",
    )?;
    write_json(
        factors_json(results.capacity, &results.next_factors),
        output_dir,
        "next_factors",
    )?;
    match crate::parameters::saving_format() {
        SavingFormat::Parquet => {
            write_parquet(results, output_dir)?;
            write_parquet_with_prefix(&results.next_exp_weights, output_dir, "net_cond_next_exp_")
        }
        SavingFormat::CSV => {
            write_csv(results, output_dir)?;
            write_csv_with_prefix(&results.next_exp_weights, output_dir, "net_cond_next_exp_")
        }
    }
}

/// Capacity and factors in the format of the `capacity` and `factors` parameters of the
/// calibration.
#[derive(Serialize)]
struct FactorsJson {
    /// Capacity per lane of an edge whose factors are all equal to 1, in PCE per second per lane.
    capacity: f64,
    /// Value of each factor, by factor id.
    factors: BTreeMap<String, f64>,
}

/// Returns the capacity and the value of each factor in the format of the `capacity` and `factors`
/// parameters of the calibration.
fn factors_json(capacity: FlowPerLane, factors: &[(MetroId, f64)]) -> FactorsJson {
    FactorsJson {
        capacity: f64::from(capacity),
        factors: factors
            .iter()
            .map(|(id, value)| (id.to_string(), *value))
            .collect(),
    }
}

impl ToArrow<3> for CalibrationResults {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 3]> {
        Ok([
            self.edges_batch()?,
            self.days_batch()?,
            self.delays_batch()?,
        ])
    }
    fn names() -> [&'static str; 3] {
        ["calibrated_edges", "calibration_days", "calibration_delays"]
    }
}

impl CalibrationResults {
    /// Returns the table of the calibrated capacities of the edges with factors.
    fn edges_batch(&self) -> Result<Option<RecordBatch>> {
        let mut edge_id = IdBuilder::default();
        let mut capacity = Float64Builder::new();
        let mut bottleneck_flow = Float64Builder::new();
        for &(id, c, flow) in self.edge_capacities.iter() {
            edge_id.append_value(id);
            capacity.append_value(f64::from(c));
            bottleneck_flow.append_value(f64::from(flow));
        }
        finish_batch(vec![
            ("edge_id", &mut edge_id, false),
            ("capacity", &mut capacity, false),
            ("bottleneck_flow", &mut bottleneck_flow, false),
        ])
    }

    /// Returns the table of the diagnostics of the simulated days.
    fn days_batch(&self) -> Result<Option<RecordBatch>> {
        let mut day = UInt64Builder::new();
        let mut iteration_counter = UInt64Builder::new();
        let mut conditions_rmse = Float64Builder::new();
        let mut travel_time_gap = Float64Builder::new();
        let mut learning_weight = Float64Builder::new();
        let mut trust_region = Float64Builder::new();
        let mut nb_surrogate_days = UInt64Builder::new();
        let mut score = Float64Builder::new();
        let mut score_noise = Float64Builder::new();
        let mut factors: Vec<_> = self.factors.iter().map(|_| Float64Builder::new()).collect();
        for d in self.days.iter() {
            day.append_value(d.day);
            iteration_counter.append_value(d.iteration_counter as u64);
            conditions_rmse.append_value(f64::from(d.conditions_rmse));
            travel_time_gap.append_option(d.travel_time_gap);
            learning_weight.append_value(d.learning_weight);
            trust_region.append_value(d.trust_region);
            nb_surrogate_days.append_value(d.nb_surrogate_days);
            score.append_option(d.score.map(f64::from));
            score_noise.append_option(d.score_noise.map(f64::from));
            for (builder, &value) in factors.iter_mut().zip(d.factors.iter()) {
                builder.append_value(value);
            }
        }
        let factor_names: Vec<String> = self
            .factors
            .iter()
            .map(|(id, _)| format!("factor_{id}"))
            .collect();
        let mut columns: Vec<(&str, &mut dyn ArrayBuilder, bool)> = vec![
            ("day", &mut day, false),
            ("iteration_counter", &mut iteration_counter, false),
            ("conditions_rmse", &mut conditions_rmse, false),
            ("travel_time_gap", &mut travel_time_gap, true),
            ("learning_weight", &mut learning_weight, false),
            ("trust_region", &mut trust_region, false),
            ("nb_surrogate_days", &mut nb_surrogate_days, false),
            ("score", &mut score, true),
            ("score_noise", &mut score_noise, true),
        ];
        for (name, builder) in factor_names.iter().zip(factors.iter_mut()) {
            columns.push((name, builder, false));
        }
        finish_batch(columns)
    }

    /// Returns the table of the target and predicted delays of the target routes.
    fn delays_batch(&self) -> Result<Option<RecordBatch>> {
        let mut id = IdBuilder::default();
        let mut departure_time = Float64Builder::new();
        let mut target_delay = Float64Builder::new();
        let mut initial_predicted_delay = Float64Builder::new();
        let mut predicted_delay = Float64Builder::new();
        for delay in self.delays.iter() {
            id.append_value(delay.id);
            departure_time.append_value(f64::from(delay.departure_time));
            target_delay.append_value(f64::from(delay.target_delay));
            initial_predicted_delay.append_value(f64::from(delay.initial_predicted_delay));
            predicted_delay.append_value(f64::from(delay.predicted_delay));
        }
        finish_batch(vec![
            ("id", &mut id, false),
            ("departure_time", &mut departure_time, false),
            ("target_delay", &mut target_delay, false),
            (
                "initial_predicted_delay",
                &mut initial_predicted_delay,
                false,
            ),
            ("predicted_delay", &mut predicted_delay, false),
        ])
    }
}
