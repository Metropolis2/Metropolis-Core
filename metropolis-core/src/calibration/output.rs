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
use metro_io::write::{finish_batch, write_csv, write_parquet, IdBuilder, ToArrow};
use serde_derive::Serialize;

use super::CalibrationResults;
use crate::parameters::SavingFormat;

/// Saves the results of the capacity calibration in the output directory:
///
/// - `calibrated_capacities.json`: the calibrated capacities, in the format of the `capacities`
///   parameter of the calibration (in PCE per second per lane);
/// - `calibration_iterations.[ext]`: the diagnostics of each outer iteration;
/// - `calibration_delays.[ext]`: the target and predicted delays of each target route.
pub(super) fn save(results: &CalibrationResults) -> Result<()> {
    let output_dir = crate::parameters::output_directory();
    write_json(
        capacities_json(results),
        output_dir,
        "calibrated_capacities",
    )?;
    match crate::parameters::saving_format() {
        SavingFormat::Parquet => write_parquet(results, output_dir),
        SavingFormat::CSV => write_csv(results, output_dir),
    }
}

/// Calibrated capacities in the format of the `capacities` parameter of the calibration, in PCE
/// per second per lane.
#[derive(Serialize)]
#[serde(untagged)]
enum CapacitiesJson {
    /// A single capacity, when no edge has a category.
    Uniform(f64),
    /// The capacity of each category, by category id.
    ByCategory(BTreeMap<String, f64>),
}

/// Returns the calibrated capacities in the format of the `capacities` parameter of the
/// calibration.
fn capacities_json(results: &CalibrationResults) -> CapacitiesJson {
    match results.capacities.as_slice() {
        [(None, capacity)] => CapacitiesJson::Uniform(f64::from(*capacity)),
        capacities => CapacitiesJson::ByCategory(
            capacities
                .iter()
                .map(|(id, capacity)| {
                    let id = id.expect("Categories have an id when there are several of them");
                    (id.to_string(), f64::from(*capacity))
                })
                .collect(),
        ),
    }
}

impl ToArrow<2> for CalibrationResults {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 2]> {
        Ok([self.iterations_batch()?, self.delays_batch()?])
    }
    fn names() -> [&'static str; 2] {
        ["calibration_iterations", "calibration_delays"]
    }
}

impl CalibrationResults {
    /// Returns the table of the diagnostics of the outer iterations.
    fn iterations_batch(&self) -> Result<Option<RecordBatch>> {
        let mut outer = UInt64Builder::new();
        let mut nb_days = UInt64Builder::new();
        let mut first_rmse = Float64Builder::new();
        let mut last_rmse = Float64Builder::new();
        let mut first_gap = Float64Builder::new();
        let mut last_gap = Float64Builder::new();
        let mut nb_equilibrium_days = UInt64Builder::new();
        let mut score = Float64Builder::new();
        let mut score_noise = Float64Builder::new();
        let mut nb_optimizations = UInt64Builder::new();
        let mut capacities: Vec<_> = self
            .category_ids
            .iter()
            .map(|_| Float64Builder::new())
            .collect();
        for it in self.iterations.iter() {
            outer.append_value(it.outer);
            nb_days.append_value(it.conditions_rmse.len() as u64);
            first_rmse.append_option(it.conditions_rmse.first().map(|&r| f64::from(r)));
            last_rmse.append_option(it.conditions_rmse.last().map(|&r| f64::from(r)));
            first_gap.append_option(it.travel_time_gaps.first().copied().flatten());
            last_gap.append_option(it.travel_time_gaps.last().copied().flatten());
            nb_equilibrium_days.append_value(it.nb_equilibrium_days);
            score.append_value(f64::from(it.score));
            score_noise.append_option(it.score_noise.map(f64::from));
            nb_optimizations.append_value(it.nb_optimizations);
            for (builder, &capacity) in capacities.iter_mut().zip(it.capacities.iter()) {
                builder.append_value(f64::from(capacity));
            }
        }
        let capacity_names: Vec<String> = self
            .category_ids
            .iter()
            .map(|id| id.map_or_else(|| "capacity".to_owned(), |id| format!("capacity_{id}")))
            .collect();
        let mut columns: Vec<(&str, &mut dyn ArrayBuilder, bool)> = vec![
            ("outer", &mut outer, false),
            ("nb_route_choice_days", &mut nb_days, false),
            ("first_day_conditions_rmse", &mut first_rmse, false),
            ("last_day_conditions_rmse", &mut last_rmse, false),
            ("first_day_travel_time_gap", &mut first_gap, true),
            ("last_day_travel_time_gap", &mut last_gap, true),
            ("nb_equilibrium_days", &mut nb_equilibrium_days, false),
            ("score", &mut score, false),
            ("score_noise", &mut score_noise, true),
            ("nb_optimizations", &mut nb_optimizations, false),
        ];
        for (name, builder) in capacity_names.iter().zip(capacities.iter_mut()) {
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
