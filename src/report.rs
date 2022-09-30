// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! HTML report with the results of a simulation.
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Result};
use askama::Template;
use ttf::TTFNum;

use crate::mode::ModeResults;
use crate::simulation::results::{AggregateResults, SimulationResults};
use crate::units::Time;

/// Writes a HTML report of the given [SimulationResults].
///
/// The report is written in file `report.html` in the given output directory.
pub fn write_report<T: TTFNum>(results: &SimulationResults<T>, output_dir: &Path) -> Result<()> {
    let report_results = build_report(results)?;
    let filename: PathBuf = [output_dir.to_str().unwrap(), "report.html"]
        .iter()
        .collect();
    let mut file = File::create(&filename)?;
    file.write_all(report_results.render().unwrap().as_bytes())?;
    Ok(())
}

/// Returns a [ReportResults] given the [SimulationResults].
fn build_report<T: TTFNum>(results: &SimulationResults<T>) -> Result<ReportResults<T>> {
    if let Some(last_iteration) = &results.last_iteration {
        let mut road_departure_times = Vec::with_capacity(last_iteration.agent_results().len());
        for (_, agent_result) in last_iteration.iter_agent_results() {
            if let ModeResults::Road(_) = agent_result.mode_results() {
                road_departure_times.push(agent_result.departure_time().unwrap());
            }
        }

        let last_iteration = IterationStatistics {
            road_departure_times,
        };
        Ok(ReportResults {
            iterations: results.iterations.clone(),
            last_iteration,
        })
    } else {
        Err(anyhow!("Cannot build report without last iteration"))
    }
}

/// Statistics computed from the [SimulationResults].
struct IterationStatistics<T> {
    /// Vec with the departure time of each agent.
    road_departure_times: Vec<Time<T>>,
}

/// Results used to build the HTML report of a simulation.
#[derive(Template)]
#[template(path = "report.html")]
struct ReportResults<T: TTFNum> {
    pub(crate) iterations: Vec<AggregateResults<T>>,
    pub(crate) last_iteration: IterationStatistics<T>,
}
