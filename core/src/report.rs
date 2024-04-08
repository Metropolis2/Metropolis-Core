// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! HTML report with the results of a simulation.
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use anyhow::{anyhow, Result};
use askama::Template;

use crate::mode::trip::results::LegTypeResults;
use crate::mode::ModeResults;
use crate::simulation::results::{AggregateResults, SimulationResults};
use crate::units::NonNegativeSeconds;

/// Writes a HTML report of the given [SimulationResults].
///
/// The report is written in file `report.html` in the given output directory.
pub(crate) fn write_report(results: &SimulationResults) -> Result<()> {
    let report_results = build_report(results)?;
    let filename: PathBuf = [
        crate::parameters::output_directory().to_str().unwrap(),
        "report.html",
    ]
    .iter()
    .collect();
    let mut file = File::create(filename)?;
    let render = report_results.render()?;
    file.write_all(render.as_bytes())?;
    Ok(())
}

/// Returns a [ReportResults] given the [SimulationResults].
fn build_report(results: &SimulationResults) -> Result<ReportResults> {
    if let Some(last_iteration) = &results.last_iteration {
        let mut road_departure_times = Vec::with_capacity(last_iteration.agent_results().len());
        let mut road_arrival_times = Vec::with_capacity(last_iteration.agent_results().len());
        for (_, agent_result) in last_iteration.iter_agent_results() {
            if let ModeResults::Trip(trip_results) = &agent_result.mode_results {
                for leg_result in trip_results.legs.iter() {
                    if let LegTypeResults::Road(_) = &leg_result.class {
                        road_departure_times.push(leg_result.departure_time);
                        road_arrival_times.push(leg_result.arrival_time);
                    }
                }
            }
        }

        let last_iteration = IterationStatistics {
            road_departure_times,
            road_arrival_times,
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
#[derive(Debug)]
struct IterationStatistics {
    /// Vec with the departure time of each agent.
    road_departure_times: Vec<NonNegativeSeconds>,
    /// Vec with the arrival time of each agent.
    road_arrival_times: Vec<NonNegativeSeconds>,
}

/// Results used to build the HTML report of a simulation.
#[derive(Debug, Template)]
#[template(path = "report.html")]
struct ReportResults {
    pub(crate) iterations: Vec<AggregateResults>,
    pub(crate) last_iteration: IterationStatistics,
}
