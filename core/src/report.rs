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
use crate::units::{Interval, NonNegativeSeconds};

const NB_BINS: usize = 128;

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
        road_departure_times.sort_unstable();
        road_arrival_times.sort_unstable();

        let last_iteration = if road_departure_times.is_empty() {
            IterationStatistics::default()
        } else {
            let departure_time_histogram =
                get_histogram(road_departure_times, crate::parameters::period());
            let arrival_time_histogram =
                get_histogram(road_arrival_times, crate::parameters::period());
            IterationStatistics {
                departure_time_histogram,
                arrival_time_histogram,
            }
        };
        Ok(ReportResults {
            iterations: results.iterations.clone(),
            last_iteration,
        })
    } else {
        Err(anyhow!("Cannot build report without last iteration"))
    }
}

#[derive(Debug, Default)]
struct Histogram {
    bars: Vec<usize>,
    period: Interval,
}

/// Statistics computed from the [SimulationResults].
#[derive(Debug, Default)]
struct IterationStatistics {
    departure_time_histogram: Histogram,
    arrival_time_histogram: Histogram,
}

/// Results used to build the HTML report of a simulation.
#[derive(Debug, Template)]
#[template(path = "report.html", whitespace = "suppress")]
struct ReportResults {
    pub(crate) iterations: Vec<AggregateResults>,
    pub(crate) last_iteration: IterationStatistics,
}

fn get_histogram(values: Vec<NonNegativeSeconds>, min_period: Interval) -> Histogram {
    debug_assert!(!values.is_empty());
    // debug_assert!(values.is_sorted());
    let mut bars = Vec::with_capacity(NB_BINS);
    let period = Interval::new(
        min_period.start().min(values[0]),
        min_period.end().max(values[values.len() - 1]),
    );
    let interval = period.length() / NB_BINS;
    let mut t = period.start();
    let mut n = 0;
    for (i, v) in values.iter().enumerate() {
        while v > &(t + interval).into() {
            bars.push(i - n);
            n = i;
            t += interval;
        }
    }
    bars.push(values.len() - n);
    if bars.len() < NB_BINS {
        bars.extend(std::iter::repeat(0).take(NB_BINS - bars.len()));
    }
    Histogram { bars, period }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn histogram_test() {
        let values = vec![
            NonNegativeSeconds::try_from(3.0).unwrap(),
            NonNegativeSeconds::try_from(5.0).unwrap(),
            NonNegativeSeconds::try_from(5.1).unwrap(),
            NonNegativeSeconds::try_from(5.2).unwrap(),
            NonNegativeSeconds::try_from(9.0).unwrap(),
            NonNegativeSeconds::try_from(12.0).unwrap(),
            NonNegativeSeconds::try_from(15.0).unwrap(),
        ];
        let period = Interval::try_from([0.0, 2.0 * NB_BINS as f64]).unwrap();
        let mut exp_bars = vec![0, 1, 3, 0, 1, 1, 0, 1];
        exp_bars.append(&mut vec![0; NB_BINS - exp_bars.len()]);
        let histogram = get_histogram(values, period);
        assert_eq!(exp_bars, histogram.bars);
        assert_eq!(period, histogram.period);
    }
}
