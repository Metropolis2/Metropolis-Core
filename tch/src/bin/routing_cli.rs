// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Binary to compute earliest-arrival or profile queries from input files.
use std::path::{Path, PathBuf};

use anyhow::Result;
#[cfg(feature = "expire")]
use chrono::{Local, NaiveDate};
use clap::Parser;
use tch::tools::run_queries;

/// Compute earliest-arrival or profile queries using time-dependent Contraction Hierarchies
#[derive(Parser, Debug)]
#[command(author, version, about, long_about)]
struct Args {
    /// Path to the JSON file with the parameters
    #[arg(required = true)]
    parameters: PathBuf,
}

fn main() -> Result<()> {
    check_expiry_date();
    let args = Args::parse();
    compute_travel_times(&args.parameters)
}

fn compute_travel_times(path: &Path) -> Result<()> {
    run_queries(path)
}

#[cfg(feature = "expire")]
fn check_expiry_date() {
    let expiration_date = NaiveDate::from_ymd_opt(2025, 12, 31).unwrap();
    let today = Local::now().date_naive();
    if today > expiration_date {
        eprintln!("This program has expired. Please contact the developer.");
        std::process::exit(1);
    }
}

#[cfg(not(feature = "expire"))]
fn check_expiry_date() {}
