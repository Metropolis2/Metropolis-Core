// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Binary to run Metropolis simulation from a set of input files.
use std::path::PathBuf;

use anyhow::Result;
#[cfg(feature = "expire")]
use chrono::{Local, NaiveDate};
use clap::Parser;
#[cfg(not(target_env = "msvc"))]
use tikv_jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

/// METROPOLIS2 simulator.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Path to the JSON file with the parameters
    #[arg(required = true)]
    parameters: PathBuf,
}

fn main() -> Result<()> {
    check_expiry_date();
    let args = Args::parse();
    metropolis_core::run_simulation(&args.parameters)
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
