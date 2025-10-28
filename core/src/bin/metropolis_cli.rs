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

//! Binary to run a Metropolis-Core simulation from a set of input files.
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

/// Metropolis-Core: the Rust-based core of the METROPOLIS2 simulator.
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
