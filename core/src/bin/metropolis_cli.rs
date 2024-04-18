// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Binary to run Metropolis simulation from a set of input files.
use std::path::PathBuf;

use anyhow::Result;
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
    let args = Args::parse();
    metropolis_core::run_simulation(&args.parameters)
}
