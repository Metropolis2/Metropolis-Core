//! Example running a simulation from Parquet files.
use std::path::PathBuf;

use anyhow::{Context, Result};
use metropolis_core::run_simulation;

fn main() -> Result<()> {
    let wd = env!("CARGO_MANIFEST_DIR");
    let p: PathBuf = [wd, "examples/data/parquet/parameters.json"]
        .iter()
        .collect();
    run_simulation(&p).context("Failed to run simulation from Parquet input")
}

#[test]
fn parquet_example_test() -> Result<()> {
    main()
}
