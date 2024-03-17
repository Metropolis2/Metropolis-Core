//! Example running a simulation from CSV files.
use std::path::PathBuf;

use anyhow::{Context, Result};
use tch::run_queries;

fn main() -> Result<()> {
    let wd = env!("CARGO_MANIFEST_DIR");
    let p: PathBuf = [wd, "examples/data/csv/parameters.json"].iter().collect();
    run_queries(&p).context("Failed to run routing queries from CSV input")
}

#[test]
fn csv_example_test() -> Result<()> {
    main()
}
