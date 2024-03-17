//! Example running a simulation from Parquet files.
use std::path::PathBuf;

use anyhow::{Context, Result};
use tch::run_queries;

fn main() -> Result<()> {
    let wd = env!("CARGO_MANIFEST_DIR");
    let p: PathBuf = [wd, "examples/data/parquet/parameters.json"]
        .iter()
        .collect();
    run_queries(&p).context("Failed to run routing queries from Parquet input")
}

#[test]
fn parquet_example_test() -> Result<()> {
    main()
}
