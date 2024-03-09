use std::path::PathBuf;

use anyhow::{Context, Result};
use metropolis::run_simulation;

fn main() -> Result<()> {
    let wd = env!("CARGO_MANIFEST_DIR");
    let p: PathBuf = [wd, "examples/data/csv/parameters.json"].iter().collect();
    run_simulation(&p).context("Failed to run simulaton from CSV input")
}

#[test]
fn csv_example_test() -> Result<()> {
    main()
}
