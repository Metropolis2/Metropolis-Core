use std::path::PathBuf;

use anyhow::{Context, Result};
use metropolis::run_simulation;

fn main() -> Result<()> {
    let wd = env!("CARGO_MANIFEST_DIR");
    let p: PathBuf = [wd, "examples/data/unnested_parquet/parameters.json"]
        .iter()
        .collect();
    run_simulation(&p).context("Failed to run simulaton from Unnested Parquet input")
}

#[test]
fn unnested_parquet_example_test() -> Result<()> {
    main()
}
