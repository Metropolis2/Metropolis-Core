use std::path::PathBuf;

use anyhow::Result;
use metropolis::run_simulation;

fn main() -> Result<()> {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    dir.push("examples/data");
    run_simulation(
        &[&dir, &PathBuf::from("parameters.json")]
            .iter()
            .collect::<PathBuf>(),
    )
}

#[test]
fn complete_example_test() {
    main().unwrap();
}
