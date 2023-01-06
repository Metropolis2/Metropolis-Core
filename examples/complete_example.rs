use anyhow::Result;
use metropolis::run_simulation_from_json_files;
use std::path::PathBuf;

fn main() -> Result<()> {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    dir.push("examples/data");
    run_simulation_from_json_files(
        &[&dir, &PathBuf::from("agents.json")]
            .iter()
            .collect::<PathBuf>(),
        &[&dir, &PathBuf::from("parameters.json")]
            .iter()
            .collect::<PathBuf>(),
        Some(
            &[&dir, &PathBuf::from("road-network.json")]
                .iter()
                .collect::<PathBuf>(),
        ),
        Some(
            &[&dir, &PathBuf::from("weights.json")]
                .iter()
                .collect::<PathBuf>(),
        ),
        &[&dir, &PathBuf::from("output")].iter().collect::<PathBuf>(),
    )
}
