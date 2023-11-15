// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Imports / exports through JSON files.

use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use log::info;
use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::{
    network::{road_network::RoadNetwork, Network},
    simulation::Simulation,
};

/// Deserializes a simulation from JSON files.
pub fn get_simulation_from_json_files(
    agents: &Path,
    parameters: &Path,
    road_network: Option<&Path>,
) -> Result<Simulation<f64>> {
    // Read input files.
    info!("Reading input files");
    let agents = read_json(agents)?;
    let parameters = read_json(parameters)?;
    let road_network: Option<RoadNetwork<f64>> = if let Some(rn) = road_network {
        Some(read_json(rn)?)
    } else {
        None
    };
    let network = Network::new(road_network);
    Ok(Simulation::new(agents, network, parameters))
}

/// Read some deserializable data from an uncompressed or a zstd-compressed JSON file.
pub fn read_json<D: DeserializeOwned>(filename: &Path) -> Result<D> {
    let mut bytes = Vec::new();
    File::open(filename)
        .with_context(|| format!("Unable to open file `{filename:?}`"))?
        .read_to_end(&mut bytes)
        .with_context(|| format!("Unable to read file `{filename:?}`"))?;
    let decoded_bytes = if filename.extension().and_then(|s| s.to_str()) == Some("zst") {
        zstd::decode_all(bytes.as_slice())
            .with_context(|| format!("Unable to decode zstd-compressed file `{filename:?}`"))?
    } else {
        bytes
    };
    let data = serde_json::from_slice(&decoded_bytes)
        .with_context(|| format!("Unable to parse file `{filename:?}`"))?;
    Ok(data)
}

/// Write some serializable data as an uncompressed JSON file.
///
/// The file is stored in the given directory, with filename "{name}.json".
pub fn write_json<D: Serialize>(data: D, output_dir: &Path, name: &str) -> Result<()> {
    let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.json")]
        .iter()
        .collect();
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&data)?;
    writer.write_all(&buffer)?;
    Ok(())
}

/// Write some serializable data as a Zstd compressed JSON file.
///
/// The file is stored in the given directory, with filename "{name}.json.zst".
pub fn write_compressed_json<D: Serialize>(data: D, output_dir: &Path, name: &str) -> Result<()> {
    let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.json.zst")]
        .iter()
        .collect();
    let mut writer = File::create(filename)?;
    let buffer = serde_json::to_vec(&data)?;
    let encoded_buffer = zstd::encode_all(buffer.as_slice(), 0)?;
    writer.write_all(&encoded_buffer)?;
    Ok(())
}

/// Append some serializable data to a JSON file.
///
/// The JSON file must contain a list of the data type `D`.
///
/// If the JSON does not exist, the file is created, with the data to append in a list.
pub fn append_json<D: Serialize + DeserializeOwned>(
    to_append: D,
    output_dir: &Path,
    name: &str,
) -> Result<()> {
    let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.json")]
        .iter()
        .collect();
    let mut data: Vec<D> = if filename.is_file() {
        read_json(&filename)?
    } else {
        vec![]
    };
    data.push(to_append);
    write_json(data, output_dir, name)?;
    Ok(())
}
