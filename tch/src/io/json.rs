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

//! Imports / exports through JSON files.

use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::tools::Parameters;

/// Deserializes parameters from JSON files.
pub fn get_parameters_from_json(path: &Path) -> Result<Parameters> {
    read_json(path).context("Failed to read parameters")
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
