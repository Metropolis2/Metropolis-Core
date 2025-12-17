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

//! Imports / exports through parquet format.

use std::{
    fs::File,
    io::Seek,
    path::{Path, PathBuf},
    sync::Arc,
};

use anyhow::{anyhow, Context, Result};
use arrow::{
    array::RecordBatch,
    csv::{reader::Format, ReaderBuilder, Writer},
};

use super::arrow::ToArrow;

/// Write data that can be converted to arrow format as a CSV file.
pub fn write_csv<D: ToArrow<J>, const J: usize>(data: &D, output_dir: &Path) -> Result<()> {
    let batches = D::to_arrow(data, true)?;
    for (name, maybe_batch) in D::names().into_iter().zip(batches.into_iter()) {
        if let Some(batch) = maybe_batch {
            let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.csv")]
                .iter()
                .collect();
            let file = File::create(filename)?;
            let mut writer = Writer::new(file);
            writer.write(&batch)?;
        }
    }
    Ok(())
}

pub(crate) fn get_batch_record(filename: &Path) -> Result<RecordBatch> {
    let mut file =
        File::open(filename).with_context(|| format!("Cannot open file `{filename:?}`"))?;
    let (schema, nb_rows) = Format::default()
        .with_header(true)
        .infer_schema(&mut file, None)
        .with_context(|| format!("Cannot infer schema from file `{filename:?}`"))?;
    file.rewind()?;
    let mut reader = ReaderBuilder::new(Arc::new(schema))
        .with_batch_size(nb_rows)
        .with_header(true)
        .build(file)
        .with_context(|| format!("Cannot read file `{filename:?}`"))?;
    reader
        .next()
        .ok_or_else(|| anyhow!("No data to read from `{filename:?}`"))?
        .with_context(|| format!("Cannot read arrow data from `{filename:?}`"))
}
