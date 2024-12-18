// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Imports / exports through parquet format.

use std::path::PathBuf;
use std::{fs::File, path::Path};

use anyhow::{anyhow, Context, Result};
use arrow::array::RecordBatch;
use parquet::arrow::ArrowWriter;
use parquet::file::properties::WriterProperties;
use parquet::{arrow::arrow_reader::ParquetRecordBatchReaderBuilder, basic::Compression};

use super::arrow::ToArrow;

/// Writes data that can be converted to arrow format as a parquet file.
pub fn write_parquet<D: ToArrow<J>, const J: usize>(data: &D, output_dir: &Path) -> Result<()> {
    let batches = D::to_arrow(data, false)?;
    for (name, maybe_batch) in D::names().into_iter().zip(batches.into_iter()) {
        if let Some(batch) = maybe_batch {
            let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.parquet")]
                .iter()
                .collect();
            let file = File::create(&filename)
                .with_context(|| format!("Cannot create file `{filename:?}`"))?;
            let props = WriterProperties::builder()
                .set_compression(Compression::SNAPPY)
                .build();
            let mut writer = ArrowWriter::try_new(file, batch.schema(), Some(props))
                .with_context(|| format!("Cannot create writer for file `{filename:?}`"))?;
            writer
                .write(&batch)
                .with_context(|| format!("Cannot write batch to file `{filename:?}`"))?;
            writer
                .close()
                .with_context(|| format!("Cannot close file after writing `{filename:?}`"))?;
        }
    }
    Ok(())
}

pub(crate) fn get_batch_record(filename: &Path) -> Result<RecordBatch> {
    let file = File::open(filename).with_context(|| format!("Cannot open file `{filename:?}`"))?;
    let builder = ParquetRecordBatchReaderBuilder::try_new(file)
        .with_context(|| format!("Cannot read file `{filename:?}`"))?;
    let mut reader = builder
        .with_batch_size(usize::MAX)
        .build()
        .with_context(|| format!("Cannot decode file `{filename:?}`"))?;
    reader
        .next()
        .ok_or_else(|| anyhow!("No data to read from `{filename:?}`"))?
        .with_context(|| format!("Cannot read arrow data from `{filename:?}`"))
}
