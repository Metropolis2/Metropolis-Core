// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Imports / exports through parquet format.

use std::{
    fs::File,
    path::{Path, PathBuf},
    sync::Arc,
};

use anyhow::{anyhow, Context, Result};
use arrow::array::RecordBatch;
use parquet::arrow::ArrowWriter;
use parquet::file::properties::WriterProperties;
use parquet::{arrow::arrow_reader::ParquetRecordBatchReaderBuilder, basic::Compression};
use polars::prelude::*;

use super::arrow::ToArrow;
use super::polars::ToPolars;

/// Writes data that can be converted to arrow format as a parquet file.
pub fn write_parquet<D: ToArrow<J>, const J: usize>(data: &D, output_dir: &Path) -> Result<()> {
    write_parquet_with_prefix(data, output_dir, "")
}

/// Writes data that can be converted to arrow format as a parquet file.
///
/// The given prefix is prepended to the names of the saved files.
pub fn write_parquet_with_prefix<D: ToArrow<J>, const J: usize>(
    data: &D,
    output_dir: &Path,
    prefix: &str,
) -> Result<()> {
    let batches = D::to_arrow(data)?;
    for (name, maybe_batch) in D::names().into_iter().zip(batches.into_iter()) {
        if let Some(batch) = maybe_batch {
            let filename: PathBuf = [
                output_dir.to_str().unwrap(),
                &format!("{prefix}{name}.parquet"),
            ]
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

/// Appends data to a parquet file.
///
/// The data is appended as a new row to the existing parquet file.
///
/// If the parquet file does not exist, it is create with a single row.
pub fn append_parquet<D: ToPolars>(data: D, output_dir: &Path, name: &str) -> Result<()> {
    let append_df = data.to_dataframe()?;
    let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.parquet")]
        .iter()
        .collect();
    let mut df = if filename.is_file() {
        let mut file =
            File::open(&filename).with_context(|| format!("Cannot open file `{filename:?}`"))?;
        let mut df = ParquetReader::new(&mut file)
            .with_schema(Some(Arc::new(D::schema())))
            .finish()
            .with_context(|| format!("Cannot read file `{filename:?}`"))?;
        df.vstack_mut(&append_df)
            .context("Cannot append iteration results to DataFrame")?;
        df
    } else {
        append_df
    };
    let mut file =
        File::create(&filename).with_context(|| format!("Cannot create file `{filename:?}`"))?;
    // This line is required to not end up with large filesize.
    df.as_single_chunk_par();
    ParquetWriter::new(&mut file)
        .finish(&mut df)
        .with_context(|| format!("Cannot write file `{filename:?}`"))?;
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
