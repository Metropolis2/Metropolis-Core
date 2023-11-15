// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Imports / exports through parquet format.

use std::{
    fs::File,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use parquet::{arrow::ArrowWriter, basic::Compression, file::properties::WriterProperties};
use polars::prelude::*;

use super::arrow::{ToArrow, ToPolars};

/// Write data that can be converted to arrow format as a parquet file.
pub fn write_parquet<D: ToArrow<J>, const J: usize>(data: D, output_dir: &Path) -> Result<()> {
    let batches = D::to_arrow(data)?;
    for (name, batch) in D::names().into_iter().zip(batches.into_iter()) {
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
    Ok(())
}

/// Append data to a parquet file.
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
