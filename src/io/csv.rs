// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Imports / exports through parquet format.

use std::{
    fs::File,
    io::Seek,
    path::{Path, PathBuf},
};

use anyhow::{anyhow, Context, Result};
use arrow::{
    array::RecordBatch,
    csv::{reader::Format, ReaderBuilder, Writer},
};
use polars::prelude::*;

use super::arrow::ToArrow;
use super::polars::ToPolars;

/// Write data that can be converted to arrow format as a CSV file.
pub fn write_csv<D: ToArrow<J>, const J: usize>(data: D, output_dir: &Path) -> Result<()> {
    write_csv_with_prefix(data, output_dir, "")
}

/// Write data that can be converted to arrow format as a CSV file.
///
/// The given prefix is prepended to the names of the saved files.
pub fn write_csv_with_prefix<D: ToArrow<J>, const J: usize>(
    data: D,
    output_dir: &Path,
    prefix: &str,
) -> Result<()> {
    let batches = D::to_arrow(data)?;
    for (name, maybe_batch) in D::names().into_iter().zip(batches.into_iter()) {
        if let Some(batch) = maybe_batch {
            let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{prefix}{name}.csv")]
                .iter()
                .collect();
            let file = File::create(filename)?;
            let mut writer = Writer::new(file);
            writer.write(&batch)?;
        }
    }
    Ok(())
}

/// Append data to a CSV file.
///
/// The data is appended as a new row to the existing CSV file.
///
/// If the CSV file does not exist, it is create with a single row.
pub fn append_csv<D: ToPolars>(data: D, output_dir: &Path, name: &str) -> Result<()> {
    let append_df = data.to_dataframe()?;
    let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.csv")]
        .iter()
        .collect();
    let mut df = if filename.is_file() {
        let mut file =
            File::open(&filename).with_context(|| format!("Cannot open file `{filename:?}`"))?;
        let mut df = CsvReader::new(&mut file)
            .with_schema(Some(Arc::new(Schema::from(D::schema()))))
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
    CsvWriter::new(&mut file)
        .finish(&mut df)
        .with_context(|| format!("Cannot write file `{filename:?}`"))?;
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
