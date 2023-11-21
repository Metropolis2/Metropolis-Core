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
use arrow::csv::Writer;
use polars::prelude::*;

use super::arrow::ToArrow;
use super::polars::ToPolars;

/// Write data that can be converted to arrow format as a CSV file.
pub fn write_csv<D: ToArrow<J>, const J: usize>(data: D, output_dir: &Path) -> Result<()> {
    let batches = D::to_arrow(data)?;
    for (name, batch) in D::names().into_iter().zip(batches.into_iter()) {
        let filename: PathBuf = [output_dir.to_str().unwrap(), &format!("{name}.csv")]
            .iter()
            .collect();
        let file = File::create(filename)?;
        let mut writer = Writer::new(file);
        writer.write(&batch)?;
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
