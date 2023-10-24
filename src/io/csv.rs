// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Imports / exports through parquet format.

use std::{
    fs::File,
    path::{Path, PathBuf},
};

use anyhow::Result;
use arrow::csv::Writer;

use super::arrow::ToArrow;

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
