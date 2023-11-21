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
use itertools::izip;
use parquet::{arrow::ArrowWriter, basic::Compression, file::properties::WriterProperties};
use polars::prelude::*;

use super::arrow::ToArrow;
use super::polars::ToPolars;
use crate::agent::Agent;

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

#[allow(dead_code, unused_variables, unused_mut, missing_docs)]
pub fn get_agents_from_parquet_files<T>(input_dir: &Path) -> Result<Vec<Agent<T>>> {
    // Read agents parquet file.
    let agents_filename: PathBuf = [input_dir.to_str().unwrap(), &"agents.parquet"]
        .iter()
        .collect();
    let agents_df = LazyFrame::scan_parquet(agents_filename, Default::default())?.collect()?;
    // let schema = Schema::from_iter([Field::new("agent_id", DataType::UInt64))
    // let agents_df = LazyFrame::scan_parquet(agents_filename, Default::default())?
    // .collect()?
    // .select_with_schema(["agent_id", "mode_choice"], schema)?;
    assert_eq!(
        agents_df.height(),
        agents_df["agent_id"].n_unique()?,
        "Agent ids must be unique in file `agents.parquet`"
    );
    // Read modes parquet file.
    let modes_filename: PathBuf = [input_dir.to_str().unwrap(), &"modes.parquet"]
        .iter()
        .collect();
    let modes_df = LazyFrame::scan_parquet(modes_filename, Default::default())?.collect()?;
    // Read legs parquet file.
    let legs_filename: PathBuf = [input_dir.to_str().unwrap(), &"legs.parquet"]
        .iter()
        .collect();
    let legs_df = LazyFrame::scan_parquet(legs_filename, Default::default())?.collect()?;
    // Create DataFrame with the indices in `modes_df` corresponding to each agent id.
    let mut mode_ids = modes_df.group_by(["agent_id"])?.groups()?;
    mode_ids.rename("groups", "mode_ids")?;
    // Create DataFrame with the indices in `legs_df` corresponding to each agent id.
    let mut leg_ids = legs_df.group_by(["agent_id"])?.groups()?;
    leg_ids.rename("groups", "leg_ids")?;
    // Add the mode indices and leg indices of the agents to `agent_df`.
    let agents_df = agents_df
        .left_join(&mode_ids, ["agent_id"], ["agent_id"])?
        .left_join(&leg_ids, ["agent_id"], ["agent_id"])?;
    let mut agents = Vec::with_capacity(agents_df.height());
    for (agent_id, choice_model, mode_ids, leg_ids) in izip!(
        agents_df["agent_id"].iter(),
        agents_df["choice_model"].iter(),
        agents_df["mode_ids"].iter(),
        agents_df["leg_ids"].iter(),
    ) {}
    Ok(agents)
}
