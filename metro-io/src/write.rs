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

//! Functions to convert data to arrow format and to write it as CSV or Parquet files.
use std::any::Any;
use std::fs::File;
use std::path::Path;
use std::sync::Arc;

use anyhow::{Context, Result};
use arrow::array::{
    ArrayBuilder, ArrayRef, Int64Builder, RecordBatch, StringBuilder, UInt64Builder,
};
use arrow::compute::{cast_with_options, CastOptions};
use arrow::csv::Writer;
use arrow::datatypes::{DataType, Schema};
use parquet::arrow::ArrowWriter;
use parquet::basic::{Compression, Encoding, ZstdLevel};
use parquet::file::properties::WriterProperties;
use parquet::schema::types::ColumnPath;

use crate::MetroId;

/// Trait for data that can be converted to arrow format, as `J` tables.
pub trait ToArrow<const J: usize = 1> {
    /// Converts the data to `J` [RecordBatch]es (`None` if a table is empty).
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; J]>;
    /// Returns the names of the `J` tables, used as filenames.
    fn names() -> [&'static str; J];
}

/// Builds a [RecordBatch] from a list of `(name, builder, nullable)` columns.
///
/// The data type of each column is the one of the array built.
///
/// Returns `None` if the [RecordBatch] has no row.
pub fn finish_batch(
    columns: Vec<(&str, &mut dyn ArrayBuilder, bool)>,
) -> Result<Option<RecordBatch>> {
    let batch = RecordBatch::try_from_iter_with_nullable(
        columns
            .into_iter()
            .map(|(name, builder, nullable)| (name, builder.finish(), nullable)),
    )?;
    Ok((batch.num_rows() > 0).then_some(batch))
}

/// Writes data that can be converted to arrow format as CSV files.
///
/// If `float32` is `true`, Float64 columns are written as Float32 values.
pub fn write_csv<D: ToArrow<J>, const J: usize>(
    data: &D,
    output_dir: &Path,
    float32: bool,
) -> Result<()> {
    write_csv_with_prefix(data, output_dir, "", float32)
}

/// Writes data that can be converted to arrow format as CSV files.
///
/// The given prefix is prepended to the names of the saved files.
///
/// As the CSV format does not support lists, List columns are written as strings.
///
/// If `float32` is `true`, Float64 columns are written as Float32 values.
pub fn write_csv_with_prefix<D: ToArrow<J>, const J: usize>(
    data: &D,
    output_dir: &Path,
    prefix: &str,
    float32: bool,
) -> Result<()> {
    for (name, maybe_batch) in D::names().into_iter().zip(data.to_arrow()?) {
        if let Some(batch) = maybe_batch {
            let filename = output_dir.join(format!("{prefix}{name}.csv"));
            let file = File::create(&filename)
                .with_context(|| format!("Cannot create file `{filename:?}`"))?;
            let batch = cast_columns(&batch, |dtype| csv_type(dtype, float32))
                .with_context(|| format!("Cannot cast columns for `{filename:?}`"))?;
            Writer::new(file)
                .write(&batch)
                .with_context(|| format!("Cannot write batch to file `{filename:?}`"))?;
        }
    }
    Ok(())
}

/// Returns the data type to which a column of the given data type is cast before being written as
/// CSV (`None` if the column is written as is).
///
/// List columns are cast to strings and, if `float32` is `true`, Float64 columns are cast to
/// Float32.
fn csv_type(dtype: &DataType, float32: bool) -> Option<DataType> {
    match dtype {
        DataType::List(_) | DataType::LargeList(_) => Some(DataType::Utf8),
        _ => float32_type(dtype, float32),
    }
}

/// Returns `Some(DataType::Float32)` if `float32` is `true` and the given data type is Float64,
/// `None` otherwise.
fn float32_type(dtype: &DataType, float32: bool) -> Option<DataType> {
    (float32 && dtype == &DataType::Float64).then_some(DataType::Float32)
}

/// Returns a copy of the [RecordBatch] where each column is cast to the data type returned by
/// `to_type` (columns for which `to_type` returns `None` are left unchanged).
fn cast_columns(
    batch: &RecordBatch,
    to_type: impl Fn(&DataType) -> Option<DataType>,
) -> Result<RecordBatch> {
    let schema = batch.schema();
    let columns = schema
        .fields()
        .iter()
        .zip(batch.columns())
        .map(|(field, column)| {
            let column = if let Some(dtype) = to_type(field.data_type()) {
                cast_with_options(
                    column,
                    &dtype,
                    &CastOptions {
                        safe: false,
                        ..Default::default()
                    },
                )?
            } else {
                Arc::clone(column)
            };
            Ok((field.name(), column, field.is_nullable()))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(RecordBatch::try_from_iter_with_nullable(columns)?)
}

/// Writes data that can be converted to arrow format as Parquet files.
///
/// If `float32` is `true`, Float64 columns are written as Float32 columns.
pub fn write_parquet<D: ToArrow<J>, const J: usize>(
    data: &D,
    output_dir: &Path,
    float32: bool,
) -> Result<()> {
    write_parquet_with_prefix(data, output_dir, "", float32)
}

/// Writes data that can be converted to arrow format as Parquet files.
///
/// The given prefix is prepended to the names of the saved files.
///
/// If `float32` is `true`, Float64 columns are written as Float32 columns.
pub fn write_parquet_with_prefix<D: ToArrow<J>, const J: usize>(
    data: &D,
    output_dir: &Path,
    prefix: &str,
    float32: bool,
) -> Result<()> {
    for (name, maybe_batch) in D::names().into_iter().zip(data.to_arrow()?) {
        if let Some(batch) = maybe_batch {
            let filename = output_dir.join(format!("{prefix}{name}.parquet"));
            let file = File::create(&filename)
                .with_context(|| format!("Cannot create file `{filename:?}`"))?;
            let batch = if float32 {
                cast_columns(&batch, |dtype| float32_type(dtype, true))
                    .with_context(|| format!("Cannot cast columns for `{filename:?}`"))?
            } else {
                batch
            };
            let props = parquet_writer_properties(&batch.schema());
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

/// Returns the properties used to write Parquet files with the given schema.
///
/// Columns are compressed with ZSTD. Float columns are written with the `BYTE_STREAM_SPLIT`
/// encoding (instead of dictionary encoding), which makes them much more compressible.
fn parquet_writer_properties(schema: &Schema) -> WriterProperties {
    let mut builder =
        WriterProperties::builder().set_compression(Compression::ZSTD(ZstdLevel::default()));
    for field in schema.fields() {
        if matches!(field.data_type(), DataType::Float32 | DataType::Float64) {
            let path = ColumnPath::from(field.name().as_str());
            builder = builder
                .set_column_dictionary_enabled(path.clone(), false)
                .set_column_encoding(path, Encoding::BYTE_STREAM_SPLIT);
        }
    }
    builder.build()
}

/// Arrow builder for [MetroId] values.
///
/// The data type of the array (`u64`, `i64` or string) is set by the first value appended. If no
/// value is appended, the array is of type `u64`.
#[derive(Debug, Default)]
pub enum IdBuilder {
    /// No value appended yet.
    #[default]
    Uninitiated,
    /// Builder for ids stored as unsigned integers.
    Unsigned(UInt64Builder),
    /// Builder for ids stored as signed integers.
    Integer(Int64Builder),
    /// Builder for ids stored as strings.
    Arbitrary(StringBuilder),
}

impl IdBuilder {
    /// Appends a value to the builder.
    ///
    /// Panics if the value is not of the same kind as the first value appended.
    pub fn append_value(&mut self, v: MetroId) {
        // Only when the first value is appended (the first time this function is called), can we
        // know the dtype of the ids (uint, int or str).
        if matches!(self, Self::Uninitiated) {
            *self = match v {
                MetroId::Unsigned(_) => Self::Unsigned(Default::default()),
                MetroId::Integer(_) => Self::Integer(Default::default()),
                MetroId::Arbitrary(_) => Self::Arbitrary(Default::default()),
            };
        }
        match self {
            Self::Unsigned(builder) => builder.append_value(v.into_unsigned().unwrap()),
            Self::Integer(builder) => builder.append_value(v.into_integer().unwrap()),
            Self::Arbitrary(builder) => builder.append_value(v.resolve_arbitrary().unwrap()),
            Self::Uninitiated => unreachable!(),
        }
    }

    /// Appends a null value to the builder.
    ///
    /// Panics if no value was appended before.
    pub fn append_null(&mut self) {
        match self {
            Self::Unsigned(builder) => builder.append_null(),
            Self::Integer(builder) => builder.append_null(),
            Self::Arbitrary(builder) => builder.append_null(),
            Self::Uninitiated => unreachable!(),
        }
    }
}

impl ArrayBuilder for IdBuilder {
    fn len(&self) -> usize {
        match self {
            Self::Unsigned(builder) => builder.len(),
            Self::Integer(builder) => builder.len(),
            Self::Arbitrary(builder) => builder.len(),
            Self::Uninitiated => 0,
        }
    }
    fn finish(&mut self) -> ArrayRef {
        match self {
            Self::Unsigned(builder) => Arc::new(builder.finish()),
            Self::Integer(builder) => Arc::new(builder.finish()),
            Self::Arbitrary(builder) => Arc::new(builder.finish()),
            // It can happen that no value where inserted into the builder.
            // In this case, the dtype is UInt64 and an empty array is returned.
            Self::Uninitiated => Arc::new(UInt64Builder::default().finish()),
        }
    }
    fn finish_cloned(&self) -> ArrayRef {
        match self {
            Self::Unsigned(builder) => Arc::new(builder.finish_cloned()),
            Self::Integer(builder) => Arc::new(builder.finish_cloned()),
            Self::Arbitrary(builder) => Arc::new(builder.finish_cloned()),
            Self::Uninitiated => Arc::new(UInt64Builder::default().finish()),
        }
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
    fn into_box_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

impl Extend<Option<MetroId>> for IdBuilder {
    fn extend<T: IntoIterator<Item = Option<MetroId>>>(&mut self, iter: T) {
        for v in iter {
            match v {
                Some(v) => self.append_value(v),
                None => self.append_null(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use arrow::array::{AsArray, Float64Builder, ListBuilder};

    use super::*;

    #[test]
    fn finish_batch_test() {
        let mut ids = IdBuilder::default();
        let mut values = Float64Builder::new();
        let mut lists = ListBuilder::new(IdBuilder::default());
        assert!(finish_batch(vec![
            ("id", &mut ids, false),
            ("value", &mut values, true),
            ("list", &mut lists, true),
        ])
        .unwrap()
        .is_none());
        ids.append_value(MetroId::from("a"));
        values.append_null();
        lists.append_value([Some(MetroId::Integer(-1)), Some(MetroId::Integer(2))]);
        let batch = finish_batch(vec![
            ("id", &mut ids, false),
            ("value", &mut values, true),
            ("list", &mut lists, true),
        ])
        .unwrap()
        .unwrap();
        let schema = batch.schema();
        assert_eq!(schema.field(0).data_type(), &DataType::Utf8);
        assert!(!schema.field(0).is_nullable());
        assert_eq!(schema.field(1).data_type(), &DataType::Float64);
        assert!(schema.field(1).is_nullable());
        assert_eq!(
            schema.field(2).data_type(),
            &DataType::new_list(DataType::Int64, true)
        );
        let csv_batch = cast_columns(&batch, |dtype| csv_type(dtype, false)).unwrap();
        assert_eq!(csv_batch.schema().field(1).data_type(), &DataType::Float64);
        assert_eq!(csv_batch.schema().field(2).data_type(), &DataType::Utf8);
        assert_eq!(csv_batch.column(2).as_string::<i32>().value(0), "[-1, 2]");
        let csv_batch = cast_columns(&batch, |dtype| csv_type(dtype, true)).unwrap();
        assert_eq!(csv_batch.schema().field(0).data_type(), &DataType::Utf8);
        assert_eq!(csv_batch.schema().field(1).data_type(), &DataType::Float32);
        assert!(csv_batch.schema().field(1).is_nullable());
        assert_eq!(csv_batch.schema().field(2).data_type(), &DataType::Utf8);
    }
}
