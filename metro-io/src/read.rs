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

//! Functions to read CSV or Parquet files and to extract typed columns from them.
//!
//! A file is read as a [RecordBatch] with [read_batch], then its columns are extracted with a
//! [Columns] and their values are read row by row with [GetValue]:
//!
//! ```no_run
//! # use std::path::Path;
//! # use metro_io::read::{read_batch, required, Columns, GetValue};
//! # fn main() -> anyhow::Result<()> {
//! let mut columns = Columns::new(read_batch(Path::new("edges.parquet"))?);
//! let edge_ids = columns.id(&["edge_id"])?;
//! let speeds = columns.f64(&["speed"])?;
//! columns.warn_unused();
//! for i in 0..columns.len() {
//!     let edge_id = required(edge_ids.get(i), "edge_id")?;
//!     let speed: Option<f64> = speeds.get(i);
//! }
//! # Ok(())
//! # }
//! ```
use std::fs::File;
use std::io::Seek;
use std::path::Path;
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use arrow::array::{
    new_null_array, Array, ArrayRef, ArrowPrimitiveType, AsArray, BooleanArray, Float64Array,
    Int64Array, LargeListArray, ListArray, PrimitiveArray, StringArray, StructArray, UInt64Array,
};
use arrow::compute::{cast_with_options, CastOptions};
use arrow::csv::{reader::Format, ReaderBuilder};
use arrow::datatypes::{DataType, FieldRef, Float64Type, Int64Type, UInt64Type};
use arrow::record_batch::RecordBatch;
use log::warn;
use parquet::arrow::arrow_reader::ParquetRecordBatchReaderBuilder;

use crate::hash::HashSet;
use crate::MetroId;

/// Reads a CSV or Parquet file as a [RecordBatch].
///
/// The format is deduced from the extension of the file (`.csv` or `.parquet`).
pub fn read_batch(filename: &Path) -> Result<RecordBatch> {
    match filename.extension().and_then(|e| e.to_str()) {
        Some("parquet") => read_parquet(filename),
        Some("csv") => read_csv(filename),
        Some(_) | None => Err(anyhow!("Unrecognised file format: `{filename:?}`")),
    }
}

fn read_csv(filename: &Path) -> Result<RecordBatch> {
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

fn read_parquet(filename: &Path) -> Result<RecordBatch> {
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

/// Returns the value if it is not `None` or an error stating that value `name` is mandatory.
pub fn required<T>(value: Option<T>, name: &str) -> Result<T> {
    value.ok_or_else(|| anyhow!("Value `{name}` is mandatory"))
}

/// Typed access to the columns of a [RecordBatch].
///
/// A column is identified by a list of names: `["a", "b"]` designates either the sub-column `"b"`
/// of the Struct column `"a"` or the column named `"a.b"`.
///
/// Missing columns are returned as arrays full of nulls. Columns are cast to the requested type,
/// returning an error if the cast fails.
///
/// The names of the requested columns are recorded so that [Columns::warn_unused] can warn about
/// the columns that were never requested.
#[derive(Debug)]
pub struct Columns {
    array: StructArray,
    used: HashSet<String>,
}

impl Columns {
    /// Creates a new [Columns] from a [RecordBatch].
    pub fn new(batch: RecordBatch) -> Self {
        Self {
            array: StructArray::from(batch),
            used: HashSet::default(),
        }
    }

    /// Returns the number of rows.
    pub fn len(&self) -> usize {
        self.array.len()
    }

    /// Returns `true` if there is no row.
    pub fn is_empty(&self) -> bool {
        self.array.is_empty()
    }

    /// Returns the column with the given names, as `f64` values.
    pub fn f64(&mut self, names: &[&str]) -> Result<Float64Array> {
        self.primitive::<Float64Type>(names)
    }

    /// Returns the column with the given names, as `u64` values.
    pub fn u64(&mut self, names: &[&str]) -> Result<UInt64Array> {
        self.primitive::<UInt64Type>(names)
    }

    /// Returns the column with the given names, as string values.
    pub fn str(&mut self, names: &[&str]) -> Result<StringArray> {
        let column = self.cast(names, &DataType::Utf8)?;
        Ok(column.as_string::<i32>().clone())
    }

    /// Returns the column with the given names, as boolean values.
    pub fn bool(&mut self, names: &[&str]) -> Result<BooleanArray> {
        let column = self.cast(names, &DataType::Boolean)?;
        Ok(column.as_boolean().clone())
    }

    /// Returns the column with the given names, as lists of `f64` values.
    ///
    /// Returns an error if a list contains a null value.
    pub fn list_f64(&mut self, names: &[&str]) -> Result<ListF64Array> {
        let column = self.cast(names, &DataType::new_list(DataType::Float64, false))?;
        Ok(ListF64Array(column.as_list::<i32>().clone()))
    }

    /// Returns the column with the given names, as [MetroId] values.
    pub fn id(&mut self, names: &[&str]) -> Result<IdArray> {
        let column = self.column(names, &DataType::UInt64);
        let column = cast_column(&column, &id_dtype(column.data_type()), names)?;
        Ok(IdArray::from_array(&column))
    }

    /// Returns the column with the given names, as lists of [MetroId] values.
    ///
    /// Returns an error if a list contains a null value.
    pub fn id_list(&mut self, names: &[&str]) -> Result<IdListArray> {
        let column = self.column(names, &DataType::new_large_list(DataType::UInt64, false));
        let inner_dtype = match column.data_type() {
            DataType::List(field)
            | DataType::ListView(field)
            | DataType::LargeList(field)
            | DataType::LargeListView(field) => field.data_type(),
            _ => bail!("Not a List column: {}", names.join(".")),
        };
        let dtype = DataType::new_large_list(id_dtype(inner_dtype), false);
        let column = cast_column(&column, &dtype, names)?;
        let lists = column.as_list::<i64>().clone();
        let values = IdArray::from_array(lists.values());
        Ok(IdListArray { lists, values })
    }

    /// Sends a warning for each column that has not been requested.
    pub fn warn_unused(&self) {
        for field in self.array.fields() {
            self.warn_unused_field(field, "");
        }
    }

    fn warn_unused_field(&self, field: &FieldRef, prefix: &str) {
        let full_name = format!("{prefix}{}", field.name());
        if let DataType::Struct(subfields) = field.data_type() {
            for subfield in subfields {
                self.warn_unused_field(subfield, &format!("{full_name}."));
            }
        } else if !self.used.contains(&full_name) {
            warn!("Unknown column `{full_name}`");
        }
    }

    fn primitive<T: ArrowPrimitiveType>(&mut self, names: &[&str]) -> Result<PrimitiveArray<T>> {
        let column = self.cast(names, &T::DATA_TYPE)?;
        Ok(column.as_primitive::<T>().clone())
    }

    /// Returns the column with the given names, cast to the given data type.
    fn cast(&mut self, names: &[&str], dtype: &DataType) -> Result<ArrayRef> {
        let column = self.column(names, dtype);
        cast_column(&column, dtype, names)
    }

    /// Returns the column with the given names, or an array of nulls with data type
    /// `default_dtype` if the column does not exist.
    fn column(&mut self, names: &[&str], default_dtype: &DataType) -> ArrayRef {
        self.used.insert(names.join("."));
        find_column(&self.array, names)
            .unwrap_or_else(|| new_null_array(default_dtype, self.array.len()))
    }
}

/// Returns the column that matches the given names, or `None` if the column cannot be found.
///
/// If `names` is `["a", "b"]`, the function searches for a Struct column with name `"a"` and a
/// sub-column named `"b"`, or for a column with name `"a.b"`.
fn find_column(array: &StructArray, names: &[&str]) -> Option<ArrayRef> {
    debug_assert!(!names.is_empty());
    if let Some(column) = array.column_by_name(names[0]) {
        if names.len() == 1 {
            return Some(column.clone());
        }
        // Nested structure.
        if let Some(struct_array) = column.as_struct_opt() {
            if let Some(column) = find_column(struct_array, &names[1..]) {
                return Some(column);
            }
        } else {
            warn!(
                "Column `{}` exists but it is not of type `Struct`",
                names[0]
            );
        }
    }
    if names.len() == 1 {
        return None;
    }
    // Try to find the nested column as a non-nested column with a separator.
    array.column_by_name(&names.join(".")).cloned()
}

/// Casts the given array to a new data type, returning an error if the cast failed.
fn cast_column(array: &dyn Array, to_type: &DataType, names: &[&str]) -> Result<ArrayRef> {
    cast_with_options(
        array,
        to_type,
        &CastOptions {
            safe: false,
            ..Default::default()
        },
    )
    .with_context(|| {
        format!(
            "Cannot cast column `{}` from {} to {}",
            names.join("."),
            array.data_type(),
            to_type
        )
    })
}

/// Returns the data type that ids of the given data type are read as: `u64` for unsigned
/// integers, `i64` for signed integers and strings otherwise.
fn id_dtype(dtype: &DataType) -> DataType {
    if dtype.is_unsigned_integer() {
        DataType::UInt64
    } else if dtype.is_integer() {
        DataType::Int64
    } else {
        DataType::Utf8
    }
}

/// Access to the value of an array at a given position.
pub trait GetValue {
    /// Type of the values returned.
    type Value<'a>
    where
        Self: 'a;

    /// Returns the value at position `i`, or `None` if the value is null.
    fn get(&self, i: usize) -> Option<Self::Value<'_>>;
}

impl<T: ArrowPrimitiveType> GetValue for PrimitiveArray<T> {
    type Value<'a> = T::Native;
    fn get(&self, i: usize) -> Option<T::Native> {
        self.is_valid(i).then(|| self.value(i))
    }
}

impl GetValue for StringArray {
    type Value<'a> = &'a str;
    fn get(&self, i: usize) -> Option<&str> {
        self.is_valid(i).then(|| self.value(i))
    }
}

impl GetValue for BooleanArray {
    type Value<'a> = bool;
    fn get(&self, i: usize) -> Option<bool> {
        self.is_valid(i).then(|| self.value(i))
    }
}

/// Array of lists of `f64` values.
#[derive(Debug)]
pub struct ListF64Array(ListArray);

impl GetValue for ListF64Array {
    type Value<'a> = Vec<f64>;
    fn get(&self, i: usize) -> Option<Vec<f64>> {
        if self.0.is_null(i) {
            return None;
        }
        self.0
            .value(i)
            .as_primitive::<Float64Type>()
            .iter()
            .collect()
    }
}

/// Array of [MetroId] values.
#[derive(Debug)]
pub enum IdArray {
    /// Ids stored as unsigned integers.
    Unsigned(UInt64Array),
    /// Ids stored as signed integers.
    Integer(Int64Array),
    /// Ids stored as strings.
    Arbitrary(StringArray),
}

impl IdArray {
    /// Creates an [IdArray] from an array whose data type was given by [id_dtype].
    fn from_array(array: &ArrayRef) -> Self {
        match array.data_type() {
            DataType::UInt64 => Self::Unsigned(array.as_primitive::<UInt64Type>().clone()),
            DataType::Int64 => Self::Integer(array.as_primitive::<Int64Type>().clone()),
            DataType::Utf8 => Self::Arbitrary(array.as_string::<i32>().clone()),
            dtype => unreachable!("Invalid data type for ids: {dtype}"),
        }
    }
}

impl GetValue for IdArray {
    type Value<'a> = MetroId;
    fn get(&self, i: usize) -> Option<MetroId> {
        match self {
            Self::Unsigned(array) => array.get(i).map(MetroId::from),
            Self::Integer(array) => array.get(i).map(MetroId::from),
            Self::Arbitrary(array) => array.get(i).map(MetroId::from),
        }
    }
}

/// Array of lists of [MetroId] values.
#[derive(Debug)]
pub struct IdListArray {
    lists: LargeListArray,
    /// Values of all the lists.
    values: IdArray,
}

impl GetValue for IdListArray {
    type Value<'a> = Vec<MetroId>;
    fn get(&self, i: usize) -> Option<Vec<MetroId>> {
        if self.lists.is_null(i) {
            return None;
        }
        let offsets = self.lists.value_offsets();
        (offsets[i] as usize..offsets[i + 1] as usize)
            .map(|j| self.values.get(j))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use arrow::array::{Int64Builder, LargeListBuilder, ListBuilder, StringBuilder};
    use arrow::datatypes::{Field, Fields};

    use super::*;

    fn batch(columns: Vec<(&str, ArrayRef)>) -> RecordBatch {
        RecordBatch::try_from_iter(columns).unwrap()
    }

    #[test]
    fn id_columns_test() {
        let mut columns = Columns::new(batch(vec![
            ("u", Arc::new(UInt64Array::from(vec![Some(1), None]))),
            ("i", Arc::new(Int64Array::from(vec![Some(-1), Some(2)]))),
            ("s", Arc::new(StringArray::from(vec![Some("a"), None]))),
        ]));
        let u = columns.id(&["u"]).unwrap();
        assert_eq!(u.get(0), Some(MetroId::Unsigned(1)));
        assert_eq!(u.get(1), None);
        let i = columns.id(&["i"]).unwrap();
        assert_eq!(i.get(0), Some(MetroId::Integer(-1)));
        let s = columns.id(&["s"]).unwrap();
        assert_eq!(s.get(0), Some(MetroId::from("a")));
        assert_eq!(s.get(1), None);
        // Missing columns are full of nulls.
        let missing = columns.id(&["missing"]).unwrap();
        assert_eq!(missing.get(0), None);
        assert_eq!(missing.get(1), None);
    }

    #[test]
    fn id_list_column_test() {
        let mut ints = ListBuilder::new(Int64Builder::new());
        ints.append_value([Some(1), Some(-2)]);
        ints.append_null();
        ints.append_value([]);
        ints.append_value([Some(4)]);
        let mut with_null = ListBuilder::new(Int64Builder::new());
        with_null.append_value([Some(3), None]);
        with_null.append_null();
        with_null.append_null();
        with_null.append_null();
        let mut strs = LargeListBuilder::new(StringBuilder::new());
        strs.append_value([Some("a")]);
        strs.append_value([Some("b"), Some("c")]);
        strs.append_null();
        strs.append_value([Some("d")]);
        let mut columns = Columns::new(batch(vec![
            ("ints", Arc::new(ints.finish())),
            ("strs", Arc::new(strs.finish())),
            ("with_null", Arc::new(with_null.finish())),
            ("not_list", Arc::new(Float64Array::from(vec![0.0; 4]))),
        ]));
        let ints = columns.id_list(&["ints"]).unwrap();
        assert_eq!(
            ints.get(0),
            Some(vec![MetroId::Integer(1), MetroId::Integer(-2)])
        );
        assert_eq!(ints.get(1), None);
        assert_eq!(ints.get(2), Some(vec![]));
        let strs = columns.id_list(&["strs"]).unwrap();
        assert_eq!(
            strs.get(1),
            Some(vec![MetroId::from("b"), MetroId::from("c")])
        );
        assert_eq!(strs.get(2), None);
        assert_eq!(strs.get(3), Some(vec![MetroId::from("d")]));
        // Lists with null values are not allowed.
        assert!(columns.id_list(&["with_null"]).is_err());
        assert!(columns.id_list(&["not_list"]).is_err());
        let missing = columns.id_list(&["missing"]).unwrap();
        assert_eq!(missing.get(0), None);
    }

    #[test]
    fn list_f64_column_test() {
        let mut lists = ListBuilder::new(Int64Builder::new());
        lists.append_value([Some(1), Some(2)]);
        lists.append_null();
        let mut columns = Columns::new(batch(vec![("l", Arc::new(lists.finish()))]));
        let lists = columns.list_f64(&["l"]).unwrap();
        assert_eq!(lists.get(0), Some(vec![1.0, 2.0]));
        assert_eq!(lists.get(1), None);
    }

    #[test]
    fn nested_column_test() {
        let inner = StructArray::new(
            Fields::from(vec![Field::new("b", DataType::Int64, true)]),
            vec![Arc::new(Int64Array::from(vec![1, 2]))],
            None,
        );
        let mut columns = Columns::new(batch(vec![
            ("a", Arc::new(inner)),
            ("c.d", Arc::new(StringArray::from(vec!["x", "y"]))),
            ("e", Arc::new(StringArray::from(vec!["1.5", "2"]))),
        ]));
        // Sub-column of a Struct column.
        assert_eq!(columns.f64(&["a", "b"]).unwrap().get(1), Some(2.0));
        // Column whose name contains a separator.
        assert_eq!(columns.str(&["c", "d"]).unwrap().get(0), Some("x"));
        // Strings are cast to floats.
        assert_eq!(columns.f64(&["e"]).unwrap().get(0), Some(1.5));
        // Invalid casts are errors.
        assert!(columns.u64(&["c", "d"]).is_err());
        assert_eq!(columns.bool(&["missing"]).unwrap().get(0), None);
        assert_eq!(
            columns.used,
            ["a.b", "c.d", "e", "missing"]
                .into_iter()
                .map(String::from)
                .collect()
        );
    }
}
