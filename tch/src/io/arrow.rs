// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Utility functions to work with arrow format.

use std::path::Path;
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use arrow::array::{
    new_null_array, Array, ArrayRef, AsArray, Float64Array, Float64Builder, ListBuilder,
    StructArray, UInt64Array, UInt64Builder,
};
use arrow::compute::{cast_with_options, CastOptions};
use arrow::datatypes::{DataType, Field, FieldRef, Schema};
use arrow::record_batch::RecordBatch;
use hashbrown::{HashMap, HashSet};
use log::warn;
use ttf::{PwlTTF, TTF};

use crate::tools::{Edge, Graph, Query, QueryResult};

pub trait ToArrow<const J: usize = 1> {
    fn to_arrow(data: &Self, list_to_string: bool) -> Result<[Option<RecordBatch>; J]>;
    fn names() -> [&'static str; J];
}

/// Reads [Graph] from the filenames of edges and TTFs.
pub fn get_graph_from_files(edges_path: &Path, ttfs_path: Option<&Path>) -> Result<Graph> {
    let mut ttf_map = if let Some(path) = ttfs_path {
        let ttfs_batch = filename_to_batch_record(path)?;
        let ttfs_vec = read_ttfs(ttfs_batch).context("Cannot parse TTFs")?;
        // Collect all the values in a map edge_id -> (td, tt).
        let mut global_map: HashMap<u64, Vec<(f64, f64)>> = HashMap::new();
        for (eid, x, y) in ttfs_vec {
            global_map.entry(eid).or_insert_with(Vec::new).push((x, y));
        }
        // Build the TTFs.
        let mut ttf_map = HashMap::with_capacity(global_map.len());
        for (eid, xy_vec) in global_map.into_iter() {
            let ttf = build_ttf(xy_vec)
                .with_context(|| format!("Failed to build TTF for edge id `{eid}`"))?;
            ttf_map.insert(eid, ttf);
        }
        check_same_start_and_interval(&ttf_map)?;
        ttf_map
    } else {
        HashMap::new()
    };
    let edge_batch = filename_to_batch_record(edges_path)?;
    let mut edges = read_edges(edge_batch).context("Cannot parse edges")?;
    for edge in edges.iter_mut() {
        if let Some(ttf) = ttf_map.remove(&edge.edge_id) {
            edge.travel_time = ttf
        }
    }
    Ok(Graph::from_edges(edges))
}

fn build_ttf(mut xy_vec: Vec<(f64, f64)>) -> Result<TTF<f64>> {
    debug_assert!(!xy_vec.is_empty());
    if xy_vec.len() == 1 {
        return Ok(TTF::Constant(xy_vec[0].1));
    }
    xy_vec.sort_by(|(x0, _), (x1, _)| x0.partial_cmp(x1).unwrap());
    let start_x = xy_vec[0].0;
    let interval_x = xy_vec[1].0 - start_x;
    if !xy_vec
        .iter()
        .zip(std::iter::successors(Some(start_x), |&t| {
            Some(t + interval_x)
        }))
        .all(|(xy, xp_td)| xy.0 == xp_td)
    {
        bail!(
            "The departure time values are not evenly spaced with interval {}",
            interval_x
        );
    }
    let ttf = if xy_vec.iter().all(|xy| xy.1 == xy_vec[0].1) {
        TTF::Constant(xy_vec[0].1)
    } else {
        TTF::Piecewise(PwlTTF::from_values(
            xy_vec.into_iter().map(|xy| xy.1).collect(),
            start_x,
            interval_x,
        ))
    };
    Ok(ttf)
}

fn check_same_start_and_interval(ttf_map: &HashMap<u64, TTF<f64>>) -> Result<()> {
    if let Some((start, interval)) = ttf_map
        .values()
        .filter_map(get_ttf_start_and_interval)
        .next()
    {
        if ttf_map
            .values()
            .filter_map(get_ttf_start_and_interval)
            .all(|(start_x, interval_x)| start_x == start && interval_x == interval)
        {
            Ok(())
        } else {
            Err(anyhow!(
                "All the TTFs must have the same departure-time intervals"
            ))
        }
    } else {
        // All TTFs are constant.
        Ok(())
    }
}

fn get_ttf_start_and_interval(ttf: &TTF<f64>) -> Option<(f64, f64)> {
    if let TTF::Piecewise(pwl_ttf) = ttf {
        Some((
            pwl_ttf.x_at_index(0),
            pwl_ttf.x_at_index(1) - pwl_ttf.x_at_index(0),
        ))
    } else {
        None
    }
}

/// Reads node ordering from a filename.
pub fn get_node_order_from_file(path: &Path) -> Result<HashMap<u64, usize>> {
    let batch = filename_to_batch_record(path)?;
    let order = read_node_order(batch).context("Cannot parse node ordering")?;
    Ok(order)
}

/// Reads queries from a filename.
pub fn get_queries_from_file(path: &Path) -> Result<Vec<Query>> {
    let batch = filename_to_batch_record(path)?;
    let queries = read_queries(batch).context("Cannot parse queries")?;
    Ok(queries)
}

/// Reads a CSV or Parquet file as a [RecordBatch].
fn filename_to_batch_record(filename: &Path) -> Result<RecordBatch> {
    match filename.extension().and_then(|e| e.to_str()) {
        Some("parquet") => super::parquet::get_batch_record(filename),
        Some("csv") => super::csv::get_batch_record(filename),
        Some(_) | None => Err(anyhow!("Unrecognised file format: `{filename:?}`")),
    }
}

/// Returns a reference to the array corresponding to the column that matches the given names.
///
/// Returns `None` if the column cannot be found.
///
/// If `names` is `["a", "b"]`, the function searches for the columns with name `"a.b"` and `"a_b"`
/// or for a Struct column with name `"a"` and a subcolumn named `"b"`.
fn get_column(array: &StructArray, names: &[&str]) -> Option<ArrayRef> {
    debug_assert!(!names.is_empty());
    if let Some(array) = array.column_by_name(names[0]) {
        if names.len() == 1 {
            return Some(array.clone());
        }
        // Nested structure.
        if let Some(struct_array) = array.as_struct_opt() {
            if let Some(array) = get_column(struct_array, &names[1..]) {
                return Some(array);
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
    // Try to find the nested column as an non-nested column with a separator.
    let full_name = names.join(".");
    if let Some(array) = get_column(array, &[full_name.as_str()]) {
        return Some(array);
    }
    None
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

/// Macro to get a column by name from an array and cast it to a specific datatype.
macro_rules! get_column {
    ([$($name:literal),+] in $array:ident as $ty:tt) => {
        get_column_inner!([$($name),+] in $array as type_to_array!($ty) | type_to_dtype!($ty))
    };
}

macro_rules! type_to_dtype {
    (u64) => {
        DataType::UInt64
    };
    (f64) => {
        DataType::Float64
    };
    (str) => {
        DataType::Utf8
    };
    (bool) => {
        DataType::Boolean
    };
}

macro_rules! type_to_array {
    (u64) => {
        UInt64Array
    };
    (f64) => {
        Float64Array
    };
    (str) => {
        StringArray
    };
    (bool) => {
        BooleanArray
    };
}

macro_rules! get_column_inner {
    ([$($name:literal),+] in $array:ident as $out_array:ty | $dtype:expr) => {
        {
            let column = get_column(&$array, &[$($name),+])
                .unwrap_or_else(|| new_null_array(&$dtype, $array.len()));
            let casted_column = cast_column(&column, &$dtype, &[$($name),+])?;
            casted_column.as_any().downcast_ref::<$out_array>().unwrap().clone()
        }
    };
}

/// Macro to get a value at a given position from an array, or `None` if the value is `null`.
macro_rules! get_value {
    ($array:ident[$i:ident]) => {
        if $array.is_null($i) {
            None
        } else {
            Some($array.value($i))
        }
    };
}

const EDGE_COLUMNS: [&str; 4] = ["edge_id", "source", "target", "travel_time"];

/// Reads an arrow `RecordBatch` with edges data and returns a `Vec` of `Edge`.
pub(crate) fn read_edges(batch: RecordBatch) -> Result<Vec<Edge>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &EDGE_COLUMNS);
    let edge_id_values = get_column!(["edge_id"] in struct_array as u64);
    let source_values = get_column!(["source"] in struct_array as u64);
    let target_values = get_column!(["target"] in struct_array as u64);
    let travel_time_values = get_column!(["travel_time"] in struct_array as f64);
    let n = struct_array.len();
    let mut edges = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity(n);
    for i in 0..n {
        let edge_id = get_value!(edge_id_values[i]);
        let source = get_value!(source_values[i]);
        let target = get_value!(target_values[i]);
        let travel_time = get_value!(travel_time_values[i]);
        let edge_id = edge_id.ok_or_else(|| anyhow!("Value `edge_id` is mandatory"))?;
        let source = source.ok_or_else(|| anyhow!("Value `source` is mandatory"))?;
        let target = target.ok_or_else(|| anyhow!("Value `target` is mandatory"))?;
        let travel_time = TTF::Constant(travel_time.unwrap_or(1.0));
        let edge = Edge {
            edge_id,
            source,
            target,
            travel_time,
        };
        if !unique_ids.insert(edge_id) {
            bail!("Found duplicate `edge_id`: {edge_id}",);
        }
        edges.push(edge);
    }
    Ok(edges)
}

const TTFS_COLUMNS: [&str; 3] = ["edge_id", "departure_time", "travel_time"];

type TTFsVec = Vec<(u64, f64, f64)>;

/// Reads an arrow `RecordBatch` with TTFs data and returns a [TTFsVec].
pub(crate) fn read_ttfs(batch: RecordBatch) -> Result<TTFsVec> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &TTFS_COLUMNS);
    let edge_id_values = get_column!(["edge_id"] in struct_array as u64);
    let departure_time_values = get_column!(["departure_time"] in struct_array as f64);
    let travel_time_values = get_column!(["travel_time"] in struct_array as f64);
    let n = struct_array.len();
    let mut ttfs = Vec::with_capacity(n);
    for i in 0..n {
        let edge_id = get_value!(edge_id_values[i]);
        let departure_time = get_value!(departure_time_values[i]);
        let travel_time = get_value!(travel_time_values[i]);
        let edge_id = edge_id.ok_or_else(|| anyhow!("Value `edge_id` is mandatory"))?;
        let departure_time =
            departure_time.ok_or_else(|| anyhow!("Value `departure_time` is mandatory"))?;
        let travel_time = travel_time.ok_or_else(|| anyhow!("Value `travel_time` is mandatory"))?;
        ttfs.push((edge_id, departure_time, travel_time));
    }
    Ok(ttfs)
}

const NODE_ORDER_COLUMNS: [&str; 2] = ["node_id", "order"];

/// Reads an arrow `RecordBatch` with node ordering and returns a Vec with the ordering.
pub(crate) fn read_node_order(batch: RecordBatch) -> Result<HashMap<u64, usize>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &NODE_ORDER_COLUMNS);
    let node_id_values = get_column!(["node_id"] in struct_array as u64);
    let order_values = get_column!(["order"] in struct_array as u64);
    let n = struct_array.len();
    let mut nodes = HashMap::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity(n);
    for i in 0..n {
        let node_id = get_value!(node_id_values[i]);
        let order = get_value!(order_values[i]);
        let node_id = node_id.ok_or_else(|| anyhow!("Value `node_id` is mandatory"))?;
        let order = order.ok_or_else(|| anyhow!("Value `order` is mandatory"))? as usize;
        if !unique_ids.insert(node_id) {
            bail!("Found duplicate `node_id`: {node_id}",);
        }
        nodes.insert(node_id, order);
    }
    Ok(nodes)
}

const QUERY_COLUMNS: [&str; 4] = ["query_id", "origin", "destination", "departure_time"];

/// Reads an arrow `RecordBatch` with queries and returns a Vec of [Query].
pub(crate) fn read_queries(batch: RecordBatch) -> Result<Vec<Query>> {
    let struct_array = StructArray::from(batch);
    warn_unused_columns(&struct_array, &QUERY_COLUMNS);
    let query_id_values = get_column!(["query_id"] in struct_array as u64);
    let origin_values = get_column!(["origin"] in struct_array as u64);
    let destination_values = get_column!(["destination"] in struct_array as u64);
    let departure_time_values = get_column!(["departure_time"] in struct_array as f64);
    let n = struct_array.len();
    let mut queries = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity(n);
    for i in 0..n {
        let query_id = get_value!(query_id_values[i]);
        let origin = get_value!(origin_values[i]);
        let destination = get_value!(destination_values[i]);
        let departure_time = get_value!(departure_time_values[i]);
        let query_id = query_id.ok_or_else(|| anyhow!("Value `query_id` is mandatory"))?;
        let origin = origin.ok_or_else(|| anyhow!("Value `origin` is mandatory"))?;
        let destination = destination.ok_or_else(|| anyhow!("Value `destination` is mandatory"))?;
        if !unique_ids.insert(query_id) {
            bail!("Found duplicate `query_id`: {query_id}",);
        }
        let query = Query {
            id: query_id,
            source: origin,
            target: destination,
            departure_time,
        };
        queries.push(query);
    }
    Ok(queries)
}

/// Sends warnings for unused columns.
fn warn_unused_columns(array: &StructArray, columns: &[&str]) {
    let columns_set: HashSet<&str> = columns.iter().copied().collect();
    for field in array.fields() {
        check_unused_column(field, &columns_set, vec![]);
    }
}

fn check_unused_column(field: &FieldRef, columns: &HashSet<&str>, mut prefix: Vec<String>) {
    match field.data_type() {
        DataType::Struct(struct_field) => {
            prefix.push(field.name().to_owned());
            for subfield in struct_field {
                check_unused_column(subfield, columns, prefix.clone())
            }
        }
        _ => {
            let full_name = if prefix.is_empty() {
                field.name().to_owned()
            } else {
                format!("{}.{}", prefix.join("."), field.name())
            };
            if !columns.contains(full_name.as_str()) {
                warn!("Unknown column `{}`", full_name);
            }
        }
    }
}

#[derive(Debug, Default)]
struct NodeOrderBuilder {
    node_id: UInt64Builder,
    order: UInt64Builder,
}

impl NodeOrderBuilder {
    fn new() -> Self {
        Self::default()
    }

    fn append(&mut self, node_id: u64, order: usize) {
        self.node_id.append_value(node_id);
        self.order.append_value(order as u64);
    }

    fn finish(&mut self) -> Result<Option<RecordBatch>> {
        let schema = Schema::new(vec![
            Field::new("node_id", DataType::UInt64, false),
            Field::new("order", DataType::UInt64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(self.node_id.finish()),
                Arc::new(self.order.finish()),
            ],
        )?;
        if batch.num_rows() == 0 {
            Ok(None)
        } else {
            Ok(Some(batch))
        }
    }
}

impl ToArrow for HashMap<u64, usize> {
    fn to_arrow(
        data: &HashMap<u64, usize>,
        _list_to_string: bool,
    ) -> Result<[Option<RecordBatch>; 1]> {
        let mut builder = NodeOrderBuilder::new();
        for (node_id, order) in data.iter() {
            builder.append(*node_id, *order);
        }
        Ok([builder.finish()?])
    }
    fn names() -> [&'static str; 1] {
        ["node_order"]
    }
}

#[derive(Debug, Default)]
struct QueryResultBuilder {
    ea_query_id: UInt64Builder,
    ea_arrival_time: Float64Builder,
    ea_route: ListBuilder<UInt64Builder>,
    profile_query_id: UInt64Builder,
    profile_departure_time: Float64Builder,
    profile_travel_time: Float64Builder,
}

impl QueryResultBuilder {
    fn new() -> Self {
        Self::default()
    }

    fn append(&mut self, res: &QueryResult) {
        match res {
            QueryResult::EarliestArrival((query_id, maybe_ta, maybe_route)) => {
                self.ea_query_id.append_value(*query_id);
                if let Some(ta) = maybe_ta {
                    self.ea_arrival_time.append_value(*ta);
                    if let Some(route) = maybe_route {
                        self.ea_route.append_value(route.iter().map(|id| Some(*id)));
                    } else {
                        self.ea_route.append_null();
                    }
                } else {
                    // Origin and destination are not connected.
                    self.ea_arrival_time.append_null();
                    debug_assert!(maybe_route.is_none());
                    self.ea_route.append_null();
                }
            }
            QueryResult::Profile((query_id, maybe_ttf)) => {
                if let Some(ttf) = maybe_ttf {
                    match ttf {
                        TTF::Constant(tt) => {
                            self.profile_query_id.append_value(*query_id);
                            self.profile_departure_time.append_null();
                            self.profile_travel_time.append_value(*tt);
                        }
                        TTF::Piecewise(pwl_ttf) => {
                            for (x, y) in pwl_ttf.iter() {
                                self.profile_query_id.append_value(*query_id);
                                self.profile_departure_time.append_value(x);
                                self.profile_travel_time.append_value(y);
                            }
                        }
                    }
                } else {
                    // Origin and destination are not connected.
                    self.profile_query_id.append_value(*query_id);
                    self.profile_departure_time.append_null();
                    self.profile_travel_time.append_null();
                }
            }
        }
    }

    fn finish(&mut self, list_to_string: bool) -> Result<[Option<RecordBatch>; 2]> {
        let route_dt = if list_to_string {
            DataType::Utf8
        } else {
            DataType::new_list(DataType::UInt64, true)
        };
        let ea_schema = Schema::new(vec![
            Field::new("query_id", DataType::UInt64, false),
            Field::new("arrival_time", DataType::Float64, true),
            Field::new("route", route_dt, true),
        ]);
        let route_array = if list_to_string {
            cast_with_options(
                &self.ea_route.finish(),
                &DataType::Utf8,
                &CastOptions {
                    safe: false,
                    ..Default::default()
                },
            )?
        } else {
            Arc::new(self.ea_route.finish())
        };
        let ea_batch = RecordBatch::try_new(
            Arc::new(ea_schema),
            vec![
                Arc::new(self.ea_query_id.finish()),
                Arc::new(self.ea_arrival_time.finish()),
                route_array,
            ],
        )?;
        let profile_schema = Schema::new(vec![
            Field::new("query_id", DataType::UInt64, false),
            Field::new("departure_time", DataType::Float64, true),
            Field::new("travel_time", DataType::Float64, true),
        ]);
        let profile_batch = RecordBatch::try_new(
            Arc::new(profile_schema),
            vec![
                Arc::new(self.profile_query_id.finish()),
                Arc::new(self.profile_departure_time.finish()),
                Arc::new(self.profile_travel_time.finish()),
            ],
        )?;
        let batch0 = if ea_batch.num_rows() == 0 {
            None
        } else {
            Some(ea_batch)
        };
        let batch1 = if profile_batch.num_rows() == 0 {
            None
        } else {
            Some(profile_batch)
        };
        Ok([batch0, batch1])
    }
}

impl ToArrow<2> for Vec<QueryResult> {
    fn to_arrow(data: &Self, list_to_string: bool) -> Result<[Option<RecordBatch>; 2]> {
        let mut builder = QueryResultBuilder::new();
        for res in data.iter() {
            builder.append(res);
        }
        builder.finish(list_to_string)
    }
    fn names() -> [&'static str; 2] {
        ["ea_results", "profile_results"]
    }
}
