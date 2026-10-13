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

//! Functions to read the input files of the routing tool.

use std::path::Path;

use anyhow::{anyhow, bail, Context, Result};
use arrow::record_batch::RecordBatch;
use metro_io::read::{read_batch, required, Columns, GetValue};
use ttf::{PwlTTF, TTF};

use crate::hash::{HashMap, HashSet};
use crate::tools::{Edge, Graph, MetroId, Query};

/// Reads [Graph] from the filenames of edges and TTFs.
pub fn get_graph_from_files(edges_path: &Path, ttfs_path: Option<&Path>) -> Result<Graph> {
    let mut ttf_map = if let Some(path) = ttfs_path {
        let ttfs_batch = read_batch(path)?;
        let ttfs_vec = read_ttfs(ttfs_batch).context("Cannot parse TTFs")?;
        // Collect all the values in a map edge_id -> (td, tt).
        let mut global_map: HashMap<MetroId, Vec<(f64, f64)>> = HashMap::default();
        for (eid, x, y) in ttfs_vec {
            global_map.entry(eid).or_insert_with(Vec::new).push((x, y));
        }
        // Build the TTFs.
        let mut ttf_map = HashMap::with_capacity_and_hasher(global_map.len(), Default::default());
        for (eid, xy_vec) in global_map.into_iter() {
            let ttf = build_ttf(xy_vec)
                .with_context(|| format!("Failed to build TTF for edge id `{eid}`"))?;
            ttf_map.insert(eid, ttf);
        }
        check_same_start_and_interval(&ttf_map)?;
        ttf_map
    } else {
        HashMap::default()
    };
    let edge_batch = read_batch(edges_path)?;
    let mut edges = read_edges(edge_batch).context("Cannot parse edges")?;
    for edge in edges.iter_mut() {
        if let Some(ttf) = ttf_map.remove(&edge.edge_id) {
            edge.travel_time = ttf
        }
    }
    Graph::from_edges(edges)
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

fn check_same_start_and_interval(ttf_map: &HashMap<MetroId, TTF<f64>>) -> Result<()> {
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
pub fn get_node_order_from_file(path: &Path) -> Result<HashMap<MetroId, usize>> {
    let batch = read_batch(path)?;
    let order = read_node_order(batch).context("Cannot parse node ordering")?;
    Ok(order)
}

/// Reads queries from a filename.
pub fn get_queries_from_file(path: &Path) -> Result<Vec<Query>> {
    let batch = read_batch(path)?;
    let queries = read_queries(batch).context("Cannot parse queries")?;
    Ok(queries)
}

/// Reads an arrow `RecordBatch` with edges data and returns a `Vec` of `Edge`.
pub fn read_edges(batch: RecordBatch) -> Result<Vec<Edge>> {
    let mut columns = Columns::new(batch);
    let edge_ids = columns.id(&["edge_id"])?;
    let sources = columns.id(&["source"])?;
    let targets = columns.id(&["target"])?;
    let travel_times = columns.f64(&["travel_time"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut edges = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let edge_id = required(edge_ids.get(i), "edge_id")?;
        let edge = Edge {
            edge_id,
            source: required(sources.get(i), "source")?,
            target: required(targets.get(i), "target")?,
            travel_time: TTF::Constant(travel_times.get(i).unwrap_or(1.0)),
        };
        if !unique_ids.insert(edge_id) {
            bail!("Found duplicate `edge_id`: {edge_id}",);
        }
        edges.push(edge);
    }
    Ok(edges)
}

type TTFsVec = Vec<(MetroId, f64, f64)>;

/// Reads an arrow `RecordBatch` with TTFs data and returns a [TTFsVec].
fn read_ttfs(batch: RecordBatch) -> Result<TTFsVec> {
    let mut columns = Columns::new(batch);
    let edge_ids = columns.id(&["edge_id"])?;
    let departure_times = columns.f64(&["departure_time"])?;
    let travel_times = columns.f64(&["travel_time"])?;
    columns.warn_unused();
    (0..columns.len())
        .map(|i| {
            Ok((
                required(edge_ids.get(i), "edge_id")?,
                required(departure_times.get(i), "departure_time")?,
                required(travel_times.get(i), "travel_time")?,
            ))
        })
        .collect()
}

/// Reads an arrow `RecordBatch` with node ordering and returns a map with the ordering.
fn read_node_order(batch: RecordBatch) -> Result<HashMap<MetroId, usize>> {
    let mut columns = Columns::new(batch);
    let node_ids = columns.id(&["node_id"])?;
    let orders = columns.u64(&["order"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut nodes = HashMap::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let node_id = required(node_ids.get(i), "node_id")?;
        let order = required(orders.get(i), "order")? as usize;
        if nodes.insert(node_id, order).is_some() {
            bail!("Found duplicate `node_id`: {node_id}",);
        }
    }
    Ok(nodes)
}

/// Reads an arrow `RecordBatch` with queries and returns a Vec of [Query].
pub fn read_queries(batch: RecordBatch) -> Result<Vec<Query>> {
    let mut columns = Columns::new(batch);
    let query_ids = columns.id(&["query_id"])?;
    let origins = columns.id(&["origin"])?;
    let destinations = columns.id(&["destination"])?;
    let departure_times = columns.f64(&["departure_time"])?;
    columns.warn_unused();
    let n = columns.len();
    let mut queries = Vec::with_capacity(n);
    let mut unique_ids = HashSet::with_capacity_and_hasher(n, Default::default());
    for i in 0..n {
        let query_id = required(query_ids.get(i), "query_id")?;
        let origin = required(origins.get(i), "origin")?;
        let destination = required(destinations.get(i), "destination")?;
        if !unique_ids.insert(query_id) {
            bail!("Found duplicate `query_id`: {query_id}",);
        }
        queries.push(Query {
            id: query_id,
            source: origin,
            target: destination,
            departure_time: departure_times.get(i),
        });
    }
    Ok(queries)
}
