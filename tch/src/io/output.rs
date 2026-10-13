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

//! Conversion of the outputs of the routing tool to arrow format.

use anyhow::Result;
use arrow::array::{Float64Builder, ListBuilder, RecordBatch, UInt64Builder};
use metro_io::write::{finish_batch, IdBuilder, ToArrow};
use ttf::TTF;

use crate::hash::HashMap;
use crate::tools::{MetroId, QueryResult};

/// Node ordering of a graph, as a map node id -> order.
#[derive(Debug)]
pub(crate) struct NodeOrder<'a>(pub(crate) &'a HashMap<MetroId, usize>);

impl ToArrow for NodeOrder<'_> {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 1]> {
        let mut node_id = IdBuilder::default();
        let mut order = UInt64Builder::default();
        for (id, ord) in self.0.iter() {
            node_id.append_value(*id);
            order.append_value(*ord as u64);
        }
        Ok([finish_batch(vec![
            ("node_id", &mut node_id, false),
            ("order", &mut order, false),
        ])?])
    }
    fn names() -> [&'static str; 1] {
        ["node_order"]
    }
}

/// Results of a set of queries.
#[derive(Debug)]
pub(crate) struct QueryResults<'a>(pub(crate) &'a [QueryResult]);

impl ToArrow<2> for QueryResults<'_> {
    fn to_arrow(&self) -> Result<[Option<RecordBatch>; 2]> {
        let mut builder = QueryResultBuilder::default();
        for res in self.0.iter() {
            builder.append(res);
        }
        builder.finish()
    }
    fn names() -> [&'static str; 2] {
        ["ea_results", "profile_results"]
    }
}

#[derive(Debug, Default)]
struct QueryResultBuilder {
    ea_query_id: IdBuilder,
    ea_arrival_time: Float64Builder,
    ea_route: ListBuilder<IdBuilder>,
    profile_query_id: IdBuilder,
    profile_departure_time: Float64Builder,
    profile_travel_time: Float64Builder,
}

impl QueryResultBuilder {
    fn append(&mut self, res: &QueryResult) {
        match res {
            QueryResult::EarliestArrival((query_id, maybe_ta, maybe_route)) => {
                self.ea_query_id.append_value(*query_id);
                if let Some(ta) = maybe_ta {
                    self.ea_arrival_time.append_value(*ta);
                    if let Some(route) = maybe_route {
                        self.ea_route.append_value(route.iter().copied().map(Some));
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

    fn finish(&mut self) -> Result<[Option<RecordBatch>; 2]> {
        let ea_batch = finish_batch(vec![
            ("query_id", &mut self.ea_query_id, false),
            ("arrival_time", &mut self.ea_arrival_time, true),
            ("route", &mut self.ea_route, true),
        ])?;
        let profile_batch = finish_batch(vec![
            ("query_id", &mut self.profile_query_id, false),
            ("departure_time", &mut self.profile_departure_time, true),
            ("travel_time", &mut self.profile_travel_time, true),
        ])?;
        Ok([ea_batch, profile_batch])
    }
}
