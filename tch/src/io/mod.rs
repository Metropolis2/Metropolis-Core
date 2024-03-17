// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to import / export of simulation data.

mod arrow;
pub mod csv;
pub mod json;
pub mod parquet;

pub use arrow::{get_graph_from_files, get_node_order_from_file, get_queries_from_file};
pub use json::get_parameters_from_json;
