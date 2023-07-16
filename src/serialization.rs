// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use hashbrown::HashMap;
use petgraph::{
    graph::{node_index, DiGraph},
    prelude::NodeIndex,
};
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer};
use ttf::TTFNum;

use crate::network::road_network::{RoadEdge, RoadGraph};

impl<'de, T> Deserialize<'de> for RoadGraph<T>
where
    T: TTFNum,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let deser_graph = DeserRoadGraph::deserialize(deserializer)?;
        // The nodes in the DiGraph need to be ordered from 0 to n-1 so we create a map u64 ->
        // NodeIndex to re-index the nodes.
        let node_map: HashMap<u64, NodeIndex> = deser_graph
            .edges
            .iter()
            .map(|(s, _, _)| s)
            .chain(deser_graph.edges.iter().map(|(_, t, _)| t))
            .enumerate()
            .map(|(idx, &id)| (id, node_index(idx)))
            .collect();
        let edges: Vec<_> = deser_graph
            .edges
            .into_iter()
            .map(|(s, t, e)| (node_map[&s], node_map[&t], e))
            .collect();
        let graph = DiGraph::from_edges(edges);
        Ok(RoadGraph::new(graph, node_map))
    }
}

#[derive(Deserialize, JsonSchema)]
#[serde(rename = "RoadGraph")]
#[serde(bound = "T: TTFNum")]
pub(crate) struct DeserRoadGraph<T> {
    /// Edges of the graph, represented as a tuple `(s, t, e)`, where `s` is the id of the source
    /// node, `t` is the id of the target node and `e` is the description of the edge.
    #[validate(length(min = 1))]
    edges: Vec<(u64, u64, RoadEdge<T>)>,
}
