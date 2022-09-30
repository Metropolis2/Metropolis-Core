// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use crate::network::road_network::{ODPairs, RoadEdge, RoadGraph};

use petgraph::graph::{node_index, DiGraph};
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer};
use ttf::TTFNum;

impl<'de, T> Deserialize<'de> for RoadGraph<T>
where
    T: TTFNum,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let deser_graph = DeserRoadGraph::deserialize(deserializer)?;
        let graph = DiGraph::from_edges(deser_graph.edges.into_iter());
        Ok(RoadGraph::new(graph))
    }
}

#[derive(Deserialize, JsonSchema)]
#[serde(rename = "RoadGraph")]
#[serde(bound = "T: TTFNum")]
pub(crate) struct DeserRoadGraph<T> {
    /// Edges of the graph, represented as a tuple `(s, t, e)`, where `s` is the id of the source
    /// node, `t` is the id of the target node and `e` is the description of the edge.
    #[validate(length(min = 1))]
    edges: Vec<(u32, u32, RoadEdge<T>)>,
}

#[derive(Deserialize, JsonSchema)]
#[serde(rename = "ODPairs")]
pub(crate) struct DeserODPairs {
    /// Origin-destination pairs represented as tuples `(o, d)`, where `o` is the id of the origin
    /// node and `d` is the id of the destination node.
    pairs: Vec<(usize, usize)>,
}

impl From<DeserODPairs> for ODPairs {
    fn from(raw_pairs: DeserODPairs) -> Self {
        let pairs: Vec<_> = raw_pairs
            .pairs
            .into_iter()
            .map(|p| (node_index(p.0), node_index(p.1)))
            .collect();
        ODPairs::from_vec(pairs)
    }
}
