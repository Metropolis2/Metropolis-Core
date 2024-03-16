// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use serde::{Deserialize, Deserializer};
use ttf::TTFNum;

use crate::network::road_network::{OriginalNodeId, RoadEdge, RoadGraph};

impl<'de, T> Deserialize<'de> for RoadGraph<T>
where
    T: TTFNum,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let deser_graph = DeserRoadGraph::deserialize(deserializer)?;
        Ok(RoadGraph::from_edges(deser_graph.edges))
    }
}

#[derive(Deserialize)]
#[serde(rename = "RoadGraph")]
#[serde(bound = "T: TTFNum")]
pub(crate) struct DeserRoadGraph<T> {
    /// Edges of the graph, represented as a tuple `(s, t, e)`, where `s` is the id of the source
    /// node, `t` is the id of the target node and `e` is the description of the edge.
    edges: Vec<(OriginalNodeId, OriginalNodeId, RoadEdge<T>)>,
}
