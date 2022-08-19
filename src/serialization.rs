use crate::network::road_network::{RoadEdge, RoadGraph};

use petgraph::graph::DiGraph;
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
