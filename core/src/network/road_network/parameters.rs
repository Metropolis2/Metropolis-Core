// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Parameters related to the road network.
use anyhow::{bail, Result};
use num_traits::ConstZero;
use serde_derive::Deserialize;

use tch::ContractionParameters;

use crate::units::*;

fn read_global() -> &'static RoadNetworkParameters {
    crate::parameters::road_network()
}

pub(crate) fn contraction() -> &'static ContractionParameters {
    &read_global().contraction
}

pub(crate) fn recording_interval() -> PositiveSeconds {
    read_global().recording_interval
}

pub(crate) fn approximation_bound() -> NonNegativeSeconds {
    read_global().approximation_bound
}

pub(crate) fn spillback() -> bool {
    read_global().spillback
}

pub(crate) fn backward_wave_speed() -> Option<MetersPerSecond> {
    read_global().backward_wave_speed
}

pub(crate) fn max_pending_duration() -> NonNegativeSeconds {
    read_global().max_pending_duration
}

pub(crate) fn constrain_inflow() -> bool {
    read_global().constrain_inflow
}

pub(crate) fn algorithm_type() -> AlgorithmType {
    read_global().algorithm_type
}

const fn default_is_true() -> bool {
    true
}

/// Set of parameters related to a [RoadNetwork].
#[derive(Clone, Debug, Deserialize)]
pub struct RoadNetworkParameters {
    /// [ContractionParameters] controlling how a [HierarchyOverlay] is built from a [RoadNetwork].
    #[serde(default)]
    pub contraction: ContractionParameters,
    /// Time interval for which travel times are recorded at the edge level during the simulation.
    pub recording_interval: PositiveSeconds,
    #[serde(default)]
    /// Approximation bound in seconds, used to simplify the travel-time functions when the
    /// difference between the maximum and the minimum travel time is smaller than this bound.
    pub approximation_bound: NonNegativeSeconds,
    /// If `true` the total headways of vehicles on each edge of the road network is limited by the
    /// total length of the edges.
    #[serde(default = "default_is_true")]
    pub spillback: bool,
    /// Speed at which the holes created by a vehicle leaving an edge are propagating backward.
    ///
    /// By default, the holes propagate instantaneously.
    pub backward_wave_speed: Option<MetersPerSecond>,
    /// Maximum amount of time a vehicle can be pending to enter the next edge.
    #[serde(default)]
    pub max_pending_duration: NonNegativeSeconds,
    /// If `true` (default), the inflow of vehicles entering an edge is limiting by the edge's flow
    /// capacity.
    /// If `false`, only the edge's outflow is limited by its capacity.
    #[serde(default = "default_is_true")]
    pub constrain_inflow: bool,
    /// Algorithm type to use when computing the origin-destination travel-time functions.
    /// Possible values are: "Best" (default), "Intersect" and "TCH".
    ///
    /// Intersect is recommended when the number of unique origins and destinations represent a
    /// relatively small part of the total number of nodes in the graph.
    #[serde(default)]
    pub algorithm_type: AlgorithmType,
}

impl Default for RoadNetworkParameters {
    fn default() -> Self {
        Self {
            contraction: Default::default(),
            recording_interval: PositiveSeconds::new_unchecked(1.0),
            approximation_bound: Default::default(),
            spillback: false,
            backward_wave_speed: None,
            max_pending_duration: NonNegativeSeconds::ZERO,
            constrain_inflow: true,
            algorithm_type: AlgorithmType::Best,
        }
    }
}

impl RoadNetworkParameters {
    pub(crate) fn check_validity(&self) -> Result<()> {
        if self.spillback && !self.max_pending_duration.is_positive() {
            bail!(
                "The parameter `max_pending_duration` must be set to a positive value when \
                spillback is enabled."
            );
        }
        Ok(())
    }
}

/// Algorithm type to use for the profile queries.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Deserialize)]
pub enum AlgorithmType {
    /// Try to guess which algorithm will be the fastest.
    #[default]
    Best,
    /// Time-dependent contraction hierarchies (TCH): long pre-processing time, fast queries.
    #[serde(rename = "TCH")]
    Tch,
    /// Many-to-many TCH: Longest pre-processing time, fastest queries.
    Intersect,
}
