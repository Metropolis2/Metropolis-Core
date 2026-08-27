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

//! Cache of the contraction-hierarchy node orders, so that they can be re-used from one iteration
//! of the simulation to the next one.
//!
//! Building a [HierarchyOverlay] with [HierarchyOverlay::order] both computes a node order and
//! contracts the nodes in that order. Computing the node order is the expensive part: it simulates
//! the contraction of every node to estimate how attractive it is to contract.
//!
//! The topology of the road network never changes during a simulation, only the travel-time
//! functions of the edges do. A node order computed at some iteration thus remains valid for the
//! whole simulation; it only becomes a *worse* order (i.e., it yields a denser hierarchy) as
//! congestion drifts away from the congestion it was computed for.
//!
//! During the first iterations, congestion usually varies a lot from one iteration to the next one,
//! so re-computing the node order is worth it. Later on, the learning model damps the day-to-day
//! variations and the node order can be re-used, which allows the (much cheaper)
//! [HierarchyOverlay::construct] to be used instead.
//!
//! How much drift is tolerated is set by the `node_order_reuse_threshold` parameter. Even with its
//! default value of zero, a node order is re-used when the expected travel times did not change at
//! all since it was computed, as re-computing it would then yield the very same order. This is
//! notably the case for the first iteration whenever no road-network conditions file is given: the
//! cache is seeded during the pre-processing, which builds a contraction hierarchy for the
//! free-flow travel times, and the initial conditions are then those very travel times.
use num_traits::ConstZero;
use tch::HierarchyOverlay;

use super::preprocess::UniqueVehicleIndex;
use super::weights::RoadNetworkWeights;
use crate::units::*;

/// Node order of a [HierarchyOverlay], together with how much the expected travel times drifted
/// since it was computed.
#[derive(Clone, Debug)]
pub(crate) struct CachedNodeOrder {
    /// Order of the nodes in the hierarchy, indexed by `NodeIndex::index`, as returned by
    /// [HierarchyOverlay::get_order].
    order: Vec<usize>,
    /// Complexity of the hierarchy that was built when the node order was computed.
    ///
    /// This is only used to report how much the hierarchy degrades when the node order is re-used.
    reference_complexity: usize,
    /// Upper bound on the change in the expected travel-time functions since the node order was
    /// computed.
    ///
    /// This is the sum of the root mean squared differences between the expected travel-time
    /// functions of two consecutive iterations. As the root mean squared difference is a norm, the
    /// triangle inequality guarantees that this sum is an upper bound of the actual difference
    /// with the travel-time functions the node order was computed for.
    drift: NonNegativeSeconds,
}

/// Node orders of the [HierarchyOverlay] of each unique vehicle, re-used from one iteration of the
/// simulation to the next one.
#[derive(Clone, Debug, Default)]
pub struct NodeOrderCache {
    /// Cached node order of each unique vehicle, indexed by [UniqueVehicleIndex].
    entries: Vec<Option<CachedNodeOrder>>,
}

impl NodeOrderCache {
    /// Returns `true` if no node order is cached.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.iter().all(Option::is_none)
    }

    /// Returns the node order to be re-used for the given unique vehicle, if any.
    ///
    /// Returns `None` if no node order was cached for this unique vehicle or if the expected
    /// travel times drifted by more than the given threshold since the node order was computed.
    /// In that case, a new node order must be computed and stored with
    /// [NodeOrderCache::store].
    ///
    /// With a threshold of zero, the node order is only re-used if the expected travel times did
    /// not change at all since it was computed. Re-computing the node order would then yield the
    /// very same order, so re-using it is free of any cost in quality.
    pub(crate) fn get(
        &self,
        uvehicle_id: UniqueVehicleIndex,
        threshold: NonNegativeSeconds,
    ) -> Option<&CachedNodeOrder> {
        let entry = self.entries.get(uvehicle_id.index())?.as_ref()?;
        (entry.drift <= threshold).then_some(entry)
    }

    /// Stores the node order of the given hierarchy for the given unique vehicle and resets its
    /// drift.
    pub(crate) fn store(
        &mut self,
        uvehicle_id: UniqueVehicleIndex,
        hierarchy: &HierarchyOverlay<AnySeconds>,
    ) {
        if self.entries.len() <= uvehicle_id.index() {
            self.entries.resize(uvehicle_id.index() + 1, None);
        }
        self.entries[uvehicle_id.index()] = Some(CachedNodeOrder {
            order: hierarchy.get_order().to_vec(),
            reference_complexity: hierarchy.complexity(),
            drift: NonNegativeSeconds::ZERO,
        });
    }

    /// Increases the drift of all the cached node orders by the change in the expected travel-time
    /// functions between two consecutive iterations.
    ///
    /// The node orders that drifted by more than the given threshold are discarded, as they will
    /// never be re-used: the drift can only increase.
    pub(crate) fn add_drift(
        &mut self,
        weights: &RoadNetworkWeights,
        new_weights: &RoadNetworkWeights,
        threshold: NonNegativeSeconds,
    ) {
        if self.is_empty() {
            // No node order is cached: there is nothing to update.
            return;
        }
        for (entry_opt, rmse) in self
            .entries
            .iter_mut()
            .zip(weights.rmse_per_vehicle(new_weights))
        {
            if let Some(entry) = entry_opt {
                entry.drift += rmse;
                if entry.drift > threshold {
                    *entry_opt = None;
                }
            }
        }
    }
}

impl CachedNodeOrder {
    /// Returns the order of the nodes in the hierarchy, indexed by `NodeIndex::index`.
    pub(crate) fn order(&self) -> &[usize] {
        &self.order
    }

    /// Returns the complexity of the hierarchy that was built when the node order was computed.
    pub(crate) fn reference_complexity(&self) -> usize {
        self.reference_complexity
    }

    /// Returns the upper bound on the change in the expected travel-time functions since the node
    /// order was computed.
    pub(crate) fn drift(&self) -> NonNegativeSeconds {
        self.drift
    }
}
