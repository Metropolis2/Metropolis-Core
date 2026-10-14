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

//! Cumulative arrival curves recorded at the edge-entry bottlenecks during the within-day model.
use log::info;
use num_traits::ConstZero;
use petgraph::graph::EdgeIndex;

use crate::units::*;

/// Cumulative arrival curve at a bottleneck: total PCE of the vehicles that have reached the
/// bottleneck by each time.
#[derive(Clone, Debug, Default)]
pub(crate) struct ArrivalCurve {
    /// Arrival times, strictly increasing (vehicles arriving at the same time are merged).
    times: Vec<NonNegativeSeconds>,
    /// Total PCE of the vehicles arrived up to `times[i]` (included).
    cumulative_pce: Vec<PCE>,
}

impl ArrivalCurve {
    /// Records the arrival of a vehicle with the given PCE at the given time.
    ///
    /// The arrivals must be recorded in chronological order.
    pub(crate) fn push(&mut self, time: NonNegativeSeconds, pce: PCE) {
        match self.times.last() {
            Some(&last_time) if last_time == time => {
                *self.cumulative_pce.last_mut().unwrap() += pce;
            }
            last_time_opt => {
                debug_assert!(last_time_opt.is_none_or(|&t| t < time));
                self.times.push(time);
                self.cumulative_pce.push(self.total_pce() + pce);
            }
        }
    }

    /// Returns the number of points of the curve (i.e., the number of distinct arrival times).
    pub(crate) fn len(&self) -> usize {
        self.times.len()
    }

    /// Returns the total PCE of the vehicles recorded.
    pub(crate) fn total_pce(&self) -> PCE {
        self.cumulative_pce.last().copied().unwrap_or(PCE::ZERO)
    }

    /// Shrinks the capacity of the curve as much as possible.
    pub(crate) fn shrink_to_fit(&mut self) {
        self.times.shrink_to_fit();
        self.cumulative_pce.shrink_to_fit();
    }
}

/// Arrival curve at the entry bottleneck of each edge (`None` if the arrivals were not recorded),
/// indexed by `EdgeIndex`.
#[derive(Clone, Debug)]
pub(crate) struct ArrivalCurves(pub(super) Vec<Option<ArrivalCurve>>);

impl ArrivalCurves {
    /// Returns the arrival curve at the entry of the given edge (`None` if the arrivals were not
    /// recorded).
    pub(crate) fn get(&self, edge: EdgeIndex) -> Option<&ArrivalCurve> {
        self.0[edge.index()].as_ref()
    }

    /// Logs the number of curves, number of points, total PCE and memory size of the curves.
    pub(crate) fn log_summary(&self) {
        let curves: Vec<_> = self.0.iter().flatten().collect();
        let nb_points: usize = curves.iter().map(|c| c.len()).sum();
        let total_pce: f64 = curves.iter().map(|c| f64::from(c.total_pce())).sum();
        let point_size = size_of::<NonNegativeSeconds>() + size_of::<PCE>();
        let memory = (nb_points * point_size) as f64 / 1e6;
        info!(
            "Recorded arrival curves at {} edges: {nb_points} distinct arrival times, \
            {total_pce:.0} PCE, {memory:.1} MB",
            curves.len(),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(t: f64) -> NonNegativeSeconds {
        NonNegativeSeconds::new_unchecked(t)
    }

    fn pce(v: f64) -> PCE {
        PCE::new_unchecked(v)
    }

    #[test]
    fn push_test() {
        let mut curve = ArrivalCurve::default();
        assert_eq!(curve.len(), 0);
        assert_eq!(curve.total_pce(), PCE::ZERO);
        curve.push(s(10.), pce(1.));
        curve.push(s(12.), pce(2.));
        // Arrivals at the same time are merged.
        curve.push(s(12.), pce(0.5));
        curve.push(s(15.), pce(1.));
        assert_eq!(curve.len(), 3);
        assert_eq!(curve.times, vec![s(10.), s(12.), s(15.)]);
        assert_eq!(curve.cumulative_pce, vec![pce(1.), pce(3.5), pce(4.5)]);
        assert_eq!(curve.total_pce(), pce(4.5));
    }
}
