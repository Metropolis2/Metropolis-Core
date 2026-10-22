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

use crate::units::*;

/// Arrival curve at a bottleneck: arrival time and PCE of each vehicle that has reached the
/// bottleneck, in the order in which the vehicles reached it.
#[derive(Clone, Debug, Default)]
pub(crate) struct ArrivalCurve {
    /// Arrival times, non-decreasing (the vehicles arriving at the same time have one entry each).
    times: Vec<NonNegativeSeconds>,
    /// PCE of the vehicle arrived at `times[i]`.
    pce: Vec<PCE>,
}

impl ArrivalCurve {
    /// Records the arrival of a vehicle with the given PCE at the given time.
    ///
    /// The arrivals must be recorded in chronological order.
    pub(crate) fn push(&mut self, time: NonNegativeSeconds, pce: PCE) {
        debug_assert!(self.times.last().is_none_or(|&t| t <= time));
        self.times.push(time);
        self.pce.push(pce);
    }

    /// Returns the arrival times of the curve (non-decreasing).
    pub(crate) fn times(&self) -> &[NonNegativeSeconds] {
        &self.times
    }

    /// Returns the PCE of the vehicle arrived at each arrival time.
    pub(crate) fn pce(&self) -> &[PCE] {
        &self.pce
    }

    /// Returns the number of points of the curve (i.e., the number of vehicles recorded).
    pub(crate) fn len(&self) -> usize {
        self.times.len()
    }

    /// Returns the total PCE of the vehicles recorded.
    pub(crate) fn total_pce(&self) -> PCE {
        self.pce.iter().copied().sum()
    }

    /// Shrinks the capacity of the curve as much as possible.
    pub(crate) fn shrink_to_fit(&mut self) {
        self.times.shrink_to_fit();
        self.pce.shrink_to_fit();
    }
}

/// Arrival curve at the entry bottleneck of each edge (`None` if the arrivals were not recorded),
/// indexed by `EdgeIndex`.
#[derive(Clone, Debug)]
pub(crate) struct ArrivalCurves(Vec<Option<ArrivalCurve>>);

impl FromIterator<Option<ArrivalCurve>> for ArrivalCurves {
    fn from_iter<I: IntoIterator<Item = Option<ArrivalCurve>>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for ArrivalCurves {
    type Item = Option<ArrivalCurve>;
    type IntoIter = std::vec::IntoIter<Option<ArrivalCurve>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl ArrivalCurves {
    /// Logs the number of curves, number of points, total PCE and memory size of the curves.
    pub(crate) fn log_summary(&self) {
        let curves: Vec<_> = self.0.iter().flatten().collect();
        let nb_points: usize = curves.iter().map(|c| c.len()).sum();
        let total_pce: f64 = curves.iter().map(|c| f64::from(c.total_pce())).sum();
        let point_size = size_of::<NonNegativeSeconds>() + size_of::<PCE>();
        let memory = (nb_points * point_size) as f64 / 1e6;
        info!(
            "Recorded arrival curves at {} edges: {nb_points} arrivals, \
            {total_pce:.0} PCE, {memory:.1} MB",
            curves.len(),
        );
    }
}

#[cfg(test)]
mod tests {
    use num_traits::ConstZero;

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
        // Arrivals at the same time are kept separate.
        curve.push(s(12.), pce(0.5));
        curve.push(s(15.), pce(1.));
        assert_eq!(curve.len(), 4);
        assert_eq!(curve.times, vec![s(10.), s(12.), s(12.), s(15.)]);
        assert_eq!(curve.pce, vec![pce(1.), pce(2.), pce(0.5), pce(1.)]);
        assert_eq!(curve.total_pce(), pce(4.5));
    }
}
