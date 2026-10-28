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
///
/// With spillback, it also stores the release time of each vehicle that waited for space on the
/// edge (the time at which the edge stopped being full for it, or at which it was forced to enter).
#[derive(Clone, Debug, Default)]
pub(crate) struct ArrivalCurve {
    /// Arrival times, non-decreasing (the vehicles arriving at the same time have one entry each).
    times: Vec<NonNegativeSeconds>,
    /// PCE of the vehicle arrived at `times[i]`.
    pce: Vec<PCE>,
    /// Index (in the arrival order) and release time of each vehicle that waited for space, by
    /// increasing index.
    releases: Vec<(usize, NonNegativeSeconds)>,
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

    /// Records the release of the vehicle with the given index (in the arrival order), which waited
    /// for space on the edge, at the given time.
    ///
    /// The releases must be recorded by increasing index.
    pub(crate) fn push_release(&mut self, index: usize, time: NonNegativeSeconds) {
        debug_assert!(index < self.times.len());
        debug_assert!(time >= self.times[index]);
        debug_assert!(self.releases.last().is_none_or(|&(i, _)| i < index));
        self.releases.push((index, time));
    }

    /// Returns the arrival times of the curve (non-decreasing).
    pub(crate) fn times(&self) -> &[NonNegativeSeconds] {
        &self.times
    }

    /// Returns the PCE of the vehicle arrived at each arrival time.
    pub(crate) fn pce(&self) -> &[PCE] {
        &self.pce
    }

    /// Returns the index (in the arrival order) and release time of each vehicle that waited for
    /// space on the edge, by increasing index.
    pub(crate) fn releases(&self) -> &[(usize, NonNegativeSeconds)] {
        &self.releases
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
        self.releases.shrink_to_fit();
    }
}

/// Arrival curve at the entry bottleneck of each edge (`None` if the arrivals were not recorded),
/// indexed by `EdgeIndex`.
#[derive(Clone, Debug, Default)]
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
    /// Logs the number of curves, number of points, total PCE, number of vehicles that waited for
    /// space and memory size of the curves.
    pub(crate) fn log_summary(&self) {
        let curves: Vec<_> = self.0.iter().flatten().collect();
        let nb_points: usize = curves.iter().map(|c| c.len()).sum();
        let nb_releases: usize = curves.iter().map(|c| c.releases.len()).sum();
        let total_pce: f64 = curves.iter().map(|c| f64::from(c.total_pce())).sum();
        let point_size = size_of::<NonNegativeSeconds>() + size_of::<PCE>();
        let release_size = size_of::<(usize, NonNegativeSeconds)>();
        let memory = (nb_points * point_size + nb_releases * release_size) as f64 / 1e6;
        info!(
            "Recorded arrival curves at {} edges: {nb_points} arrivals, \
            {total_pce:.0} PCE, {nb_releases} waited for space, {memory:.1} MB",
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
        assert!(curve.releases().is_empty());
        curve.push_release(1, s(14.));
        curve.push_release(3, s(15.));
        assert_eq!(curve.releases(), &[(1, s(14.)), (3, s(15.))]);
    }
}
