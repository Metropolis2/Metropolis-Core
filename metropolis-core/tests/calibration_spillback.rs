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

//! Integration test for the road-capacity calibration with spillback: the target delays are
//! simulated with known capacities, which the calibration must recover.
mod common;
use common::*;

#[test]
fn calibration_spillback_test() {
    // The edges hold 3 vehicles: the agents going to 2 queue at `B` on `A`, which gets full, so the
    // agents going to 1 also wait for space at the entry of `A` (the largest delay of these agents
    // is 38 s without spillback).
    init_simulation(true, 3.0);
    let target_routes = simulated_target_routes();
    let max_delay_1 = max_delay(&target_routes, 1);
    assert!(max_delay_1 > 60., "{max_delay_1}");

    // From the true capacities, the surrogate model reproduces the simulated delays exactly (with
    // the recorded release times of the vehicles that waited for space), so the capacities do not
    // change.
    let capacities = calibrate(TRUE_CAPACITIES, "", &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-6, "{capacities:?}");
    }

    // From a wrong guess, the true capacities are recovered.
    let capacities = calibrate([0.4, 0.18], "", &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-3, "{capacities:?}");
    }
}
