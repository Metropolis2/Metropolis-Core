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

//! Integration test for the road-capacity calibration: the target delays are simulated with known
//! capacities, which the calibration must recover.
use metropolis_core::units::MetroId;

mod common;
use common::*;

#[test]
fn calibration_test() {
    init_simulation(false, 1.0);
    let target_routes = simulated_target_routes();
    // The agents queue at `A` and those going to 2 also queue at `B` (the largest delay at `A` is
    // 39 s, for the last agent).
    assert_eq!(max_delay(&target_routes, 1), 38.);
    let max_delay_2 = max_delay(&target_routes, 2);
    assert!(max_delay_2 > 60., "{max_delay_2}");

    // From the true capacities, the surrogate model reproduces the simulated delays exactly, so the
    // capacities do not change.
    let capacities = calibrate(TRUE_CAPACITIES, "", &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-6, "{capacities:?}");
    }

    // From a wrong guess, the true capacities are recovered.
    let capacities = calibrate([0.4, 0.18], "", &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-3, "{capacities:?}");
    }

    // Same with the surrogate models of the last 3 days (the agents have a single route, so the days
    // only differ by their capacities).
    let capacities = calibrate([0.4, 0.18], r#", "surrogate_days": 3"#, &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-3, "{capacities:?}");
    }

    // Same after warm-up days (with smaller trust regions, as the learning weight decreases).
    let capacities = calibrate([0.4, 0.18], r#", "warmup_days": 3"#, &target_routes);
    for (c, t) in capacities.iter().zip(TRUE_CAPACITIES) {
        assert!((c / t - 1.).abs() < 1e-3, "{capacities:?}");
    }

    // With warm-up days and a single other day, the initial capacities are returned.
    let results = calibrate_factors(
        &[(0, "A"), (1, "B")],
        r#"{"A": 0.4, "B": 0.18}"#,
        r#", "warmup_days": 3, "stopping": {"max_days": 4}"#,
        &target_routes,
    );
    assert_eq!(
        sorted(&results.factors),
        vec![("A".to_owned(), 0.4), ("B".to_owned(), 0.18)]
    );
    // The capacities are still optimized after the last day, towards the true capacities.
    for (id, f) in sorted(&results.next_factors) {
        match id.as_str() {
            "A" => assert!(f > 0.4, "{f}"),
            _ => assert!(f < 0.18, "{f}"),
        }
    }

    // A factor shared by the two edges (`road`) and a factor of `B` only (`narrow`): the true values
    // are 0.5 and 0.3 (0.15 / 0.5). The vehicles reach `B` at half the capacity of `A` at most, so
    // `B` has a queue only with `narrow` below 0.5 (above, the delays do not depend on it).
    let edge_factors = [(0, "road"), (1, "road"), (1, "narrow")];
    let results = calibrate_factors(
        &edge_factors,
        r#"{"road": 0.8, "narrow": 0.45}"#,
        "",
        &target_routes,
    );
    let factors = sorted(&results.factors);
    for ((_, f), t) in factors.iter().zip([0.3, 0.5]) {
        assert!((f / t - 1.).abs() < 1e-3, "{factors:?}");
    }
    // The capacity of each edge is the product of its factors.
    for &(id, capacity, flow) in results.edge_capacities.iter() {
        let expected = match id {
            MetroId::Integer(0) => factors[1].1,
            _ => factors[0].1 * factors[1].1,
        };
        assert!((f64::from(capacity) - expected).abs() < 1e-12);
        assert_eq!(f64::from(flow), f64::from(capacity));
    }
    // With a minimum of 0.4 for `narrow`, it stops at that bound, and `road` goes below its true
    // value to make up for the too large capacity of `B`.
    let results = calibrate_factors(
        &edge_factors,
        r#"{"road": 0.8, "narrow": {"initial": 0.45, "min": 0.4}}"#,
        "",
        &target_routes,
    );
    let factors = sorted(&results.factors);
    assert!((factors[0].1 - 0.4).abs() < 1e-12, "{factors:?}");
    assert!(factors[1].1 < 0.5, "{factors:?}");
}
