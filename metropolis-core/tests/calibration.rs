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
use metropolis_core::calibration::parameters::CapacityCalibrationParameters;

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
    let params: CapacityCalibrationParameters = serde_json::from_str(
        r#"{"capacities": {"A": 0.4, "B": 0.18}, "warmup_days": 3, "stopping": {"max_days": 4}}"#,
    )
    .unwrap();
    let results = metropolis_core::calibration::calibrate(&params, target_routes.clone()).unwrap();
    let mut capacities: Vec<_> = results
        .capacities
        .iter()
        .map(|(id, c)| (id.unwrap().to_string(), f64::from(*c)))
        .collect();
    capacities.sort_by(|a, b| a.0.cmp(&b.0));
    assert_eq!(
        capacities,
        vec![("A".to_owned(), 0.4), ("B".to_owned(), 0.18)]
    );
    // The capacities are still optimized after the last day, towards the true capacities.
    for (id, c) in results.next_capacities.iter() {
        let c = f64::from(*c);
        match id.unwrap().to_string().as_str() {
            "A" => assert!(c > 0.4, "{c}"),
            _ => assert!(c < 0.18, "{c}"),
        }
    }
}
