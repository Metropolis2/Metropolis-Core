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

//! Optimization of the capacities of the categories: least squares of the predicted delays of the
//! target routes (surrogate model) minus their target delays, plus an optional penalty on the
//! capacities, with the Levenberg–Marquardt algorithm, within bounds.
use std::time::Instant;

use log::info;
use rayon::prelude::*;

use super::parameters::OptimizerParameters;
use super::surrogate::MeanSurrogate;
use super::EdgeCategories;
use crate::units::*;

/// Initial damping factor of the Levenberg–Marquardt algorithm (the damping matrix is this factor
/// times the diagonal of the Gauss–Newton matrix).
const INITIAL_DAMPING: f64 = 1e-3;

/// Number of rows of the Jacobian matrix summed by each task when computing the normal equations
/// (the partial sums are added in a fixed order, so the results do not depend on the threads).
const BLOCK_SIZE: usize = 1024;

/// Returns the optimized capacity of each category, starting from the given capacities (those of
/// the last simulated day), on the mean of the delays predicted by the surrogate models of the last
/// simulated days.
///
/// The capacities are bounded by the minimum and maximum capacities of their category (if any) and
/// by the trust region around their initial value (maximum relative change, between 0 and 1). The
/// variables of the optimization are the capacities relative to their initial value.
///
/// The objective is the mean squared error of the delays plus the penalty `λ·Σₖ (cₖ / cₖ⁰)²`, where
/// `cₖ⁰` is the initial capacity of category `k` in the parameters (the same in every
/// optimization). The penalty is one residual per category, linear in the variables.
pub(super) fn optimize_capacities(
    surrogate: &mut MeanSurrogate,
    target_delays: &[NonNegativeSeconds],
    capacities: &[FlowPerLane],
    trust_region: f64,
    params: &OptimizerParameters,
    categories: &EdgeCategories,
) -> Vec<FlowPerLane> {
    // Bounds of the categories relative to the initial capacities.
    let ratios = |bounds: &[Option<FlowPerLane>]| -> Vec<Option<f64>> {
        bounds
            .iter()
            .zip(capacities)
            .map(|(b, &c)| b.map(|b| f64::from(b) / f64::from(c)))
            .collect()
    };
    let min_ratios = ratios(&categories.min_capacities);
    let max_ratios = ratios(&categories.max_capacities);
    let lower: Vec<f64> = min_ratios
        .iter()
        .map(|r| r.map_or(1. - trust_region, |r| r.max(1. - trust_region)))
        .collect();
    let upper: Vec<f64> = max_ratios
        .iter()
        .map(|r| r.map_or(1. + trust_region, |r| r.min(1. + trust_region)))
        .collect();
    // The capacities are clamped to the bounds of their category, so that a capacity at a bound is
    // exactly the bound (and stays within the bounds in the next optimization), despite rounding.
    let to_capacities = |x: &[f64]| -> Vec<FlowPerLane> {
        x.iter()
            .zip(capacities)
            .zip(
                categories
                    .min_capacities
                    .iter()
                    .zip(&categories.max_capacities),
            )
            .map(|((&x, &c), (min, max))| {
                let mut c = x * f64::from(c);
                if let Some(min) = min {
                    c = c.max(f64::from(*min));
                }
                if let Some(max) = max {
                    c = c.min(f64::from(*max));
                }
                FlowPerLane::new_unchecked(c)
            })
            .collect()
    };
    let scales: Vec<f64> = capacities.iter().map(|&c| f64::from(c)).collect();
    let weights = penalty_weights(
        params.penalty,
        target_delays.len(),
        capacities,
        &categories.initial_capacities,
        &surrogate.crossed_categories(),
    );
    let nb_categories = capacities.len();
    let evaluate = |x: &[f64]| {
        let (delays, mut jacobian) = surrogate.predict_with_jacobian(&to_capacities(x));
        let mut residuals: Vec<f64> = delays
            .iter()
            .zip(target_delays)
            .map(|(&p, &t)| f64::from(p) - f64::from(t))
            .collect();
        // Derivatives with respect to the relative capacities.
        jacobian.par_chunks_mut(scales.len()).for_each(|row| {
            row.iter_mut().zip(&scales).for_each(|(d, s)| *d *= s);
        });
        for (j, (&w, &x)) in weights.iter().zip(x).enumerate() {
            residuals.push(w * x);
            jacobian.extend((0..nb_categories).map(|i| if i == j { w } else { 0. }));
        }
        (residuals, jacobian)
    };
    info!("Optimizing the capacities");
    let start = Instant::now();
    let solution = levenberg_marquardt(
        evaluate,
        &lower,
        &upper,
        vec![1.; capacities.len()],
        params.max_iterations,
        params.step_tolerance,
    );
    let delay_residuals = &solution.residuals[..target_delays.len()];
    let penalty = if weights.is_empty() {
        String::new()
    } else {
        // The penalty is the sum of the squared penalty residuals divided by `N` (see
        // `penalty_weights`).
        let penalty_residuals = &solution.residuals[target_delays.len()..];
        let penalty = 2. * half_sum_of_squares(penalty_residuals) / target_delays.len() as f64;
        format!(", penalty {penalty:.4} s²")
    };
    let termination = match solution.termination {
        Termination::Stationary => "stationary point",
        Termination::StepTolerance => "step below the tolerance",
        Termination::MaxIterations => "maximum number of iterations",
    };
    info!(
        "Optimization of the capacities stopped ({termination}) after {} iterations ({:.1} s): \
        RMSE of the delays {:.3} s{penalty}",
        solution.nb_iterations,
        start.elapsed().as_secs_f64(),
        rmse(half_sum_of_squares(delay_residuals), delay_residuals.len()),
    );
    let optimized = to_capacities(&solution.x);
    for (j, &capacity) in optimized.iter().enumerate() {
        let x = solution.x[j];
        let bound = if x <= lower[j] {
            if min_ratios[j].is_some_and(|r| r >= 1. - trust_region) {
                " (minimum capacity)"
            } else {
                " (trust-region bound)"
            }
        } else if x >= upper[j] {
            if max_ratios[j].is_some_and(|r| r <= 1. + trust_region) {
                " (maximum capacity)"
            } else {
                " (trust-region bound)"
            }
        } else {
            ""
        };
        info!(
            "Category {}: optimized capacity of {:.5} PCE/s per lane ({:.0} PCE/h per lane), \
            {:+.2}%{bound}",
            categories.name(j),
            f64::from(capacity),
            3600. * f64::from(capacity),
            100. * (x - 1.),
        );
    }
    optimized
}

/// Returns the weight `wₖ` of the penalty residual `wₖ·xₖ` of each category (empty if there is no
/// penalty), where `xₖ` is the capacity relative to its value at the start of the optimization.
///
/// With `wₖ = √(N·λ)·cₖ/cₖ⁰` (`N` target routes, capacity `cₖ` at the start of the optimization,
/// initial capacity `cₖ⁰`), half the sum of the squared residuals is `N/2` times the mean squared
/// error of the delays plus `λ·Σₖ (cₖ / cₖ⁰)²`.
///
/// The weight is zero for the categories crossed by no target route: the delays do not depend on
/// their capacity, so the penalty alone would decrease it in every optimization. With a zero
/// column of the Jacobian matrix, their capacity is fixed.
fn penalty_weights(
    penalty: f64,
    nb_targets: usize,
    capacities: &[FlowPerLane],
    initial_capacities: &[FlowPerLane],
    crossed: &[bool],
) -> Vec<f64> {
    if penalty == 0. {
        return Vec::new();
    }
    let factor = (nb_targets as f64 * penalty).sqrt();
    capacities
        .iter()
        .zip(initial_capacities)
        .zip(crossed)
        .map(|((&c, &c0), &crossed)| {
            if crossed {
                factor * f64::from(c) / f64::from(c0)
            } else {
                0.
            }
        })
        .collect()
}

/// Reason why the Levenberg–Marquardt algorithm stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Termination {
    /// The gradient is zero for all the variables that are not at a bound blocking it.
    Stationary,
    /// The last step changed no variable by more than the tolerance.
    StepTolerance,
    /// The maximum number of iterations was reached.
    MaxIterations,
}

/// Result of the Levenberg–Marquardt algorithm.
#[derive(Clone, Debug)]
struct Solution {
    /// Value of the variables.
    x: Vec<f64>,
    /// Residuals at the solution.
    residuals: Vec<f64>,
    /// Number of iterations (each one evaluates the residuals once, except when no decrease of
    /// the objective is predicted).
    nb_iterations: u64,
    termination: Termination,
}

/// Minimizes the sum of the squared residuals with the Levenberg–Marquardt algorithm, within the
/// box `[lower, upper]`, starting from `x` (which must be in the box).
///
/// The function `evaluate` returns the residuals and their Jacobian matrix (row-major, one row per
/// residual and one column per variable) for the given variables.
///
/// The damping is the diagonal of the Gauss–Newton matrix times a factor updated with the rule of
/// Nielsen (1999) (Marquardt's scaling), so the step does not depend on the scale of each variable:
/// a variable whose residuals barely depend on it still gets its Gauss–Newton step. The variables
/// whose column of the Jacobian matrix is zero (they do not change the residuals) and the variables
/// at a bound that the gradient or their step pushes outside of the box are fixed (see
/// [free_step]), the step of the others is projected onto the box, and the step is accepted if it
/// decreases the objective.
///
/// The algorithm stops when the step changes no variable by more than `step_tolerance`, even if
/// the step is rejected: the next steps would be smaller, with a larger damping.
///
/// Each iteration logs the root mean square of all the residuals.
fn levenberg_marquardt(
    mut evaluate: impl FnMut(&[f64]) -> (Vec<f64>, Vec<f64>),
    lower: &[f64],
    upper: &[f64],
    mut x: Vec<f64>,
    max_iterations: u64,
    step_tolerance: f64,
) -> Solution {
    let n = x.len();
    debug_assert!(n > 0);
    debug_assert!((0..n).all(|j| lower[j] <= x[j] && x[j] <= upper[j]));
    let (mut residuals, jacobian) = evaluate(&x);
    let mut objective = half_sum_of_squares(&residuals);
    let (mut hessian, mut gradient) = normal_equations(&residuals, &jacobian, n);
    let mut damping = INITIAL_DAMPING;
    let mut damping_factor = 2.;
    let mut nb_iterations = 0;
    let termination = loop {
        let free: Vec<usize> = (0..n)
            .filter(|&j| {
                hessian[j * n + j] > 0.
                    && !(x[j] <= lower[j] && gradient[j] > 0.
                        || x[j] >= upper[j] && gradient[j] < 0.)
            })
            .collect();
        if free.iter().all(|&j| gradient[j] == 0.) {
            break Termination::Stationary;
        }
        if nb_iterations == max_iterations {
            break Termination::MaxIterations;
        }
        nb_iterations += 1;
        let mut accepted = false;
        let mut step_size = f64::INFINITY;
        if let Some(step) = free_step(&hessian, &gradient, free, damping, &x, lower, upper) {
            let trial: Vec<f64> = (0..n)
                .map(|j| (x[j] + step[j]).clamp(lower[j], upper[j]))
                .collect();
            let step: Vec<f64> = trial.iter().zip(&x).map(|(t, x)| t - x).collect();
            step_size = step.iter().fold(0., |m, s| m.max(s.abs()));
            let predicted_decrease = -dot(&gradient, &step) - quadratic_form(&hessian, &step) / 2.;
            if predicted_decrease > 0. {
                let (trial_residuals, trial_jacobian) = evaluate(&trial);
                let trial_objective = half_sum_of_squares(&trial_residuals);
                accepted = trial_objective < objective;
                info!(
                    "Iteration {nb_iterations}: RMSE {:.3} (step {}), damping {damping:.3e}",
                    rmse(trial_objective, trial_residuals.len()),
                    if accepted { "accepted" } else { "rejected" },
                );
                if accepted {
                    let ratio = (objective - trial_objective) / predicted_decrease;
                    damping *= (1. / 3.0f64).max(1. - (2. * ratio - 1.).powi(3));
                    damping_factor = 2.;
                    x = trial;
                    residuals = trial_residuals;
                    objective = trial_objective;
                    (hessian, gradient) = normal_equations(&residuals, &trial_jacobian, n);
                }
            } else {
                info!("Iteration {nb_iterations}: no decrease predicted, damping {damping:.3e}");
            }
        }
        if !accepted {
            damping *= damping_factor;
            damping_factor *= 2.;
        }
        if step_size <= step_tolerance {
            break Termination::StepTolerance;
        }
    };
    Solution {
        x,
        residuals,
        nb_iterations,
        termination,
    }
}

/// Returns half the sum of the squared residuals.
pub(super) fn half_sum_of_squares(residuals: &[f64]) -> f64 {
    residuals.iter().map(|r| r * r).sum::<f64>() / 2.
}

/// Returns the root mean square of the residuals, given half their sum of squares.
pub(super) fn rmse(half_sum_of_squares: f64, nb_residuals: usize) -> f64 {
    if nb_residuals == 0 {
        0.
    } else {
        (2. * half_sum_of_squares / nb_residuals as f64).sqrt()
    }
}

/// Returns the Gauss–Newton matrix `JᵀJ` (row-major) and the gradient `Jᵀr` of half the sum of
/// the squared residuals, given the residuals `r` and their Jacobian matrix `J` (row-major, with `n`
/// columns).
fn normal_equations(residuals: &[f64], jacobian: &[f64], n: usize) -> (Vec<f64>, Vec<f64>) {
    debug_assert_eq!(jacobian.len(), residuals.len() * n);
    let blocks: Vec<_> = jacobian
        .par_chunks(BLOCK_SIZE * n)
        .zip(residuals.par_chunks(BLOCK_SIZE))
        .map(|(rows, residuals)| {
            let mut hessian = vec![0.; n * n];
            let mut gradient = vec![0.; n];
            for (row, &r) in rows.chunks(n).zip(residuals) {
                for (i, &a) in row.iter().enumerate() {
                    if a == 0. {
                        continue;
                    }
                    gradient[i] += a * r;
                    for (h, &b) in hessian[i * n..(i + 1) * n].iter_mut().zip(row) {
                        *h += a * b;
                    }
                }
            }
            (hessian, gradient)
        })
        .collect();
    let mut hessian = vec![0.; n * n];
    let mut gradient = vec![0.; n];
    for (h, g) in blocks {
        hessian.iter_mut().zip(h).for_each(|(a, b)| *a += b);
        gradient.iter_mut().zip(g).for_each(|(a, b)| *a += b);
    }
    (hessian, gradient)
}

/// Returns the Levenberg–Marquardt step of the given free variables (zero for the other variables),
/// at `x` in the box `[lower, upper]`, or `None` if the damped matrix is not positive definite
/// (numerically).
///
/// The free variables at a bound whose step points outside of the box are fixed, and the step of
/// the others is computed again (otherwise, it would assume that the fixed variables move), until
/// no step points outside of the box at a bound.
fn free_step(
    hessian: &[f64],
    gradient: &[f64],
    mut free: Vec<usize>,
    damping: f64,
    x: &[f64],
    lower: &[f64],
    upper: &[f64],
) -> Option<Vec<f64>> {
    loop {
        let step = damped_step(hessian, gradient, &free, damping)?;
        let nb_free = free.len();
        free.retain(|&j| !(x[j] <= lower[j] && step[j] < 0. || x[j] >= upper[j] && step[j] > 0.));
        if free.len() == nb_free {
            return Some(step);
        }
    }
}

/// Returns the Levenberg–Marquardt step `-(H + λ·diag(H))⁻¹ g` of the free variables (zero for the
/// other variables), or `None` if the damped matrix is not positive definite (numerically).
fn damped_step(
    hessian: &[f64],
    gradient: &[f64],
    free: &[usize],
    damping: f64,
) -> Option<Vec<f64>> {
    let n = gradient.len();
    let matrix = free
        .iter()
        .flat_map(|&i| {
            free.iter().map(move |&j| {
                let diagonal = if i == j {
                    damping * hessian[i * n + i]
                } else {
                    0.
                };
                hessian[i * n + j] + diagonal
            })
        })
        .collect();
    let free_step = solve_cholesky(matrix, free.iter().map(|&j| -gradient[j]).collect())?;
    let mut step = vec![0.; n];
    for (&j, s) in free.iter().zip(free_step) {
        step[j] = s;
    }
    Some(step)
}

/// Returns the solution `x` of `Ax = b`, for a symmetric positive-definite matrix `A` (row-major),
/// with a Cholesky decomposition, or `None` if `A` is not positive definite (numerically).
fn solve_cholesky(mut a: Vec<f64>, mut b: Vec<f64>) -> Option<Vec<f64>> {
    let n = b.len();
    debug_assert_eq!(a.len(), n * n);
    // Decomposition A = LLᵀ, with L stored in the lower triangle of `a`.
    for j in 0..n {
        let pivot = a[j * n + j] - (0..j).map(|k| a[j * n + k].powi(2)).sum::<f64>();
        if pivot.is_nan() || pivot <= 0. {
            return None;
        }
        let pivot = pivot.sqrt();
        a[j * n + j] = pivot;
        for i in j + 1..n {
            let sum = (0..j).map(|k| a[i * n + k] * a[j * n + k]).sum::<f64>();
            a[i * n + j] = (a[i * n + j] - sum) / pivot;
        }
    }
    // Solution of Ly = b, then of Lᵀx = y.
    for i in 0..n {
        let sum = (0..i).map(|k| a[i * n + k] * b[k]).sum::<f64>();
        b[i] = (b[i] - sum) / a[i * n + i];
    }
    for i in (0..n).rev() {
        let sum = (i + 1..n).map(|k| a[k * n + i] * b[k]).sum::<f64>();
        b[i] = (b[i] - sum) / a[i * n + i];
    }
    Some(b)
}

/// Returns the dot product of two vectors.
fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b).map(|(a, b)| a * b).sum()
}

/// Returns `xᵀAx`, for a square matrix `A` (row-major).
fn quadratic_form(a: &[f64], x: &[f64]) -> f64 {
    a.chunks(x.len())
        .zip(x)
        .map(|(row, xi)| xi * dot(row, x))
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Residuals `(x1 - 1, x2 - 2, x1 + x2 - 3)`, with an exact solution at `(1, 2)`.
    fn affine(x: &[f64]) -> (Vec<f64>, Vec<f64>) {
        (
            vec![x[0] - 1., x[1] - 2., x[0] + x[1] - 3.],
            vec![1., 0., 0., 1., 1., 1.],
        )
    }

    fn assert_close(x: &[f64], expected: &[f64], tolerance: f64) {
        assert!(
            x.iter()
                .zip(expected)
                .all(|(a, b)| (a - b).abs() <= tolerance),
            "{x:?} != {expected:?}"
        );
    }

    #[test]
    fn affine_test() {
        let solution =
            levenberg_marquardt(affine, &[0., 0.], &[5., 5.], vec![0.5, 0.5], 100, 1e-12);
        assert_close(&solution.x, &[1., 2.], 1e-8);
        assert!(rmse(half_sum_of_squares(&solution.residuals), 3) < 1e-8);
        assert_ne!(solution.termination, Termination::MaxIterations);
    }

    #[test]
    fn bounded_affine_test() {
        // With x2 <= 1.5, the gradient pushes x2 to its bound, and the optimal x1 is then the
        // solution of (x1 - 1) + (x1 + 1.5 - 3) = 0.
        let solution =
            levenberg_marquardt(affine, &[0., 0.], &[5., 1.5], vec![0.5, 0.5], 100, 1e-12);
        assert_close(&solution.x, &[1.25, 1.5], 1e-8);
        assert_ne!(solution.termination, Termination::MaxIterations);
    }

    #[test]
    fn rosenbrock_test() {
        let rosenbrock = |x: &[f64]| {
            (
                vec![10. * (x[1] - x[0] * x[0]), 1. - x[0]],
                vec![-20. * x[0], 10., -1., 0.],
            )
        };
        let solution = levenberg_marquardt(
            rosenbrock,
            &[-2., -2.],
            &[2., 2.],
            vec![-1.2, 1.],
            200,
            1e-12,
        );
        assert_close(&solution.x, &[1., 1.], 1e-6);
        assert_ne!(solution.termination, Termination::MaxIterations);
    }

    #[test]
    fn zero_jacobian_test() {
        let solution = levenberg_marquardt(
            |_: &[f64]| (vec![1., -1.], vec![0., 0.]),
            &[0.],
            &[2.],
            vec![1.],
            100,
            1e-12,
        );
        assert_eq!(solution.x, vec![1.]);
        assert_eq!(solution.residuals, vec![1., -1.]);
        assert_eq!(solution.nb_iterations, 0);
        assert_eq!(solution.termination, Termination::Stationary);
    }

    #[test]
    fn penalty_test() {
        // Residual flat above 0.9 (no queue), as for a category without queues.
        let hinge = |x: &[f64]| {
            if x[0] < 0.9 {
                (vec![10. * (0.9 - x[0])], vec![-10.])
            } else {
                (vec![0.], vec![0.])
            }
        };
        let solution = levenberg_marquardt(hinge, &[0.8], &[1.2], vec![1.], 100, 1e-12);
        assert_eq!(solution.x, vec![1.]);
        assert_eq!(solution.termination, Termination::Stationary);
        // With a small penalty, the variable goes down to the start of the non-flat region.
        let weight = 0.1;
        let penalized = |x: &[f64]| {
            let (mut residuals, mut jacobian) = hinge(x);
            residuals.push(weight * x[0]);
            jacobian.push(weight);
            (residuals, jacobian)
        };
        let solution = levenberg_marquardt(penalized, &[0.8], &[1.2], vec![1.], 100, 1e-12);
        assert_close(&solution.x, &[0.9], 1e-3);
        assert_ne!(solution.termination, Termination::MaxIterations);
    }

    #[test]
    fn scaled_damping_test() {
        // A strongly constrained variable and a variable whose only curvature, above 0.9, is a
        // small penalty: with a damping that does not depend on the scale of each variable, both
        // reach their optimum (with the identity damping, x2 would barely move).
        let evaluate = |x: &[f64]| {
            let (hinge, slope) = if x[1] < 0.9 {
                (10. * (0.9 - x[1]), -10.)
            } else {
                (0., 0.)
            };
            (
                vec![1000. * (x[0] - 1.1), hinge, 0.1 * x[1]],
                vec![1000., 0., 0., slope, 0., 0.1],
            )
        };
        let solution =
            levenberg_marquardt(evaluate, &[0.8, 0.8], &[1.2, 1.2], vec![1., 1.], 30, 1e-4);
        assert_close(&solution.x, &[1.1, 0.9], 1e-3);
    }

    #[test]
    fn penalty_weights_test() {
        let capacities = [
            FlowPerLane::new_unchecked(0.4),
            FlowPerLane::new_unchecked(0.2),
        ];
        let initial = [
            FlowPerLane::new_unchecked(0.2),
            FlowPerLane::new_unchecked(0.2),
        ];
        let crossed = [true, true];
        assert!(penalty_weights(0., 100, &capacities, &initial, &crossed).is_empty());
        // √(100 × 0.01) = 1.
        assert_close(
            &penalty_weights(0.01, 100, &capacities, &initial, &crossed),
            &[2., 1.],
            1e-12,
        );
        // No penalty for a category crossed by no target route.
        assert_close(
            &penalty_weights(0.01, 100, &capacities, &initial, &[true, false]),
            &[2., 0.],
            1e-12,
        );
    }

    #[test]
    fn free_step_test() {
        // Residuals (x1 + x2 - 1, 0.1 (x1 - x2 + 3)), minimum at (-1, 2). At (0, -2), with x1 at its
        // lower bound 0, the gradient (-2.95, -3.05) pulls x1 inside the box, but the Gauss–Newton
        // step (-1, 4) pushes it outside: x1 is fixed and x2 gets its step with x1 fixed,
        // 3.05 / 1.01 (instead of 4).
        let (residuals, jacobian) = (vec![-3., 0.5], vec![1., 1., 0.1, -0.1]);
        let (hessian, gradient) = normal_equations(&residuals, &jacobian, 2);
        assert_close(&gradient, &[-2.95, -3.05], 1e-12);
        let step = free_step(
            &hessian,
            &gradient,
            vec![0, 1],
            0.,
            &[0., -2.],
            &[0., -5.],
            &[5., 5.],
        )
        .unwrap();
        assert_close(&step, &[0., 3.05 / 1.01], 1e-12);
        // Inside the box, the step is the Gauss–Newton step.
        let step = free_step(
            &hessian,
            &gradient,
            vec![0, 1],
            0.,
            &[0., -2.],
            &[-5., -5.],
            &[5., 5.],
        )
        .unwrap();
        assert_close(&step, &[-1., 4.], 1e-12);
    }

    #[test]
    fn coupled_bound_test() {
        // Same residuals as in `free_step_test`: the minimum with x1 >= 0 is at x1 = 0 and
        // x2 = 2.06 / 2.02.
        let evaluate = |x: &[f64]| {
            (
                vec![x[0] + x[1] - 1., 0.1 * (x[0] - x[1] + 3.)],
                vec![1., 1., 0.1, -0.1],
            )
        };
        let solution =
            levenberg_marquardt(evaluate, &[0., -5.], &[5., 5.], vec![0., -2.], 100, 1e-12);
        assert_close(&solution.x, &[0., 2.06 / 2.02], 1e-8);
        assert_ne!(solution.termination, Termination::MaxIterations);
    }

    #[test]
    fn solve_cholesky_test() {
        // A x = b with x = (1, -1, 2).
        let a = vec![4., 2., 0., 2., 5., 3., 0., 3., 6.];
        let x = solve_cholesky(a, vec![2., 3., 9.]).unwrap();
        assert_close(&x, &[1., -1., 2.], 1e-12);
        // Not positive definite.
        assert!(solve_cholesky(vec![1., 2., 2., 1.], vec![1., 1.]).is_none());
    }
}
