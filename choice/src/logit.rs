// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use anyhow::{anyhow, Context, Result};
use serde::{Deserialize, Serialize};
use ttf::{PwlXYF, TTFNum};

use super::ContinuousChoiceCallback;

const EULER_MASCHERONI: f64 = 0.5772156649;

/// Return Euler's constant in the desired type.
fn euler_mascheroni<V: TTFNum>() -> Result<V> {
    V::from(EULER_MASCHERONI)
        .ok_or_else(|| anyhow!("Cannot convert {:?} to Float", EULER_MASCHERONI))
}

/// A discrete or continuous Logit model.
///
/// The expecte payoff of the choice is computed using the Log-sum formula.
///
/// # Example
///
/// ```
/// use choice::LogitModel;
/// use ttf::PwlXYF;
///
/// let model = LogitModel::new(0.8f64, 1.0f64);
///
/// let (choice_id, exp_payoff) = model.get_choice(&[0.]).unwrap();
/// assert_eq!(choice_id, 0);
/// // The expected payoff is equal to the Euler's constant.
/// assert!((exp_payoff - 0.5772156649).abs() < 1e-8);
///
/// // The probabilities are `[e / (1 + e), 1 / (1 + e)]`, i.e., around 0.73 and 0.27.
/// // With `u = 0.8`, the second alternative is chosen.
/// let (choice_id, _exp_payoff) = model.get_choice(&[1., 0.]).unwrap();
/// assert_eq!(choice_id, 1);
///
/// let bpf = PwlXYF::from_values(vec![0., 0.], 0., 1.);
/// let (callback, exp_payoff) = model.get_continuous_choice(bpf).unwrap();
/// // The expected payoff is equal to the Euler's constant.
/// assert!((exp_payoff - 0.5772156649).abs() < 1e-8);
/// // The choice (given by the callback function) is equal to `u = 0.8` because the
/// // piecewise-linear function is constant between 0.0 and 1.0.
/// assert_eq!(callback(), 0.8);
/// ```
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct LogitModel<T> {
    /// Uniform random number between 0.0 and 1.0 for inversion sampling.
    u: T,
    /// Variance of the error terms, must be positive.
    mu: T,
}

impl<T: TTFNum> LogitModel<T> {
    /// Initializes a Logit model.
    ///
    /// The value of `u` must be such that `0.0 <= u < 1.0`.
    /// The value of `mu` must be such that `mu > 0`.
    pub fn new(u: T, mu: T) -> Self {
        LogitModel { u, mu }
    }

    /// Returns the alternative chosen and the expected payoff of the choice given a slice of
    /// values for a finite number of alternatives.
    ///
    /// The expected payoff is computed using the log-sum formula.
    ///
    /// Returns an Error if
    ///
    /// - The vector of values is empty.
    ///
    /// - Invalid values where found (e.g., NAN or infinity).
    ///
    /// - Euler's constant is not a valid value for the Float type.
    ///
    /// When all assumptions are satisfied, the function always return a valid choice.
    /// The expected payoff is never NAN but it can be positive infinity when mu is large.
    pub fn get_choice<V: TTFNum + Into<T> + From<T>>(&self, values: &[V]) -> Result<(usize, V)> {
        if values.is_empty() {
            return Err(anyhow!(
                "Cannot compute choice from an empty slice of values"
            ));
        }
        if values.iter().any(|&v| !v.is_finite()) {
            return Err(anyhow!("Found a non-finite payoff: {:?}", values));
        }
        // The maximum value is guaranteed to be finite because (i) all values are finite and (ii)
        // there is at least one value.
        let max_value = values.iter().fold(V::neg_infinity(), |m, &v| m.max(v));
        // Decrease the value of all alternatives by the maximum value to prevent overflow.
        // (v - max_value) is thus non-positive and mu is positive so the `exp` cannot overflow.
        // In the worse case, (v - max_value) / mu overflows to -Infinity and then the exponential
        // yields 0.0, which is fine.
        // All exp_values are between 0.0 and 1.0.
        let exp_values: Vec<T> = values
            .iter()
            .map(|&v| ((v - max_value).into() / self.mu).exp())
            .collect();
        // Compute the denominator of the logit formula.
        // Sigma is guaranteed to be between 1.0 and values.len() because all exp_values are
        // between 0.0 and 1.0 and, for i such that v_i = max_value, exp_value_i is equal to 1.0.
        let sigma = exp_values.iter().fold(T::zero(), |sum, &v| sum + v);
        // Compute the cumulative logit probabilities and find the index of the alternative chosen
        // using the inverse sampling theorem.
        // The `unwrap` does not panic because `u` < 1.0 and for the last value, `cum_prob ` = 1.0.
        let (choice_id, _) = exp_values
            .iter()
            .scan(T::zero(), |sum, &exp_v| {
                *sum += exp_v / sigma;
                Some(*sum)
            })
            .enumerate()
            .find(|&(_, cum_prob)| self.u < cum_prob)
            .unwrap();
        // Compute the expected payoff of the choice using the log-sum formula.
        // Do not forget to add back the maximum value that was substracted.
        let expected_value =
            max_value + <V as From<T>>::from(self.mu * (sigma.ln() + euler_mascheroni()?));
        Ok((choice_id, expected_value))
    }

    /// Returns the integral of the function exp(v / mu) between x0 and x1.
    ///
    /// The function can overflow to positive infinity if:
    ///
    /// - `y0` or `y1` is large
    ///
    /// - `x1 - x0` is large
    ///
    /// - `mu` is large
    ///
    /// The function can underflow to 0.0 if:
    ///
    /// - `y0` or `y1` is small
    ///
    /// - `x1 - x0` is small
    ///
    /// - `mu` is small
    fn get_cum_func_value(&self, (x0, y0): (T, T), (x1, y1): (T, T)) -> T {
        if y0 == y1 {
            // Area of a square.
            return (y0 / self.mu).exp() * (x1 - x0);
        }
        let y0_exp = (y0 / self.mu).exp();
        let y1_exp = (y1 / self.mu).exp();
        let y_exp_diff = y1_exp - y0_exp;
        if y_exp_diff.is_zero() {
            // Practically a square.
            return y0_exp * (x1 - x0);
        }
        let theta = (y1 - y0) / (x1 - x0);
        (self.mu / theta) * y_exp_diff
    }

    /// Returns the chosen x value, given the chosen segment and the distance to the threshold value.
    fn get_chosen_x(&self, (x0, y0): (T, T), (x1, y1): (T, T), prob_diff: T) -> T {
        let theta = (y1 - y0) / (x1 - x0);
        let x = if theta.is_zero() {
            // y0 and y1 are practically equal so we use linear approximation.
            x0 + prob_diff / (y0 / self.mu).exp()
        } else {
            // In practise, y0 is non-negative so the exp cannot overflow.
            x0 + (self.mu / theta) * (prob_diff * theta / self.mu + (y0 / self.mu).exp()).ln()
                - y0 / theta
        };
        // Force the bounds if overflow or underflow occured.
        x.max(x0).min(x1)
    }

    /// Returns the expected payoff of the choice and a [ContinuousChoiceCallback] that gives the
    /// chosen continuous alternative, given a [PwlXYF] that yields the payoff value for any
    /// possible alternative.
    ///
    /// The expected payoff is computed using the log-sum formula.
    ///
    /// Returns an error if
    ///
    /// - The breakpoint upper bound is infinite.
    ///
    /// - Euler's constant is not a valid value for the Float type.
    pub fn get_continuous_choice<'a, X, Y>(
        &'a self,
        func: PwlXYF<X, Y, T>,
    ) -> Result<(ContinuousChoiceCallback<'a, X>, Y)>
    where
        X: TTFNum + Into<T> + From<T> + 'a,
        Y: TTFNum + Into<T> + From<T> + 'a,
    {
        // To prevent overflow, we force the values to be non-positive when computing the
        // probabilities (the expected payoff is not affected).
        let max_value = func.max();
        if !max_value.is_finite() {
            return Err(anyhow!("Found a non-finite payoff for function {:?}", func));
        }
        // Let M + 1 be the number of breakpoints.
        // Compute each part G_i of the cumulative distribution function, for 1 <= i <= M.
        // G_i is defined as the integral, from x_i to x_i+1, of exp(y(tau) / mu) d tau.
        let cum_probs_parts: Vec<T> = func
            .double_iter()
            .map(|((x0, y0), (x1, y1))| {
                self.get_cum_func_value(
                    (x0.into(), (y0 - max_value).into()),
                    (x1.into(), (y1 - max_value).into()),
                )
            })
            .collect();
        // Compute the integral from x_1 to x_M+1 (i.e., the sum of the values G_i).
        let sigma = cum_probs_parts.iter().fold(T::zero(), |sum, &v| sum + v);
        if sigma == T::zero() {
            // An overflow was probably encountered when computing the integrals because the slopes
            // are very large.
            // We try to use a discrete choice instead (this make sense if the slopes are indeed
            // very large).
            let y_values: Vec<_> = func.iter_y().collect();
            let (id, exp_payoff) = self
                .get_choice(&y_values)
                .context("Failed to compute a deterministic choice from the y values")?;
            return Ok((Box::new(move || func.x_at_index(id)), exp_payoff));
        }
        // Compute the expected payoff using the log-sum formula.
        // Do not forget to add back the maximum value that was substracted.
        let expected_payoff =
            max_value + <Y as From<T>>::from(self.mu * (sigma.ln() + euler_mascheroni()?));
        let callback_function = move || {
            // We want to find k such that F(x_k) <= u < F(x_k+1), where F(x_i) = sum_{j<=i} G_j / Sigma.
            // To do so, we compute the cumulative sum of G_i and we stop when the cumulative sum is
            // larger than u * Sigma.
            // The value cum_prob is equal to F(x_k+1).
            let threshold = self.u * sigma;
            let (k, cum_prob) = cum_probs_parts
                .iter()
                .scan(T::zero(), |sum, &g| {
                    *sum += g;
                    Some(*sum)
                })
                .enumerate()
                .find(|(_, cum_prob)| *cum_prob > threshold)
                .unwrap_or_else(|| (cum_probs_parts.len() - 1, T::one()));
            let x0 = func.x_at_index(k);
            let x1 = func.x_at_index(k + 1);
            let y0 = func.y_at_index(k);
            let y1 = func.y_at_index(k + 1);
            <X as From<T>>::from(self.get_chosen_x(
                (x0.into(), (y0 - max_value).into()),
                (x1.into(), (y1 - max_value).into()),
                cum_probs_parts[k] - (cum_prob - threshold),
            ))
        };
        Ok((Box::new(callback_function), expected_payoff))
    }
}

#[cfg(test)]
mod tests {
    use ttf::PwlTTF;

    use super::*;

    #[test]
    fn logit_choice_test() {
        let model = LogitModel::new(0.9f64, 2.0f64);
        // No choice: error.
        assert!(model.get_choice::<f64>(&[]).is_err());
        // Invalid values: error.
        assert!(model.get_choice(&[1., 0., f64::NAN]).is_err());
        assert!(model.get_choice(&[1., 0., f64::NEG_INFINITY]).is_err());
        assert!(model.get_choice(&[1., 0., f64::INFINITY]).is_err());
        // Only 1 choice: this choice is returned with its payoff (+ mu * Euler's constant).
        assert_eq!(
            model.get_choice(&[1.]).unwrap(),
            (0, 1. + 2. * EULER_MASCHERONI)
        );
        // 2 choices with same payoff, the second one is returned because u > 0.5.
        // Expected payoff is mu * ln(1 + 1) + mu * Euler's constant.
        assert_eq!(
            model.get_choice(&[0., 0.]).unwrap(),
            (1, 2. * 2.0f64.ln() + 2. * EULER_MASCHERONI)
        );
        // Vector of very large utilities.
        assert_eq!(
            model.get_choice(&[f64::MAX, f64::MAX]).unwrap(),
            (1, f64::MAX + 2. * 2.0f64.ln() + 2. * EULER_MASCHERONI)
        );
        // Vector of very small utilities.
        assert_eq!(
            model.get_choice(&[f64::MIN, f64::MIN]).unwrap(),
            (1, f64::MIN + 2. * 2.0f64.ln() + 2. * EULER_MASCHERONI)
        );
        // Very small mu.
        let model = LogitModel::new(1e-4, f64::MIN_POSITIVE);
        let choice = model.get_choice(&[1. - f64::EPSILON, 1.]).unwrap();
        assert_eq!(choice.0, 1);
        assert!((choice.1 - 1.).abs() < 1e8);
        let choice = model.get_choice(&[f64::MIN, f64::MAX]).unwrap();
        assert_eq!(choice.0, 1);
        assert_eq!(choice.1, f64::MAX);
        // Very large mu.
        let model = LogitModel::new(0., f64::MAX);
        let choice = model.get_choice(&[f64::MIN, f64::MAX]).unwrap();
        assert_eq!(choice.0, 1);
        assert!(choice.1.is_infinite());
    }

    #[test]
    fn get_cum_func_value_test() {
        // Squares.
        let model = LogitModel::new(0.5f64, 2.0f64);
        assert_eq!(
            model.get_cum_func_value((0., 10.), (10., 10.)),
            10. * 5.0f64.exp()
        );
        assert_eq!(
            model.get_cum_func_value((-20., -10.), (-10., -10.)),
            10. * (-5.0f64).exp()
        );
        // Very small values.
        assert_eq!(
            model.get_cum_func_value((0., f64::MIN), (1., f64::MIN)),
            (f64::MIN / 2.).exp()
        );
        assert!(
            (model.get_cum_func_value((0., f64::MIN), (1., f64::MIN + 1.)) - (f64::MIN / 2.).exp())
                .abs()
                < 1e-8
        );
        // Very large values.
        assert_eq!(
            model.get_cum_func_value((0., f64::MAX), (1., f64::MAX)),
            f64::INFINITY
        );
        assert_eq!(
            model.get_cum_func_value((0., f64::MAX), (1., f64::MAX - 1.)),
            f64::INFINITY
        );
        // Very small period.
        assert!(model.get_cum_func_value((0., 0.), (f64::EPSILON, -1.)) > 0.);
        // Very large period: overflow.
        assert!(model
            .get_cum_func_value((f64::MIN, 0.), (f64::MAX, -f64::EPSILON))
            .is_infinite());
        // Small slope: no overflow somehow.
        assert!((model.get_cum_func_value((0., 0.), (1., -f64::EPSILON)) - 1.).abs() < 1e-8);
        // Large slope: overflow.
        assert!((model.get_cum_func_value((0., f64::MIN), (1., 0.)).abs() < 1e-8));
        // Very small mu.
        let model = LogitModel::new(1e-4, f64::MIN_POSITIVE);
        assert_eq!(model.get_cum_func_value((0., 0.), (1., 0.)), 1.);
        assert_eq!(model.get_cum_func_value((0., -1.), (1., -2.)), 0.);
        // Very large mu.
        let model = LogitModel::new(0., f64::MAX);
        assert_eq!(model.get_cum_func_value((0., 0.), (1., -f64::EPSILON)), 1.);
    }

    #[test]
    fn continuous_logit_test() {
        let model = LogitModel::new(0.4f64, 2.0f64);
        // Invalid values: error.
        let bpf = PwlTTF::from_values(vec![0., f64::INFINITY], 0., 10.);
        assert!(model.get_continuous_choice(bpf).is_err());
        // Two equal choices: linear interpolation.
        // Log sum is mu * ln(10.0) + mu * Euler's constant.
        let bpf = PwlTTF::from_values(vec![0., 0.], 0., 10.);
        let choice = model.get_continuous_choice(bpf).unwrap();
        assert_eq!((choice.0)(), 4.);
        assert_eq!(choice.1, 2. * 10.0f64.ln() + 2. * EULER_MASCHERONI);
        // Very large slope 1.
        let bpf = PwlTTF::from_values(vec![f64::MIN, f64::MAX], 0., 10.);
        let choice = model.get_continuous_choice(bpf).unwrap();
        assert_eq!((choice.0)(), 10.);
        assert_eq!(
            choice.1,
            f64::MAX + 2. * 2.0f64.ln() + 2. * EULER_MASCHERONI
        );
        // Very large slope 2.
        let bpf = PwlTTF::from_values(vec![f64::MIN, f64::MAX, f64::MIN], 0., 10.);
        let choice = model.get_continuous_choice(bpf).unwrap();
        assert_eq!((choice.0)(), 10.);
        assert_eq!(
            choice.1,
            f64::MAX + 2. * 3.0f64.ln() + 2. * EULER_MASCHERONI
        );
        // Very large slope 3.
        let bpf = PwlTTF::from_values(vec![f64::MAX, f64::MIN, f64::MAX], 0., 10.);
        let choice = model.get_continuous_choice(bpf).unwrap();
        assert_eq!((choice.0)(), 0.);
        assert_eq!(
            choice.1,
            f64::MAX + 2. * 3.0f64.ln() + 2. * EULER_MASCHERONI
        );
    }
}
