//! Finite numerical measures of information for the crates that depend on
//! `monad-kernel`: a supplied channel capacity in nats and a grid approximation
//! of the Chernoff information between two finite distributions.
//!
//! It builds on the probability-vector check in [`crate::causality`]. Where the
//! formal library states a coding or testing theorem, these values are numerical
//! projections of its quantities and do not prove it.

use crate::causality::assert_probability_vector;

/// A supplied finite capacity value in nats per channel use.
///
/// The formal reference is a supremum over admitted input laws, measured in
/// nats and possibly infinite. This value-holder performs no optimisation and
/// checks no coding assumptions. Convert a value in bits by multiplying by ln(2).
///
/// Lean: `MonadFormal.Information.capacity`.
#[derive(Debug, Clone, Copy)]
pub struct ChannelCapacityNats {
    /// Nats per use of the record channel.
    pub nats_per_use: f64,
}

impl ChannelCapacityNats {
    pub fn new(nats_per_use: f64) -> Self {
        assert!(
            nats_per_use.is_finite() && nats_per_use >= 0.0,
            "capacity must be finite and non-negative"
        );
        Self { nats_per_use }
    }
}

/// A grid approximation to finite-distribution Chernoff information, in nats.
///
/// The exact quantity is the logarithmic Bayes-error exponent for independent,
/// identically distributed binary testing with fixed positive priors.
/// The formal reference takes an infimum over the full open parameter interval
/// and retains infinity for disjoint supports. The numerical grid and its
/// selected parameter are not certified optimisers or proof objects. The
/// quantity is not an asymptotic prefactor or an individual false-negative rate.
///
/// Lean: `MonadFormal.Information.chernoffInfo`.
#[derive(Debug, Clone, Copy)]
pub struct ChernoffInformation {
    /// Selected grid value; infinite for disjoint supports.
    pub value: f64,
    /// Best grid parameter in [0, 1], not a certified continuous optimizer.
    pub optimal_s: f64,
}

impl ChernoffInformation {
    /// Approximate Chernoff information between two validated distributions.
    ///
    /// Uses `grid_steps + 1` equally spaced parameters and log-sum-exp on the
    /// common positive support. Endpoints mean one-sided limits from (0, 1),
    /// so support mismatch is explicit rather than hidden in a 0^0 convention.
    /// Grid error and floating-point error are not certified by this prototype.
    pub fn compute(p: &[f64], q: &[f64], grid_steps: usize) -> Self {
        assert_eq!(p.len(), q.len(), "distribution length mismatch");
        assert!(grid_steps >= 2, "need at least 2 grid points");
        assert_probability_vector(p);
        assert_probability_vector(q);

        let common: Vec<(f64, f64)> = p
            .iter()
            .zip(q)
            .filter(|(pi, qi)| **pi > 0.0 && **qi > 0.0)
            .map(|(pi, qi)| (pi.ln(), qi.ln()))
            .collect();
        if common.is_empty() {
            return Self {
                value: f64::INFINITY,
                optimal_s: 0.5,
            };
        }

        let mut best_val = f64::NEG_INFINITY;
        let mut best_s = 0.0;

        for i in 0..=grid_steps {
            let s = i as f64 / grid_steps as f64;
            let largest_log = common
                .iter()
                .map(|(lp, lq)| s * lp + (1.0 - s) * lq)
                .fold(f64::NEG_INFINITY, f64::max);
            let scaled_sum: f64 = common
                .iter()
                .map(|(lp, lq)| (s * lp + (1.0 - s) * lq - largest_log).exp())
                .sum();
            let val = -(largest_log + scaled_sum.ln());
            if val > best_val {
                best_val = val;
                best_s = s;
            }
        }

        Self {
            value: best_val.max(0.0),
            optimal_s: best_s,
        }
    }

    /// Nominal exponential envelope exp(-n * value), retaining the legacy name.
    ///
    /// This is not a floating-point-certified probability bound. A supplied
    /// public value need not come from any valid testing problem. Zero samples
    /// return the conservative envelope 1, including for disjoint supports.
    pub fn error_probability_bound(&self, n: usize) -> f64 {
        assert!(
            self.value >= 0.0,
            "exponent must be non-negative and not NaN"
        );
        if n == 0 {
            return 1.0;
        }
        (-(n as f64) * self.value).exp()
    }
}
