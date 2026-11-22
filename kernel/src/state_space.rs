//! The state space a consuming crate observes: a finite indexed carrier with a
//! cardinality bound, a measure on it and an evolution law for a regulated
//! closed world.
//!
//! It is the base of the crate, and [`crate::observer`] indexes its coarse
//! graining by [`StateIndex`]. This finite-carrier projection does not represent
//! every finite-measure or finite-dimensional space. Evolution laws are
//! obligations on trait implementations; the trait itself is not their proof.

use std::fmt;

/// An index used by the finite Rust carrier.
///
/// Lean: none. Formal carriers are arbitrary types, not these machine indices.
pub type StateIndex = usize;

/// The finite cardinality bound supplied by the caller.
///
/// Lean: none. The library has no regulator metadata type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Regulator(pub usize);

/// Finite carrier metadata: a cardinality bound and a vector dimension.
///
/// Construction does not check nonzero size, valid indices, a measure or dynamics.
///
/// Lean: none. This metadata is not a formal state-space construction.
#[derive(Debug, Clone)]
pub struct StateSpace {
    /// The regulator interpreted here as a cardinality bound.
    pub regulator: Regulator,
    /// Dimensionality of the state vectors.
    pub dim: usize,
}

impl StateSpace {
    /// Create a new regulated state space with regulator N and dimension d.
    pub fn new(regulator: Regulator, dim: usize) -> Self {
        Self { regulator, dim }
    }

    /// Cardinality bound: |X^(N)| < infinity.
    pub fn cardinality_bound(&self) -> usize {
        self.regulator.0
    }
}

impl fmt::Display for StateSpace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X^({}), dim={}", self.regulator.0, self.dim)
    }
}

/// An interface for measuring subsets of a finite indexed carrier.
///
/// Implementations must establish their measure laws. This trait does not
/// represent general Liouville, Haar, density-integral or quantum semantics.
///
/// Lean: none. No correspondence from this trait to a Lean measure is proved.
pub trait Measure {
    /// Measure of a subset identified by state indices.
    fn measure_of(&self, subset: &[StateIndex]) -> f64;

    /// Total measure of X^(N).
    fn total(&self) -> f64;
}

/// Counting measure on the indices below `total_states`.
///
/// Repeated indices count once. The total is the number of states, not a
/// normalised probability mass. Out-of-range indices panic.
///
/// Lean: none. The Rust subset/counting implementation has no formal binding.
#[derive(Debug, Clone)]
pub struct UniformMeasure {
    pub total_states: usize,
}

impl Measure for UniformMeasure {
    fn measure_of(&self, subset: &[StateIndex]) -> f64 {
        assert!(
            subset.iter().all(|i| *i < self.total_states),
            "state index out of range"
        );
        subset
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .len() as f64
    }

    fn total(&self) -> f64 {
        self.total_states as f64
    }
}

/// An interface for forward and inverse evolution of a state index.
///
/// Implementations must be bijective and measure-preserving, compose over
/// time and act as the identity at time zero. The referenced conservation
/// theorem assumes those laws; this trait does not prove them.
///
/// Lean: `MonadFormal.Entropy.observable_conservation`.
pub trait Evolution {
    /// Apply the evolution for time step dt to a state index.
    fn evolve(&self, state: StateIndex, dt: f64) -> StateIndex;

    /// Apply the inverse evolution (Phi_{-dt}).
    fn evolve_inverse(&self, state: StateIndex, dt: f64) -> StateIndex;
}
