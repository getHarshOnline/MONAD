//! What an observer may do and with what resources: the interfaces a consuming
//! crate implements to coarse-grain a state space, record a channel's output and
//! declare its allowed operations, and the budget those operations run under.
//!
//! It builds on [`crate::state_space::StateIndex`], and [`crate::causality`]
//! records influence against its [`ResourceVector`]. Observation and allowed
//! operations may lose information; the traits alone prove neither
//! irreversibility nor protocol monotonicity.

use crate::state_space::StateIndex;

/// An index returned by a coarse-graining implementation.
///
/// Lean: none. Its encoding and valid range are chosen by the implementation.
pub type MacroIndex = usize;

/// A record encoded as a 64-bit unsigned integer.
///
/// Lean: none. This machine encoding is not a formal record law.
pub type RecordValue = u64;

/// Resource budgets supplied by the caller.
///
/// The referenced influence theorem requires inclusion of permitted protocols
/// and the same preparation state. Comparing these numeric fields establishes
/// neither premise; the energy/precision convention remains profile-specific.
///
/// Lean: `MonadFormal.influences_mono`.
#[derive(Debug, Clone, PartialEq)]
pub struct ResourceVector {
    /// Maximum number of record slots.
    pub max_slots: usize,
    /// Maximum bytes of storage.
    pub max_bytes: usize,
    /// Maximum tokens (or time steps).
    pub max_tokens: usize,
    /// Legacy application-defined energy/precision coordinate. Its unit and
    /// ordering must be declared by a profile; precision and energy are not
    /// interchangeable. This four-field type does not encode the paper's
    /// separate repeated-trial budget.
    pub epsilon: f64,
}

impl ResourceVector {
    pub fn new(max_slots: usize, max_bytes: usize, max_tokens: usize, epsilon: f64) -> Self {
        Self {
            max_slots,
            max_bytes,
            max_tokens,
            epsilon,
        }
    }

    /// Whether each numeric budget in self is at most the corresponding one in other.
    /// This does not prove inclusion of channels, operations, or protocols.
    pub fn fits_within(&self, other: &ResourceVector) -> bool {
        self.epsilon.is_finite()
            && other.epsilon.is_finite()
            && self.epsilon >= 0.0
            && other.epsilon >= 0.0
            && self.max_slots <= other.max_slots
            && self.max_bytes <= other.max_bytes
            && self.max_tokens <= other.max_tokens
            && self.epsilon <= other.epsilon
    }
}

/// An interface for mapping state indices to macrostate indices.
///
/// A chosen projection can supply a probe in the referenced family. The caller
/// must establish its range, partition and any claimed surjectivity.
///
/// Lean: `MonadFormal.ProbeFamily`.
pub trait CoarseGraining {
    /// Map a microstate to a macrostate (deterministic projection).
    fn project(&self, state: StateIndex) -> MacroIndex;

    /// Number of macrostates |M_s|.
    fn num_macrostates(&self) -> usize;
}

/// An interface for obtaining a record from a macrostate and resource budget.
///
/// The referenced formal channel is a probability-preserving Markov kernel.
/// Returning one record here supplies neither that law nor a proof of it.
///
/// Lean: `MonadFormal.Approximation.Randomization`.
pub trait RecordChannel {
    /// Record a macrostate observation, returning a (possibly noisy) record value.
    fn record(&self, macro_state: MacroIndex, resources: &ResourceVector) -> RecordValue;
}

/// An interface for checking and applying named operations.
///
/// The referenced profile declares allowed transformations and a preparation
/// state. An implementation must supply that interpretation and separately
/// justify any claim that more resources permit every earlier operation.
///
/// Lean: `MonadFormal.Profile`.
pub trait AllowedOps {
    /// Check whether an operation (identified by name/id) is permitted
    /// under the given resources.
    fn is_allowed(&self, operation_id: &str, resources: &ResourceVector) -> bool;

    /// Apply an allowed operation to a state.
    /// Returns None if the operation is not allowed under the given resources.
    fn apply(
        &self,
        operation_id: &str,
        state: StateIndex,
        resources: &ResourceVector,
    ) -> Option<StateIndex>;
}
