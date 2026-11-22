//! The causal part of MONAD's vocabulary: which interventions are detectable,
//! how distinguishable two outcome distributions are, and metadata for reliable
//! records.
//!
//! Research crates that depend on `monad-kernel`, such as MUON and HENA, re-export it
//! to store and compare observed influence once their own models exist; [`crate::information`] reuses its
//! probability check, and its influence records carry the
//! [`crate::observer::ResourceVector`] they were observed under.
//!
//! [`DirectInfluenceRecords`] performs direct-pair lookup only: it supplies
//! neither reflexivity nor transitivity. Resource monotonicity requires
//! inclusion of complete witness protocols, not merely comparison of
//! resource-vector fields.

use crate::observer::ResourceVector;

/// Validate a finite probability vector, with absolute normalization tolerance
/// 1e-10 for floating-point input. This is input validation, not exact arithmetic.
pub(crate) fn assert_probability_vector(p: &[f64]) {
    assert!(!p.is_empty(), "probability vector must be nonempty");
    assert!(
        p.iter().all(|x| x.is_finite() && *x >= 0.0 && *x <= 1.0),
        "probabilities must be finite and in [0, 1]"
    );
    assert!(
        (p.iter().sum::<f64>() - 1.0).abs() <= 1e-10,
        "probabilities must sum to one"
    );
}

/// An identifier that a caller associates with an event.
///
/// The formal event is a Boolean predicate on a carrier; an integer alone
/// does not supply that predicate or its meaning.
///
/// Lean: `MonadFormal.Event`.
pub type EventId = usize;

/// An interface for a divergence between finite probability vectors.
///
/// Implementations choose their own quantity and assumptions. Total variation,
/// KL divergence and Hellinger distance do not have interchangeable bounds.
///
/// Lean: none. This generic trait does not select a particular Lean divergence.
pub trait Distinguishability {
    /// Compute the divergence between two distributions represented as
    /// probability vectors.
    fn divergence(&self, p: &[f64], q: &[f64]) -> f64;
}

/// Total variation: half the sum of absolute coordinate differences.
///
/// The reference defines the quantity for probability measures through bounded
/// measurable tests. This implementation uses floating-point vectors with equal
/// nonzero length and mass within 1e-10 of one; invalid inputs panic. A resolved
/// reference is not a proof of the floating-point implementation.
///
/// Lean: `MonadFormal.Approximation.tv`.
#[derive(Debug, Clone, Copy)]
pub struct TotalVariation;

impl Distinguishability for TotalVariation {
    fn divergence(&self, p: &[f64], q: &[f64]) -> f64 {
        assert_eq!(p.len(), q.len(), "distribution length mismatch");
        assert_probability_vector(p);
        assert_probability_vector(q);
        0.5 * p
            .iter()
            .zip(q.iter())
            .map(|(a, b)| (a - b).abs())
            .sum::<f64>()
    }
}

/// An event identifier and the value a caller intends to set.
///
/// The formal intervention also requires an allowed transformation that sets
/// the event on every state. These fields do not contain that witness.
///
/// Lean: `MonadFormal.Interv`.
#[derive(Debug, Clone)]
pub struct Intervention {
    /// The event being intervened on.
    pub event: EventId,
    /// The value set by the intervention (0 or 1 for binary events).
    pub value: u8,
}

/// Metadata for a claimed reliable record.
///
/// Reliability needs a decision rule whose type-I and type-II errors are at
/// most delta, with 0 <= delta < 1/2. These fields contain no decision rule,
/// trial evidence or persistence proof; `has_valid_error_bound` checks only delta.
///
/// Lean: none. A reliable-record decision rule has not been formalised here.
#[derive(Debug, Clone)]
pub struct ReliableRecord {
    /// The event this record witnesses.
    pub event: EventId,
    /// The horizon (time steps) at which the record is evaluated.
    pub horizon: usize,
    /// Error bound 0 <= delta < 1/2.
    pub delta: f64,
}

impl ReliableRecord {
    /// Check the claimed error bound's numerical domain. This does not verify
    /// the claim, its trial budget, or temporal persistence.
    pub fn has_valid_error_bound(&self) -> bool {
        self.delta.is_finite() && (0.0..0.5).contains(&self.delta)
    }
}

/// A threshold supplied for a particular divergence and protocol.
///
/// A detected observation requires divergence at least this value. No universal
/// sample-size scaling or error guarantee follows from the number.
///
/// Lean: none. The deterministic Lean influence model uses unequal records, not this threshold.
#[derive(Debug, Clone, Copy)]
pub struct DetectabilityThreshold(pub f64);

/// An observed divergence and threshold for an ordered pair of event IDs.
///
/// The referenced deterministic influence relation requires admissible
/// intervention witnesses and a changed record. These numeric observations
/// do not establish those witnesses or identify a causal effect.
///
/// Lean: `MonadFormal.Influences`.
#[derive(Debug, Clone)]
pub struct CausalRelation {
    /// Cause event.
    pub cause: EventId,
    /// Effect event.
    pub effect: EventId,
    /// The measured distinguishability D(P(y|do(A=1)), P(y|do(A=0))).
    pub distinguishability: f64,
    /// The threshold eta.
    pub threshold: DetectabilityThreshold,
}

impl CausalRelation {
    /// Whether the recorded numbers meet D >= eta. Divergence may be positive
    /// infinity (for example KL on incompatible supports); eta must be finite
    /// and nonnegative. A zero threshold also accepts zero divergence and is
    /// not evidence of a strictly positive effect.
    pub fn is_detected(&self) -> bool {
        !self.distinguishability.is_nan()
            && self.distinguishability >= 0.0
            && self.threshold.0.is_finite()
            && self.threshold.0 >= 0.0
            && self.distinguishability >= self.threshold.0
    }
}

/// A container of direct intervention-influence observations.
///
/// It performs exact-pair lookup, with no reflexive or transitive closure.
/// The referenced finite model shows that non-transitivity can be exact.
/// Closure-added pairs would describe reachability, not measured influence.
///
/// Lean: `MonadFormal.not_influences_A_C`.
#[derive(Debug, Clone)]
pub struct DirectInfluenceRecords {
    /// Resource metadata for these observations; not a protocol witness.
    pub resources: ResourceVector,
    /// Observed pairs, including observations below their thresholds.
    pub relations: Vec<CausalRelation>,
}

impl DirectInfluenceRecords {
    pub fn new(resources: ResourceVector) -> Self {
        Self {
            resources,
            relations: Vec::new(),
        }
    }

    /// Store an observation. Detection is checked by `is_related`.
    pub fn add_relation(&mut self, relation: CausalRelation) {
        self.relations.push(relation);
    }

    /// Check whether the exact ordered pair has a detected observation.
    pub fn is_related(&self, cause: EventId, effect: EventId) -> bool {
        self.relations
            .iter()
            .any(|r| r.cause == cause && r.effect == effect && r.is_detected())
    }
}
