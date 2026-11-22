//! Numeric comparisons with the mathematical definitions, not proofs of Rust.

use monad_kernel::causality::{
    CausalRelation, DetectabilityThreshold, DirectInfluenceRecords, Distinguishability,
    TotalVariation,
};
use monad_kernel::information::ChernoffInformation;
use monad_kernel::observer::ResourceVector;

#[test]
fn total_variation_matches_event_supremum() {
    // Enumerate events rather than repeating the implementation's L1 formula.
    // Lean: MonadFormal.Approximation.tv_eq_eventTV.
    let cases: &[(&[f64], &[f64], f64)] = &[
        (&[0.1, 0.2, 0.3, 0.4], &[0.4, 0.3, 0.2, 0.1], 0.4),
        (&[0.25, 0.25, 0.5], &[0.5, 0.25, 0.25], 0.25),
        (&[1.0, 0.0, 0.0], &[0.0, 0.0, 1.0], 1.0),
        (&[0.0, 1.0], &[0.0, 1.0], 0.0),
    ];
    for &(p, q, expected) in cases {
        let event_distance = (0..1_usize << p.len())
            .map(|mask| {
                let mass = |law: &[f64]| {
                    law.iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, value)| value)
                        .sum::<f64>()
                };
                (mass(p) - mass(q)).abs()
            })
            .fold(0.0_f64, f64::max);
        assert!((event_distance - expected).abs() < 1e-12);
        assert!((TotalVariation.divergence(p, q) - event_distance).abs() < 1e-12);
        assert!((TotalVariation.divergence(q, p) - event_distance).abs() < 1e-12);
    }
}

#[test]
fn chernoff_grid_matches_independent_reference_values() {
    // Evaluate -ln(sum(p_i^s q_i^(1-s))) directly at s = j/steps with
    // 70-digit decimal arithmetic, rather than the implementation's log-sum-exp.
    // The stored answer is the best grid point, not the continuous optimum.
    // Lean: MonadFormal.Information.chernoffInfo.
    let cases: &[(&[f64], &[f64], usize, usize, f64)] = &[
        (&[0.8, 0.2], &[0.3, 0.7], 4, 2, 0.1461088008182597),
        (&[0.99, 0.01], &[0.4, 0.6], 7, 3, 0.36583872320405475),
        (&[0.7, 0.2, 0.1], &[0.1, 0.3, 0.6], 5, 3, 0.2726061007168323),
    ];
    for &(p, q, steps, best_index, expected) in cases {
        let result = ChernoffInformation::compute(p, q, steps);
        assert!((result.value - expected).abs() < 1e-12);
        assert!((result.optimal_s - best_index as f64 / steps as f64).abs() < 1e-15);
    }
}

#[test]
fn xor_interventions_cancel_the_end_to_end_effect() {
    // The actual deterministic mechanisms from MonadFormal.intA/intB and
    // the zero preparation in MonadFormal.model. Only these intervention
    // pairs are compared; no arbitrary causal-identification claim follows.
    let prep = [false; 3];
    let int_a = |a: bool| [a, a, false];
    let int_b = |b: bool| [prep[0], b, prep[0] ^ b];
    let record_law = |bit: bool| if bit { [0.0, 1.0] } else { [1.0, 0.0] };
    let mut observations = DirectInfluenceRecords::new(ResourceVector::new(1, 1, 1, 1.0));
    for (cause, effect, high, low, expected) in [
        (0, 1, int_a(true), int_a(false), 1.0),
        (1, 2, int_b(true), int_b(false), 1.0),
        (0, 2, int_a(true), int_a(false), 0.0),
    ] {
        let divergence =
            TotalVariation.divergence(&record_law(high[effect]), &record_law(low[effect]));
        assert_eq!(divergence, expected);
        observations.add_relation(CausalRelation {
            cause,
            effect,
            distinguishability: divergence,
            threshold: DetectabilityThreshold(0.5),
        });
    }
    assert!(observations.is_related(0, 1));
    assert!(observations.is_related(1, 2));
    // A→C is stored with zero effect; lookup must not derive it from the path.
    assert_eq!(observations.relations.len(), 3);
    assert!(!observations.is_related(0, 2));
    assert!(!observations.is_related(0, 0));
}
