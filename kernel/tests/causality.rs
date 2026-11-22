use monad_kernel::causality::*;
use monad_kernel::observer::ResourceVector;

#[test]
fn total_variation_distance() {
    let tv = TotalVariation;
    let p = vec![0.5, 0.5];
    let q = vec![1.0, 0.0];
    let d = tv.divergence(&p, &q);
    assert!((d - 0.5).abs() < 1e-10);
}

#[test]
fn reliable_record_error_bound() {
    let sr = ReliableRecord {
        event: 0,
        horizon: 10,
        delta: 0.1,
    };
    assert!(sr.has_valid_error_bound());
}

#[test]
fn record_error_domain() {
    for delta in [-1.0, 0.5, 1.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert!(!ReliableRecord {
            event: 0,
            horizon: 0,
            delta
        }
        .has_valid_error_bound());
    }
    assert!(ReliableRecord {
        event: 0,
        horizon: 0,
        delta: 0.0
    }
    .has_valid_error_bound());
}

#[test]
fn direct_lookup_is_not_a_preorder() {
    let mut graph = DirectInfluenceRecords::new(ResourceVector::new(1, 1, 1, 1.0));
    for (cause, effect) in [(0, 1), (1, 2)] {
        graph.add_relation(CausalRelation {
            cause,
            effect,
            distinguishability: 1.0,
            threshold: DetectabilityThreshold(0.5),
        });
    }
    assert!(graph.is_related(0, 1) && graph.is_related(1, 2));
    assert!(!graph.is_related(0, 2));
    assert!(!graph.is_related(0, 0));
}

#[test]
fn recordability_does_not_override_detection_threshold() {
    let d = TotalVariation.divergence(&[0.8, 0.2], &[0.2, 0.8]);
    assert!((d - 0.6).abs() < 1e-12);
    assert!(!CausalRelation {
        cause: 0,
        effect: 0,
        distinguishability: d,
        threshold: DetectabilityThreshold(0.9)
    }
    .is_detected());
}

#[test]
fn detection_rejects_invalid_numbers() {
    for (d, eta) in [
        (0.5, -1.0),
        (-1.0, 0.0),
        (f64::NAN, 0.1),
        (0.5, f64::NAN),
        (f64::INFINITY, f64::INFINITY),
    ] {
        assert!(!CausalRelation {
            cause: 0,
            effect: 1,
            distinguishability: d,
            threshold: DetectabilityThreshold(eta)
        }
        .is_detected());
    }
    assert!(CausalRelation {
        cause: 0,
        effect: 1,
        distinguishability: f64::INFINITY,
        threshold: DetectabilityThreshold(1.0)
    }
    .is_detected());
}

#[test]
#[should_panic(expected = "probabilities must sum to one")]
fn total_variation_rejects_unnormalized_input() {
    TotalVariation.divergence(&[0.2, 0.2], &[0.5, 0.5]);
}

#[test]
fn direct_influence_records_basic() {
    let r = ResourceVector::new(10, 1024, 100, 0.01);
    let mut records = DirectInfluenceRecords::new(r);
    records.add_relation(CausalRelation {
        cause: 0,
        effect: 1,
        distinguishability: 0.3,
        threshold: DetectabilityThreshold(0.1),
    });
    assert!(records.is_related(0, 1));
    assert!(!records.is_related(1, 0));
}
