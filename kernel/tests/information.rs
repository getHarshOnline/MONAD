use monad_kernel::information::*;

#[test]
fn channel_capacity_in_nats() {
    // One bit per use is ln(2) nats per use. The constructor accepts nats.
    let c = ChannelCapacityNats::new(std::f64::consts::LN_2);
    assert_eq!(c.nats_per_use, std::f64::consts::LN_2);
}

#[test]
fn chernoff_identical_distributions() {
    let p = vec![0.5, 0.5];
    let q = vec![0.5, 0.5];
    let ci = ChernoffInformation::compute(&p, &q, 100);
    // Identical distributions => Chernoff info = 0
    assert!(ci.value.abs() < 1e-10);
}

#[test]
fn chernoff_distinct_distributions() {
    let p = vec![0.9, 0.1];
    let q = vec![0.1, 0.9];
    let ci = ChernoffInformation::compute(&p, &q, 1000);
    // Very different distributions => positive Chernoff info
    assert!(ci.value > 0.0);
    // Error bound should decay with n
    assert!(ci.error_probability_bound(100) < ci.error_probability_bound(10));
}

#[test]
fn symmetric_binary_reference_value() {
    let ci = ChernoffInformation::compute(&[0.9, 0.1], &[0.1, 0.9], 100);
    assert!((ci.value + 0.6_f64.ln()).abs() < 1e-12);
    assert!((ci.optimal_s - 0.5).abs() < 1e-12);
}

#[test]
fn support_endpoint_uses_the_interior_limit() {
    let ci = ChernoffInformation::compute(&[1.0, 0.0], &[0.5, 0.5], 2);
    assert!((ci.value - 2.0_f64.ln()).abs() < 1e-12);
    assert_eq!(ci.optimal_s, 0.0);
}

#[test]
fn disjoint_support_and_zero_samples() {
    let ci = ChernoffInformation::compute(&[1.0, 0.0], &[0.0, 1.0], 2);
    assert_eq!(ci.value, f64::INFINITY);
    assert_eq!(ci.error_probability_bound(0), 1.0);
    assert_eq!(ci.error_probability_bound(1), 0.0);
}

#[test]
fn tiny_overlap_stays_finite() {
    let tiny = 1e-300;
    let ci = ChernoffInformation::compute(&[1.0, tiny, 0.0], &[0.0, tiny, 1.0], 2);
    assert!(ci.value.is_finite());
    assert!((ci.value + tiny.ln()).abs() < 1e-10);
}

#[test]
#[should_panic(expected = "nonempty")]
fn rejects_empty_distributions() {
    ChernoffInformation::compute(&[], &[], 2);
}

#[test]
#[should_panic]
fn rejects_invalid_mass() {
    ChernoffInformation::compute(&[0.8, 0.8], &[0.5, 0.5], 2);
}

#[test]
#[should_panic]
fn rejects_nan_probabilities() {
    ChernoffInformation::compute(&[f64::NAN, 0.0], &[0.5, 0.5], 2);
}

#[test]
#[should_panic]
fn rejects_infinite_capacity_in_finite_value_holder() {
    ChannelCapacityNats::new(f64::INFINITY);
}
