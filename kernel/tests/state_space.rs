use monad_kernel::state_space::*;

#[test]
fn state_space_creation() {
    let ss = StateSpace::new(Regulator(1024), 16);
    assert_eq!(ss.cardinality_bound(), 1024);
    assert_eq!(ss.dim, 16);
}

#[test]
fn uniform_measure() {
    let m = UniformMeasure { total_states: 100 };
    assert_eq!(m.total(), 100.0);
    assert_eq!(m.measure_of(&[0, 1, 2]), 3.0);
    assert_eq!(m.measure_of(&[0, 0, 1, 2, 2]), 3.0);
    assert_eq!(m.measure_of(&[]), 0.0);
}

#[test]
#[should_panic(expected = "state index out of range")]
fn measure_rejects_nonmembers() {
    UniformMeasure { total_states: 2 }.measure_of(&[2]);
}
