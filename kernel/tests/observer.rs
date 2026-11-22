use monad_kernel::observer::*;

#[test]
fn resource_vector_subsumption() {
    let small = ResourceVector::new(10, 1024, 100, 0.01);
    let large = ResourceVector::new(100, 10240, 1000, 0.1);
    assert!(small.fits_within(&large));
    assert!(!large.fits_within(&small));
}
