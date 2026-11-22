import MonadFormal.Information.Testing.Chernoff
import Mathlib.Probability.Moments.Variance

/-!
# Independent-sample concentration

Paper companion: `paper/MonadFormal/Information/Testing/Sampling.tex`.
The probability space is the actual finite product law from `iidLaw`.
Mean and variance scaling follow from its coordinate marginals and
independence, rather than being assumptions about a sample statistic.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]

/-- Sum of a real statistic across an independent sample. -/
def sampleSum (f : X → ℝ) (n : ℕ) (x : Fin n → X) : ℝ := ∑ i, f (x i)

theorem integral_sampleSum (P : ProbabilityMeasure X) (f : X → ℝ) (n : ℕ) :
    (∫ x, sampleSum f n x ∂(iidLaw P n : Measure (Fin n → X))) =
      n * ∫ x, f x ∂(P : Measure X) := by
  unfold sampleSum
  rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  have he (i : Fin n) :
      (∫ x : Fin n → X, f (x i) ∂(iidLaw P n : Measure (Fin n → X))) =
        ∫ x, f x ∂(P : Measure X) := by
    have hm := measurePreserving_eval (fun _ : Fin n ↦ (P : Measure X)) i
    change (∫ x, f (Function.eval i x) ∂Measure.pi (fun _ : Fin n ↦ (P : Measure X))) = _
    rw [← integral_map hm.aemeasurable AEStronglyMeasurable.of_discrete, hm.map_eq]
  simp_rw [he]
  simp

theorem variance_sampleSum (P : ProbabilityMeasure X) (f : X → ℝ) (n : ℕ) :
    variance (sampleSum f n) (iidLaw P n : Measure (Fin n → X)) =
      n * variance f (P : Measure X) := by
  have hv := variance_sum_pi (μ := fun _ : Fin n ↦ (P : Measure X))
    (X := fun _ ↦ f) (fun _ ↦ MemLp.of_discrete)
  convert hv using 1
  · congr 1
    ext x
    simp [sampleSum]
  · simp

/-- Chebyshev concentration around the actual one-sample mean. -/
theorem iid_deviation_le (P : ProbabilityMeasure X) (f : X → ℝ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (iidLaw P n : Measure (Fin n → X))
      {x | n * ε ≤ |sampleSum f n x - n * ∫ y, f y ∂(P : Measure X)|} ≤
      ENNReal.ofReal (variance f (P : Measure X) / (n * ε ^ 2)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hb := meas_ge_le_variance_div_sq (μ := (iidLaw P n : Measure (Fin n → X)))
    (X := sampleSum f n) MemLp.of_discrete (mul_pos hn' hε)
  rw [integral_sampleSum, variance_sampleSum] at hb
  convert hb using 1
  congr 1
  field_simp

/-- A finite-sample typical set has at least half the probability once the variance bound permits it. -/
theorem iid_typical_ge_half (P : ProbabilityMeasure X) (f : X → ℝ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (hv : 2 * variance f (P : Measure X) ≤ n * ε ^ 2) :
    1 / 2 ≤ (iidLaw P n : Measure (Fin n → X)).real
      {x | |sampleSum f n x - n * ∫ y, f y ∂(P : Measure X)| < n * ε} := by
  have hb := iid_deviation_le P f hn hε
  have hratio : variance f (P : Measure X) / (n * ε ^ 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos hε))).mpr
    linarith
  have hreal := ENNReal.toReal_mono (by finiteness)
    (hb.trans (ENNReal.ofReal_le_ofReal hratio))
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hreal
  have he := measureReal_add_measureReal_compl (μ := (iidLaw P n : Measure (Fin n → X)))
    (s := {x | n * ε ≤ |sampleSum f n x - n * ∫ y, f y ∂(P : Measure X)|})
    (Set.to_countable _).measurableSet
  simp only [probReal_univ, compl_ofPred, not_le] at he
  change (iidLaw P n : Measure (Fin n → X)).real _ ≤ 1 / 2 at hreal
  linarith

end MonadFormal.Information
