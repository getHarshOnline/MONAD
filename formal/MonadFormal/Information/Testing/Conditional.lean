import MonadFormal.Information.Testing.Chernoff
import Mathlib.Probability.ConditionalProbability

/-!
# Testing a law against a conditioned version

Paper companion: `paper/MonadFormal/Information/Testing/Conditional.tex`.
A restriction identity identifies the likelihood ratio on a measurable event.
The optimal-risk formula holds on arbitrary measurable observation spaces,
and its product form will expose the scale of moving-support alternatives.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set
open Approximation
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Decide `P` on the declared event and `Q` outside it. -/
noncomputable def eventTest (A : Set X) (hA : MeasurableSet A) : Randomization X Bool := by
  classical
  exact ⟨Kernel.deterministic (fun x ↦ if x ∈ A then false else true)
    (Measurable.ite hA measurable_const measurable_const), inferInstance⟩

/-- The two errors of an event test are the missed `P` mass and the included `Q` mass. -/
theorem eventTest_risk (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (A : Set X) (hA : MeasurableSet A) :
    avgRisk binaryLoss (binaryChannel P Q).val (eventTest A hA).val (π : Measure Bool) =
      (π : Measure Bool) {false} * (P : Measure X) Aᶜ +
        (π : Measure Bool) {true} * (Q : Measure X) A := by
  classical
  rw [binary_avgRisk]
  have hp : (fun x ↦ if x ∈ A then false else true) ⁻¹' {true} = Aᶜ := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hq : (fun x ↦ if x ∈ A then false else true) ⁻¹' {false} = A := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hf : Measurable (fun x ↦ if x ∈ A then false else true) :=
    Measurable.ite hA measurable_const measurable_const
  dsimp only [eventTest]
  rw [Measure.deterministic_comp_eq_map, Measure.deterministic_comp_eq_map,
    Measure.map_apply hf (measurableSet_singleton true),
    Measure.map_apply hf (measurableSet_singleton false), hp, hq]

/-- A constant decision bounds optimal error by the mass of the other hypothesis. -/
theorem binaryError_le_prior_false (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool) :
    binaryError P Q π ≤ (π : Measure Bool) {false} := by
  have he := bayesRisk_le_avgRisk binaryLoss (binaryChannel P Q).val
    (eventTest ∅ MeasurableSet.empty).val (π : Measure Bool)
  simpa [eventTest_risk, binaryError] using he

/-- A restriction likelihood identity determines the optimal error, not merely one test's risk. -/
theorem binaryError_eq_min_of_restrict (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    {A : Set X} (hA : MeasurableSet A) (hP : (P : Measure X) A = 1)
    (hQ : (Q : Measure X).restrict A = (Q : Measure X) A • (P : Measure X)) :
    binaryError P Q π = min ((π : Measure Bool) {false})
      ((π : Measure Bool) {true} * (Q : Measure X) A) := by
  apply le_antisymm
  · apply le_min (binaryError_le_prior_false P Q π)
    have he := bayesRisk_le_avgRisk binaryLoss (binaryChannel P Q).val
      (eventTest A hA).val (π : Measure Bool)
    have hc : (P : Measure X) Aᶜ = 0 := by
      rw [measure_compl hA (measure_ne_top _ _), measure_univ, hP, tsub_self]
    simpa [eventTest_risk, hc, binaryError] using he
  · change _ ≤ ⨅ (D : Kernel X Bool) (_ : IsMarkovKernel D), _
    refine le_iInf₂ fun D hD ↦ ?_
    rw [binary_avgRisk P Q π ⟨D, hD⟩]
    have hdom : (Q : Measure X) A • (P : Measure X) ≤ (Q : Measure X) := by
      rw [← hQ]
      exact Measure.restrict_le_self
    have htest : (Q : Measure X) A * (D ∘ₘ (P : Measure X)) {false} ≤
        (D ∘ₘ (Q : Measure X)) {false} := by
      change ((Q : Measure X) A • (D ∘ₘ (P : Measure X))) {false} ≤ _
      rw [← Measure.comp_smul]
      simp only [Measure.bind_apply (measurableSet_singleton false) D.aemeasurable]
      exact lintegral_mono' hdom le_rfl
    have hd : (D ∘ₘ (P : Measure X)) {true} + (D ∘ₘ (P : Measure X)) {false} = 1 := by
      rw [← measure_union (by simp) (measurableSet_singleton false)]
      have hu : ({true} : Set Bool) ∪ {false} = univ := by ext b; cases b <;> simp
      rw [hu, measure_univ]
    calc
      _ = min ((π : Measure Bool) {false}) ((π : Measure Bool) {true} * (Q : Measure X) A) *
          ((D ∘ₘ (P : Measure X)) {true} + (D ∘ₘ (P : Measure X)) {false}) := by rw [hd, mul_one]
      _ ≤ (π : Measure Bool) {false} * (D ∘ₘ (P : Measure X)) {true} +
          ((π : Measure Bool) {true} * (Q : Measure X) A) * (D ∘ₘ (P : Measure X)) {false} := by
        rw [mul_add]
        exact add_le_add (mul_le_mul' (min_le_left _ _) le_rfl)
          (mul_le_mul' (min_le_right _ _) le_rfl)
      _ ≤ _ := by rw [mul_assoc]; exact add_le_add le_rfl (mul_le_mul' le_rfl htest)

/-- A restriction likelihood identity multiplies under independent repetition. -/
theorem iid_restrict_eq_smul (P Q : ProbabilityMeasure X) {A : Set X}
    (hQ : (Q : Measure X).restrict A = (Q : Measure X) A • (P : Measure X)) (n : ℕ) :
    (iidLaw Q n : Measure (Fin n → X)).restrict (univ.pi fun _ ↦ A) =
      (Q : Measure X) A ^ n • (iidLaw P n : Measure (Fin n → X)) := by
  change (Measure.pi fun _ : Fin n ↦ (Q : Measure X)).restrict _ = _
  rw [Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s hs
  simp [Measure.smul_apply, iidLaw, Measure.pi_pi, hQ, smul_eq_mul,
    Finset.prod_mul_distrib]

/-- Exact finite-sample error for conditioning on a measurable event, on any observation space. -/
theorem binaryError_iid_eq_min_of_restrict (P Q : ProbabilityMeasure X)
    (π : ProbabilityMeasure Bool) {A : Set X} (hA : MeasurableSet A)
    (hP : (P : Measure X) A = 1)
    (hQ : (Q : Measure X).restrict A = (Q : Measure X) A • (P : Measure X)) (n : ℕ) :
    binaryError (iidLaw P n) (iidLaw Q n) π = min ((π : Measure Bool) {false})
      ((π : Measure Bool) {true} * (Q : Measure X) A ^ n) := by
  have hmass (R : ProbabilityMeasure X) :
      (iidLaw R n : Measure (Fin n → X)) (univ.pi fun _ ↦ A) = (R : Measure X) A ^ n := by
    simp [iidLaw, Measure.pi_pi]
  have hp : (iidLaw P n : Measure (Fin n → X)) (univ.pi fun _ ↦ A) = 1 := by
    rw [hmass, hP, one_pow]
  simpa only [hmass] using binaryError_eq_min_of_restrict (iidLaw P n) (iidLaw Q n) π
    (MeasurableSet.univ_pi fun _ ↦ hA) hp (by rw [hmass]; exact iid_restrict_eq_smul P Q hQ n)

end MonadFormal.Information
