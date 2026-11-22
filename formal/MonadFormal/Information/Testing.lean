import MonadFormal.Information
import Mathlib.Probability.Decision.Risk.Countable
import Mathlib.Probability.Decision.Risk.Basic

/-!
# Optimal binary testing

Paper companion: `paper/MonadFormal/Information/Testing.tex`.
The error is the library's Bayes risk over all Markov decision kernels.
The finite-alphabet overlap formula is derived from that optimization,
not used as a substitute definition of optimality.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set
open Approximation
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Hypothesis `false` generates `P`; hypothesis `true` generates `Q`. -/
noncomputable def binaryChannel (P Q : ProbabilityMeasure X) : Randomization Bool X :=
  ⟨Kernel.ofFunOfCountable (fun h ↦ if h then (Q : Measure X) else (P : Measure X)),
    ⟨fun h ↦ by
      cases h
      · change IsProbabilityMeasure (P : Measure X)
        infer_instance
      · change IsProbabilityMeasure (Q : Measure X)
        infer_instance⟩⟩

/-- Unit loss for an incorrect binary decision. -/
def binaryLoss (h d : Bool) : ℝ≥0∞ := if h = d then 0 else 1

/-- Optimal probability of error over all randomized tests, with the declared prior. -/
noncomputable def binaryError (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool) : ℝ≥0∞ :=
  bayesRisk binaryLoss (binaryChannel P Q).val (π : Measure Bool)

theorem binary_avgRisk (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (D : Randomization X Bool) :
    avgRisk binaryLoss (binaryChannel P Q).val D.val (π : Measure Bool) =
      (π : Measure Bool) {false} * (D.val ∘ₘ (P : Measure X)) {true} +
      (π : Measure Bool) {true} * (D.val ∘ₘ (Q : Measure X)) {false} := by
  simp [avgRisk, lintegral_fintype, binaryLoss, binaryChannel,
    Kernel.ofFunOfCountable, Kernel.comp_apply, mul_comm, add_comm]

section Finite

variable [Fintype X] [MeasurableSingletonClass X]

/-- On a finite alphabet, risk retains both conditional decision probabilities. -/
theorem binary_avgRisk_finite (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (D : Randomization X Bool) :
    avgRisk binaryLoss (binaryChannel P Q).val D.val (π : Measure Bool) =
      ∑ x, ((π : Measure Bool) {false} * (P : Measure X) {x} * D.val x {true} +
        (π : Measure Bool) {true} * (Q : Measure X) {x} * D.val x {false}) := by
  rw [binary_avgRisk, Measure.bind_apply (measurableSet_singleton true) (Kernel.aemeasurable _),
    Measure.bind_apply (measurableSet_singleton false) (Kernel.aemeasurable _)]
  simp only [lintegral_fintype, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  ext x
  ring

/-- Choose the more probable hypothesis after weighting by its prior; ties choose `Q`. -/
noncomputable def likelihoodTest (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool) :
    Randomization X Bool := by
  classical
  exact ⟨Kernel.deterministic
    (fun x ↦ decide ((π : Measure Bool) {false} * (P : Measure X) {x} ≤
      (π : Measure Bool) {true} * (Q : Measure X) {x}))
    (measurable_of_countable _), inferInstance⟩

theorem likelihoodTest_risk (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool) :
    avgRisk binaryLoss (binaryChannel P Q).val (likelihoodTest P Q π).val (π : Measure Bool) =
      ∑ x, min ((π : Measure Bool) {false} * (P : Measure X) {x})
        ((π : Measure Bool) {true} * (Q : Measure X) {x}) := by
  classical
  rw [binary_avgRisk_finite]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (π : Measure Bool) {false} * (P : Measure X) {x} ≤
      (π : Measure Bool) {true} * (Q : Measure X) {x}
  · simp [likelihoodTest, Kernel.deterministic_apply, h]
  · simp [likelihoodTest, Kernel.deterministic_apply, h, min_eq_right (le_of_not_ge h)]

/-- The likelihood-ratio rule attains the optimum; randomization cannot lower its error. -/
theorem binaryError_eq_overlap (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool) :
    binaryError P Q π = ∑ x, min ((π : Measure Bool) {false} * (P : Measure X) {x})
      ((π : Measure Bool) {true} * (Q : Measure X) {x}) := by
  apply le_antisymm
  · exact (bayesRisk_le_avgRisk binaryLoss (binaryChannel P Q).val
      (likelihoodTest P Q π).val (π : Measure Bool)).trans_eq (likelihoodTest_risk P Q π)
  · change _ ≤ ⨅ (D : Kernel X Bool) (_ : IsMarkovKernel D), _
    refine le_iInf₂ fun D hD ↦ ?_
    rw [binary_avgRisk_finite P Q π ⟨D, hD⟩]
    apply Finset.sum_le_sum
    intro x _
    have hd : D x {true} + D x {false} = 1 := by
      rw [← measure_union (by simp) (measurableSet_singleton false)]
      have hu : ({true} : Set Bool) ∪ {false} = univ := by ext b; cases b <;> simp
      rw [hu, measure_univ]
    calc
      _ = min ((π : Measure Bool) {false} * (P : Measure X) {x})
          ((π : Measure Bool) {true} * (Q : Measure X) {x}) * (D x {true} + D x {false}) :=
        by rw [hd, mul_one]
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul' (min_le_left _ _) le_rfl)
          (mul_le_mul' (min_le_right _ _) le_rfl)

/-- The real-valued overlap formula is valid because all atom masses are finite. -/
theorem binaryError_toReal (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool) :
    (binaryError P Q π).toReal =
      ∑ x, min ((π : Measure Bool).real {false} * (P : Measure X).real {x})
        ((π : Measure Bool).real {true} * (Q : Measure X).real {x}) := by
  have hf (x : X) : (π : Measure Bool) {false} * (P : Measure X) {x} ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have ht (x : X) : (π : Measure Bool) {true} * (Q : Measure X) {x} ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [binaryError_eq_overlap, ENNReal.toReal_sum
    (fun x _ ↦ ne_top_of_le_ne_top (hf x) (min_le_left _ _))]
  simp only [ENNReal.toReal_min (hf _) (ht _), ENNReal.toReal_mul, measureReal_def]

/-- A pointwise lower bound on any event gives a lower bound on optimal error. -/
theorem binaryError_lower_bound (P Q R : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (A : Set X) (c : ℝ) (h : ∀ x ∈ A, c * (R : Measure X).real {x} ≤
      min ((π : Measure Bool).real {false} * (P : Measure X).real {x})
        ((π : Measure Bool).real {true} * (Q : Measure X).real {x})) :
    c * (R : Measure X).real A ≤ (binaryError P Q π).toReal := by
  classical
  rw [binaryError_toReal]
  calc
    c * (R : Measure X).real A = ∑ x ∈ A.toFinset, c * (R : Measure X).real {x} := by
      rw [← Finset.mul_sum, sum_measureReal_singleton]
      simp
    _ ≤ ∑ x ∈ A.toFinset,
        min ((π : Measure Bool).real {false} * (P : Measure X).real {x})
          ((π : Measure Bool).real {true} * (Q : Measure X).real {x}) :=
      Finset.sum_le_sum fun x hx ↦ h x (mem_toFinset.mp hx)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ ↦ le_min (mul_nonneg measureReal_nonneg measureReal_nonneg)
        (mul_nonneg measureReal_nonneg measureReal_nonneg))

end Finite

end MonadFormal.Information
