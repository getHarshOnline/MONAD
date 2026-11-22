import MonadFormal.Information.Testing.Chernoff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Order.Compact

/-!
# Common-support exponential tilting

Paper companion: `paper/MonadFormal/Information/Testing/Tilted.tex`.
The continuous partition uses only atoms positive under both hypotheses.
Its endpoint values are the masses of that common support, not necessarily
one. This retains unequal-support cases when minimizing the coefficient.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-- Atoms carrying positive probability under both hypotheses. -/
def commonSupport (P Q : ProbabilityMeasure X) : Set X :=
  {x | 0 < (P : Measure X).real {x} ∧ 0 < (Q : Measure X).real {x}}

/-- Log likelihood ratio; only its values on `commonSupport` enter the tilted law. -/
noncomputable def logLikelihood (P Q : ProbabilityMeasure X) (x : X) : ℝ :=
  Real.log ((P : Measure X).real {x}) - Real.log ((Q : Measure X).real {x})

/-- Unnormalized geometric mixture, with zero weight outside the common support. -/
noncomputable def supportWeight (P Q : ProbabilityMeasure X) (s : ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ commonSupport P Q then
    Real.exp (s * Real.log ((P : Measure X).real {x}) +
      (1 - s) * Real.log ((Q : Measure X).real {x})) else 0

theorem supportWeight_nonneg (P Q : ProbabilityMeasure X) (s : ℝ) (x : X) :
    0 ≤ supportWeight P Q s x := by
  unfold supportWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem supportWeight_pos (P Q : ProbabilityMeasure X) (s : ℝ) {x : X}
    (hx : x ∈ commonSupport P Q) : 0 < supportWeight P Q s x := by
  simp only [supportWeight, ite_eq_left hx]
  exact Real.exp_pos _

theorem hasDerivAt_supportWeight (P Q : ProbabilityMeasure X) (s : ℝ) (x : X) :
    HasDerivAt (fun t ↦ supportWeight P Q t x)
      (supportWeight P Q s x * logLikelihood P Q x) s := by
  classical
  by_cases hx : x ∈ commonSupport P Q
  · simp only [supportWeight, ite_eq_left hx, logLikelihood]
    have hd := (((hasDerivAt_id s).mul_const (Real.log ((P : Measure X).real {x}))).add
      (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const
        (Real.log ((Q : Measure X).real {x})))).exp
    simpa [Pi.add_apply, Pi.sub_apply, id_eq, mul_comm, sub_eq_add_neg] using hd
  · simp only [supportWeight, ite_eq_right hx, zero_mul]
    exact hasDerivAt_const s 0

variable [Fintype X]

/-- Continuous extension of the open-interval Chernoff coefficient to real exponents. -/
noncomputable def supportPartition (P Q : ProbabilityMeasure X) (s : ℝ) : ℝ :=
  ∑ x, supportWeight P Q s x

theorem supportPartition_pos (P Q : ProbabilityMeasure X)
    (h : (commonSupport P Q).Nonempty) (s : ℝ) : 0 < supportPartition P Q s := by
  obtain ⟨x, hx⟩ := h
  exact (supportWeight_pos P Q s hx).trans_le
    (Finset.single_le_sum (fun y _ ↦ supportWeight_nonneg P Q s y) (Finset.mem_univ x))

theorem hasDerivAt_supportPartition (P Q : ProbabilityMeasure X) (s : ℝ) :
    HasDerivAt (supportPartition P Q)
      (∑ x, supportWeight P Q s x * logLikelihood P Q x) s := by
  convert HasDerivAt.sum (u := Finset.univ)
    (fun x _ ↦ hasDerivAt_supportWeight P Q s x) using 1
  ext t
  simp [supportPartition]

theorem continuous_supportPartition (P Q : ProbabilityMeasure X) :
    Continuous (supportPartition P Q) :=
  continuous_iff_continuousAt.mpr fun s ↦ (hasDerivAt_supportPartition P Q s).continuousAt

omit [Fintype X] in
theorem ofReal_supportWeight (P Q : ProbabilityMeasure X) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) (x : X) :
    ENNReal.ofReal (supportWeight P Q s x) =
      (P : Measure X) {x} ^ s * (Q : Measure X) {x} ^ (1 - s) := by
  classical
  by_cases hx : x ∈ commonSupport P Q
  · have hp := hx.1
    have hq := hx.2
    rw [supportWeight, ite_eq_left hx, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [mul_comm s, mul_comm (1 - s), ← Real.rpow_def_of_pos hp,
      ← Real.rpow_def_of_pos hq, ← ENNReal.ofReal_rpow_of_pos hp,
      ← ENNReal.ofReal_rpow_of_pos hq]
    simp [Measure.real, ENNReal.ofReal_toReal, measure_ne_top]
  · have hz : (P : Measure X) {x} = 0 ∨ (Q : Measure X) {x} = 0 := by
      simpa only [commonSupport, mem_ofPred_eq, Measure.real,
        ENNReal.toReal_pos_iff, measure_lt_top, and_true, not_and_or,
        not_lt, nonpos_iff_eq_zero] using hx
    rcases hz with hp | hq
    · simp [supportWeight, hx, hp, ENNReal.zero_rpow_of_pos hs]
    · simp [supportWeight, hx, hq, ENNReal.zero_rpow_of_pos (sub_pos.mpr hs')]

theorem ofReal_supportPartition (P Q : ProbabilityMeasure X) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    ENNReal.ofReal (supportPartition P Q s) = chernoffCoeff P Q s := by
  rw [supportPartition, ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ supportWeight_nonneg P Q s x)]
  exact Finset.sum_congr rfl fun x _ ↦ ofReal_supportWeight P Q hs hs' x

theorem supportPartition_zero (P Q : ProbabilityMeasure X) :
    supportPartition P Q 0 = ∑ x, (commonSupport P Q).indicator
      (fun y ↦ (Q : Measure X).real {y}) x := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ commonSupport P Q
  · simp only [supportWeight, ite_eq_left hx, zero_mul, sub_zero, one_mul, zero_add,
      Real.exp_log hx.2, indicator_of_mem hx]
  · simp [supportWeight, hx]

theorem supportPartition_one (P Q : ProbabilityMeasure X) :
    supportPartition P Q 1 = ∑ x, (commonSupport P Q).indicator
      (fun y ↦ (P : Measure X).real {y}) x := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ commonSupport P Q
  · simp only [supportWeight, ite_eq_left hx, one_mul, sub_self, zero_mul, add_zero,
      Real.exp_log hx.1, indicator_of_mem hx]
  · simp [supportWeight, hx]

/-- Compactness supplies a minimizer; it need not be an interior point. -/
theorem exists_min_supportPartition (P Q : ProbabilityMeasure X) :
    ∃ s ∈ Icc (0 : ℝ) 1, IsMinOn (supportPartition P Q) (Icc 0 1) s := by
  exact isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one)
    (continuous_supportPartition P Q).continuousOn

/-- The attained closed-interval minimum equals the original open-interval infimum. -/
theorem iInf_chernoffCoeff_eq_of_isMinOn (P Q : ProbabilityMeasure X) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s) :
    (⨅ t : Ioo (0 : ℝ) 1, chernoffCoeff P Q t) =
      ENNReal.ofReal (supportPartition P Q s) := by
  apply le_antisymm
  · have hc : IsClosed {t : ℝ | (⨅ u : Ioo (0 : ℝ) 1, chernoffCoeff P Q u) ≤
        ENNReal.ofReal (supportPartition P Q t)} :=
      isClosed_le continuous_const
        (ENNReal.continuous_ofReal.comp (continuous_supportPartition P Q))
    have hi : Ioo (0 : ℝ) 1 ⊆ {t : ℝ | (⨅ u : Ioo (0 : ℝ) 1, chernoffCoeff P Q u) ≤
        ENNReal.ofReal (supportPartition P Q t)} := by
      intro t ht
      rw [mem_ofPred_eq, ofReal_supportPartition P Q ht.1 ht.2]
      exact iInf_le _ (⟨t, ht⟩ : Ioo (0 : ℝ) 1)
    apply closure_minimal hi hc
    simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hs
  · refine le_iInf fun t ↦ ?_
    rw [← ofReal_supportPartition P Q t.property.1 t.property.2]
    exact ENNReal.ofReal_le_ofReal (hmin ⟨t.property.1.le, t.property.2.le⟩)

/-- The first-order condition holds in every feasible direction, including at endpoints. -/
theorem supportPartition_firstOrder (P Q : ProbabilityMeasure X) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s) :
    0 ≤ (t - s) * ∑ x, supportWeight P Q s x * logLikelihood P Q x := by
  have h := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hasDerivAt_supportPartition P Q s).hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).segment_subset hs ht))
  simpa using h

/-- The normalized geometric mixture as an actual probability law on the original alphabet. -/
noncomputable def tiltedLaw (P Q : ProbabilityMeasure X)
    (h : (commonSupport P Q).Nonempty) (s : ℝ) : ProbabilityMeasure X := by
  let w : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (supportWeight P Q s x / supportPartition P Q s)
  have hw : ∑ x, w x = 1 := by
    dsimp [w]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦
      div_nonneg (supportWeight_nonneg P Q s x) (supportPartition_pos P Q h s).le)]
    rw [← Finset.sum_div, ← supportPartition, div_self (supportPartition_pos P Q h s).ne']
    simp
  exact (PMF.ofFintype w hw).toMeasure.toProbabilityMeasure

theorem tiltedLaw_singleton [MeasurableSingletonClass X] (P Q : ProbabilityMeasure X)
    (h : (commonSupport P Q).Nonempty) (s : ℝ) (x : X) :
    (tiltedLaw P Q h s : Measure X) {x} =
      ENNReal.ofReal (supportWeight P Q s x / supportPartition P Q s) := by
  exact PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x)

theorem tiltedLaw_real_singleton [MeasurableSingletonClass X] (P Q : ProbabilityMeasure X)
    (h : (commonSupport P Q).Nonempty) (s : ℝ) (x : X) :
    (tiltedLaw P Q h s : Measure X).real {x} =
      supportWeight P Q s x / supportPartition P Q s := by
  rw [measureReal_def, tiltedLaw_singleton, ENNReal.toReal_ofReal
    (div_nonneg (supportWeight_nonneg P Q s x) (supportPartition_pos P Q h s).le)]

theorem integral_tiltedLaw [MeasurableSingletonClass X] (P Q : ProbabilityMeasure X)
    (h : (commonSupport P Q).Nonempty) (s : ℝ) (f : X → ℝ) :
    (∫ x, f x ∂(tiltedLaw P Q h s : Measure X)) =
      (∑ x, supportWeight P Q s x * f x) / supportPartition P Q s := by
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, tiltedLaw_singleton, ENNReal.toReal_ofReal
    (div_nonneg (supportWeight_nonneg P Q s _) (supportPartition_pos P Q h s).le),
    smul_eq_mul, div_mul_eq_mul_div, Finset.sum_div]

/-- The logarithmic derivative is the mean log likelihood under the tilted probability law. -/
theorem hasDerivAt_log_supportPartition [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X) (h : (commonSupport P Q).Nonempty) (s : ℝ) :
    HasDerivAt (fun t ↦ Real.log (supportPartition P Q t))
      (∫ x, logLikelihood P Q x ∂(tiltedLaw P Q h s : Measure X)) s := by
  rw [integral_tiltedLaw]
  exact (hasDerivAt_supportPartition P Q s).log (supportPartition_pos P Q h s).ne'

/-- Normalized first-order condition, valid at boundary and interior minimizers alike. -/
theorem tilted_mean_firstOrder [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X) (h : (commonSupport P Q).Nonempty) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s) :
    0 ≤ (t - s) * ∫ x, logLikelihood P Q x ∂(tiltedLaw P Q h s : Measure X) := by
  rw [integral_tiltedLaw, ← mul_div_assoc]
  exact div_nonneg (supportPartition_firstOrder P Q hs ht hmin)
    (supportPartition_pos P Q h s).le

/-- The two endpoint directions encode all three possible optimizer locations. -/
theorem tilted_mean_endpoint_conditions [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X) (h : (commonSupport P Q).Nonempty) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s) :
    s * (∫ x, logLikelihood P Q x ∂(tiltedLaw P Q h s : Measure X)) ≤ 0 ∧
      0 ≤ (1 - s) * (∫ x, logLikelihood P Q x ∂(tiltedLaw P Q h s : Measure X)) := by
  constructor
  · simpa only [zero_sub, neg_mul, neg_nonneg] using
      tilted_mean_firstOrder P Q h hs (left_mem_Icc.mpr zero_le_one) hmin
  · exact tilted_mean_firstOrder P Q h hs (right_mem_Icc.mpr zero_le_one) hmin

omit [Fintype X] in
theorem supportWeight_mul_exp_left (P Q : ProbabilityMeasure X) (s : ℝ) {x : X}
    (hx : x ∈ commonSupport P Q) :
    supportWeight P Q s x * Real.exp ((1 - s) * logLikelihood P Q x) =
      (P : Measure X).real {x} := by
  rw [supportWeight, ite_eq_left hx, ← Real.exp_add]
  convert Real.exp_log hx.1 using 1
  congr 1
  unfold logLikelihood
  ring

omit [Fintype X] in
theorem supportWeight_mul_exp_right (P Q : ProbabilityMeasure X) (s : ℝ) {x : X}
    (hx : x ∈ commonSupport P Q) :
    supportWeight P Q s x * Real.exp (-s * logLikelihood P Q x) =
      (Q : Measure X).real {x} := by
  rw [supportWeight, ite_eq_left hx, ← Real.exp_add]
  convert Real.exp_log hx.2 using 1
  congr 1
  unfold logLikelihood
  ring

/-- The change-of-measure identity becomes a global inequality outside the common support. -/
theorem tiltedLaw_likelihood_left_le [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X) (h : (commonSupport P Q).Nonempty) (s : ℝ) (x : X) :
    (tiltedLaw P Q h s : Measure X).real {x} * supportPartition P Q s *
      Real.exp ((1 - s) * logLikelihood P Q x) ≤ (P : Measure X).real {x} := by
  rw [tiltedLaw_real_singleton, div_mul_cancel₀ _ (supportPartition_pos P Q h s).ne']
  by_cases hx : x ∈ commonSupport P Q
  · exact (supportWeight_mul_exp_left P Q s hx).le
  · simp only [supportWeight, ite_eq_right hx, zero_mul]
    exact measureReal_nonneg

theorem tiltedLaw_likelihood_right_le [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X) (h : (commonSupport P Q).Nonempty) (s : ℝ) (x : X) :
    (tiltedLaw P Q h s : Measure X).real {x} * supportPartition P Q s *
      Real.exp (-s * logLikelihood P Q x) ≤ (Q : Measure X).real {x} := by
  rw [tiltedLaw_real_singleton, div_mul_cancel₀ _ (supportPartition_pos P Q h s).ne']
  by_cases hx : x ∈ commonSupport P Q
  · exact (supportWeight_mul_exp_right P Q s hx).le
  · simp only [supportWeight, ite_eq_right hx, zero_mul]
    exact measureReal_nonneg

end MonadFormal.Information
