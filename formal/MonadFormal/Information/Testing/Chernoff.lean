import MonadFormal.Information.Testing
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Finite-sample Chernoff bounds

Paper companion: `paper/MonadFormal/Information/Testing/Chernoff.tex`.
The product law represents genuinely independent repetitions. This module
proves an upper bound on optimal error, not the matching asymptotic lower
bound. Zero masses remain allowed; endpoint powers are avoided when support
is used to interpret the coefficient.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The joint law of `n` independent observations with the same input distribution. -/
noncomputable def iidLaw (P : ProbabilityMeasure X) (n : ℕ) :
    ProbabilityMeasure (Fin n → X) := ⟨Measure.pi (fun _ ↦ (P : Measure X)), inferInstance⟩

theorem iidLaw_singleton (P : ProbabilityMeasure X) (n : ℕ) (x : Fin n → X) :
    (iidLaw P n : Measure (Fin n → X)) {x} = ∏ i, (P : Measure X) {x i} := by
  exact Measure.pi_singleton _ x

theorem iidLaw_real_singleton (P : ProbabilityMeasure X) (n : ℕ) (x : Fin n → X) :
    (iidLaw P n : Measure (Fin n → X)).real {x} = ∏ i, (P : Measure X).real {x i} := by
  simp only [measureReal_def, iidLaw_singleton, ENNReal.toReal_prod]

variable [Fintype X]

/-- The Chernoff coefficient; its support-sensitive interpretation uses `0 < s < 1`. -/
noncomputable def chernoffCoeff (P Q : ProbabilityMeasure X) (s : ℝ) : ℝ≥0∞ :=
  ∑ x, (P : Measure X) {x} ^ s * (Q : Measure X) {x} ^ (1 - s)

/-- Chernoff information in nats; disjoint supports retain the value `⊤`. -/
noncomputable def chernoffInfo (P Q : ProbabilityMeasure X) : EReal :=
  -ENNReal.log (⨅ s : Ioo (0 : ℝ) 1, chernoffCoeff P Q s)

/-- The smaller mass is bounded by every weighted geometric mean. -/
theorem min_le_geometric (a b : ℝ≥0∞) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    min a b ≤ a ^ s * b ^ (1 - s) := by
  have ht : 0 ≤ 1 - s := sub_nonneg.mpr hs'
  have he (z : ℝ≥0∞) : z = z ^ s * z ^ (1 - s) := by
    rw [← ENNReal.rpow_add_of_nonneg s (1 - s) hs ht]
    simp
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact (he a).le.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hab ht))
  · rw [min_eq_right hba]
    exact (he b).le.trans (mul_le_mul' (ENNReal.rpow_le_rpow hba hs) le_rfl)

/-- Weighted arithmetic–geometric mean inequality for finite extended masses. -/
theorem geometric_le_arithmetic (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    a ^ s * b ^ (1 - s) ≤ ENNReal.ofReal s * a + ENNReal.ofReal (1 - s) * b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have ht : 0 ≤ 1 - s := sub_nonneg.mpr hs'
  have h := NNReal.geom_mean_le_arith_mean2_weighted
    ⟨s, hs⟩ ⟨1 - s, ht⟩ a b (NNReal.eq (by change s + (1 - s) = 1; ring))
  rw [ENNReal.ofReal_eq_coe_nnreal hs, ENNReal.ofReal_eq_coe_nnreal ht,
    ← ENNReal.coe_rpow_of_nonneg _ hs, ← ENNReal.coe_rpow_of_nonneg _ ht,
    ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add]
  exact ENNReal.coe_le_coe.mpr h

/-- Probability normalization bounds every coefficient in the closed exponent interval. -/
theorem chernoffCoeff_le_one [MeasurableSingletonClass X] (P Q : ProbabilityMeasure X)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) : chernoffCoeff P Q s ≤ 1 := by
  calc
    chernoffCoeff P Q s ≤ ∑ x, (ENNReal.ofReal s * (P : Measure X) {x} +
        ENNReal.ofReal (1 - s) * (Q : Measure X) {x}) := by
      exact Finset.sum_le_sum fun x _ ↦ geometric_le_arithmetic _ _
        (measure_ne_top _ _) (measure_ne_top _ _) hs hs'
    _ = ENNReal.ofReal s + ENNReal.ofReal (1 - s) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp
    _ = 1 := by rw [← ENNReal.ofReal_add hs (sub_nonneg.mpr hs')]; simp

/-- Identical hypotheses have unit coefficient, including zero-mass outcomes. -/
theorem chernoffCoeff_self [MeasurableSingletonClass X] (P : ProbabilityMeasure X)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) : chernoffCoeff P P s = 1 := by
  simp only [chernoffCoeff, ← ENNReal.rpow_add_of_nonneg s (1 - s) hs (sub_nonneg.mpr hs')]
  simp

theorem binaryError_le_chernoff [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    binaryError P Q π ≤ (π : Measure Bool) {false} ^ s *
      (π : Measure Bool) {true} ^ (1 - s) * chernoffCoeff P Q s := by
  rw [binaryError_eq_overlap, chernoffCoeff, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  refine (min_le_geometric _ _ hs hs').trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hs,
    ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hs')]
  ring

/-- Independence makes the one-sample coefficient multiply exactly. -/
theorem chernoffCoeff_iidLaw (P Q : ProbabilityMeasure X) (n : ℕ)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    chernoffCoeff (iidLaw P n) (iidLaw Q n) s = chernoffCoeff P Q s ^ n := by
  classical
  simp only [chernoffCoeff, iidLaw_singleton,
    ← ENNReal.prod_rpow_of_nonneg hs, ← ENNReal.prod_rpow_of_nonneg (sub_nonneg.mpr hs'),
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (x : X) ↦
    (P : Measure X) {x} ^ s * (Q : Measure X) {x} ^ (1 - s))]
  simp

/-- Finite-blocklength error bound, with the fixed prior factor retained. -/
theorem binaryError_iid_le [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (n : ℕ) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    binaryError (iidLaw P n) (iidLaw Q n) π ≤
      (π : Measure Bool) {false} ^ s * (π : Measure Bool) {true} ^ (1 - s) *
        chernoffCoeff P Q s ^ n := by
  simpa only [chernoffCoeff_iidLaw P Q n hs hs'] using
    binaryError_le_chernoff (iidLaw P n) (iidLaw Q n) π hs hs'

/-- In the open exponent interval, a zero coefficient means disjoint supports. -/
theorem chernoffCoeff_eq_zero_iff (P Q : ProbabilityMeasure X)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    chernoffCoeff P Q s = 0 ↔ ∀ x, (P : Measure X) {x} = 0 ∨ (Q : Measure X) {x} = 0 := by
  simp [chernoffCoeff, Finset.sum_eq_zero_iff, mul_eq_zero,
    ENNReal.rpow_eq_zero_iff_of_pos hs, ENNReal.rpow_eq_zero_iff_of_pos (sub_pos.mpr hs')]

/-- The ordinary overlap is a uniform lower bound, even as the exponent approaches an endpoint. -/
theorem overlap_le_chernoffCoeff (P Q : ProbabilityMeasure X)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    ∑ x, min ((P : Measure X) {x}) ((Q : Measure X) {x}) ≤ chernoffCoeff P Q s := by
  exact Finset.sum_le_sum fun _ _ ↦ min_le_geometric _ _ hs hs'

/-- A vanishing infimum cannot hide a common positive atom at a limiting exponent. -/
theorem iInf_chernoffCoeff_eq_zero_iff (P Q : ProbabilityMeasure X) :
    (⨅ s : Ioo (0 : ℝ) 1, chernoffCoeff P Q s) = 0 ↔
      ∀ x, (P : Measure X) {x} = 0 ∨ (Q : Measure X) {x} = 0 := by
  constructor
  · intro h
    have hmin : (∑ x, min ((P : Measure X) {x}) ((Q : Measure X) {x})) ≤ 0 := by
      rw [← h]
      exact le_iInf fun s ↦ overlap_le_chernoffCoeff P Q s.property.1.le s.property.2.le
    have he := le_antisymm hmin zero_le
    simpa only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const,
      min_eq_zero] using he
  · intro h
    apply le_antisymm _ zero_le
    refine (iInf_le _ (⟨1 / 2, by constructor <;> norm_num⟩ : Ioo (0 : ℝ) 1)).trans_eq ?_
    exact (chernoffCoeff_eq_zero_iff P Q (by norm_num) (by norm_num)).mpr h

theorem chernoffInfo_nonneg [MeasurableSingletonClass X] (P Q : ProbabilityMeasure X) :
    0 ≤ chernoffInfo P Q := by
  unfold chernoffInfo
  apply EReal.neg_nonneg.mpr
  apply ENNReal.log_le_zero_iff.mpr
  exact (iInf_le _ (⟨1 / 2, by constructor <;> norm_num⟩ : Ioo (0 : ℝ) 1)).trans
    (chernoffCoeff_le_one P Q (by norm_num) (by norm_num))

theorem chernoffInfo_self [MeasurableSingletonClass X] (P : ProbabilityMeasure X) :
    chernoffInfo P P = 0 := by
  have hi : (⨅ s : Ioo (0 : ℝ) 1, chernoffCoeff P P s) = 1 := by
    apply le_antisymm
    · exact (iInf_le _ (⟨1 / 2, by constructor <;> norm_num⟩ : Ioo (0 : ℝ) 1)).trans_eq
        (chernoffCoeff_self P (by norm_num) (by norm_num))
    · exact le_iInf fun s ↦ (chernoffCoeff_self P s.property.1.le s.property.2.le).ge
  simp [chernoffInfo, hi]

theorem chernoffInfo_eq_top_iff (P Q : ProbabilityMeasure X) :
    chernoffInfo P Q = ⊤ ↔ ∀ x, (P : Measure X) {x} = 0 ∨ (Q : Measure X) {x} = 0 := by
  rw [chernoffInfo, EReal.neg_eq_top_iff, ENNReal.log_eq_bot_iff,
    iInf_chernoffCoeff_eq_zero_iff]

/-- Disjoint hypotheses are separated with zero Bayes error after any positive number of samples. -/
theorem binaryError_iid_eq_zero_of_disjoint [MeasurableSingletonClass X]
    (P Q : ProbabilityMeasure X)
    (π : ProbabilityMeasure Bool) (h : ∀ x, (P : Measure X) {x} = 0 ∨ (Q : Measure X) {x} = 0)
    {n : ℕ} (hn : 0 < n) : binaryError (iidLaw P n) (iidLaw Q n) π = 0 := by
  apply le_antisymm _ zero_le
  have hc : chernoffCoeff P Q (1 / 2) = 0 := (chernoffCoeff_eq_zero_iff P Q (by norm_num)
    (by norm_num)).mpr h
  have hb := binaryError_iid_le P Q π n (s := 1 / 2) (by norm_num) (by norm_num)
  simpa only [hc, zero_pow (Nat.ne_of_gt hn), mul_zero] using hb

end MonadFormal.Information
