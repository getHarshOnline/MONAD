import MonadFormal.Information.Testing.Conditional
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Moving-support alternatives

Paper companion: `paper/MonadFormal/Information/Testing/MovingSupport.tex`.
Lebesgue-uniform interval laws give an exact testing counterexample to a
universal inverse-square-root sample scale. The limit is derived from the
optimal risk over all randomized tests, not from a selected estimator.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

/-- The Lebesgue-uniform probability law on `(0, θ]`, for a positive endpoint. -/
noncomputable def intervalLaw (θ : ℝ) (hθ : 0 < θ) : ProbabilityMeasure ℝ :=
  ⟨cond volume (Ioc 0 θ), cond_isProbabilityMeasure_of_finite
    (by simp only [Real.volume_Ioc, sub_zero]; positivity) (by simp)⟩

/-- The smaller interval occupies its length ratio under the larger interval law. -/
theorem intervalLaw_mass {θ u : ℝ} (hu : 0 < u) (hθu : θ ≤ u) :
    (intervalLaw u hu : Measure ℝ) (Ioc 0 θ) = ENNReal.ofReal (θ / u) := by
  change cond volume (Ioc 0 u) (Ioc 0 θ) = _
  rw [cond_apply measurableSet_Ioc, inter_eq_right.mpr (Ioc_subset_Ioc le_rfl hθu),
    Real.volume_Ioc, Real.volume_Ioc, sub_zero, sub_zero,
    ENNReal.ofReal_div_of_pos hu, ENNReal.div_eq_inv_mul]

/-- Restricting the larger interval law gives a scalar multiple of the smaller law. -/
theorem intervalLaw_restrict {θ u : ℝ} (hθ : 0 < θ) (hu : 0 < u) (hθu : θ ≤ u) :
    (intervalLaw u hu : Measure ℝ).restrict (Ioc 0 θ) =
      (intervalLaw u hu : Measure ℝ) (Ioc 0 θ) • (intervalLaw θ hθ : Measure ℝ) := by
  rw [intervalLaw_mass hu hθu]
  change (cond volume (Ioc 0 u)).restrict (Ioc 0 θ) =
    ENNReal.ofReal (θ / u) • cond volume (Ioc 0 θ)
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset (Ioc_subset_Ioc le_rfl hθu)]
  simp only [Real.volume_Ioc, sub_zero, smul_smul, ENNReal.ofReal_div_of_pos hu,
    ENNReal.div_eq_inv_mul]
  rw [mul_assoc, ENNReal.mul_inv_cancel (by positivity : ENNReal.ofReal θ ≠ 0) ENNReal.ofReal_ne_top,
    mul_one]

/-- Exact error for any sample size and any binary prior, including zero prior masses. -/
theorem intervalLaw_binaryError {θ u : ℝ} (hθ : 0 < θ) (hu : 0 < u) (hθu : θ ≤ u)
    (π : ProbabilityMeasure Bool) (n : ℕ) :
    binaryError (iidLaw (intervalLaw θ hθ) n) (iidLaw (intervalLaw u hu) n) π =
      min ((π : Measure Bool) {false})
        ((π : Measure Bool) {true} * ENNReal.ofReal (θ / u) ^ n) := by
  rw [binaryError_iid_eq_min_of_restrict _ _ π measurableSet_Ioc
    (by rw [intervalLaw_mass hθ le_rfl, div_self hθ.ne', ENNReal.ofReal_one])
    (intervalLaw_restrict hθ hu hθu), intervalLaw_mass hu hθu]

theorem intervalLaw_binaryError_toReal {θ u : ℝ} (hθ : 0 < θ) (hu : 0 < u)
    (hθu : θ ≤ u) (π : ProbabilityMeasure Bool) (n : ℕ) :
    (binaryError (iidLaw (intervalLaw θ hθ) n) (iidLaw (intervalLaw u hu) n) π).toReal =
      min ((π : Measure Bool).real {false})
        ((π : Measure Bool).real {true} * (θ / u) ^ n) := by
  rw [intervalLaw_binaryError hθ hu hθu π n,
    ENNReal.toReal_min (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (div_nonneg hθ.le hu.le)]
  rfl

/-- Under balanced priors the smaller-support decision has the optimal error. -/
theorem intervalLaw_binaryError_equalPrior {θ u : ℝ} (hθ : 0 < θ) (hu : 0 < u)
    (hθu : θ ≤ u) (π : ProbabilityMeasure Bool)
    (hπ₀ : (π : Measure Bool).real {false} = 1 / 2)
    (hπ₁ : (π : Measure Bool).real {true} = 1 / 2) (n : ℕ) :
    (binaryError (iidLaw (intervalLaw θ hθ) n) (iidLaw (intervalLaw u hu) n) π).toReal =
      1 / 2 * (θ / u) ^ n := by
  rw [intervalLaw_binaryError_toReal hθ hu hθu, hπ₀, hπ₁]
  apply min_eq_right
  have hp : (θ / u) ^ n ≤ 1 :=
    pow_le_one₀ (div_nonneg hθ.le hu.le) ((div_le_one hu).mpr hθu)
  linarith

/-- At displacement `h / n`, the probability of remaining in the original support has a
nondegenerate exponential limit. This is a triangular array, not a fixed alternative. -/
theorem tendsto_interval_support_power {θ : ℝ} (hθ : 0 < θ) (h : ℝ) :
    Tendsto (fun n : ℕ ↦ (θ / (θ + h / n)) ^ n) atTop (𝓝 (Real.exp (-h / θ))) := by
  have hlim := (Real.tendsto_one_add_div_pow_exp (h / θ)).inv₀ (Real.exp_ne_zero _)
  have heq (n : ℕ) : θ / (θ + h / n) = (1 + (h / θ) / n)⁻¹ := by
    rw [inv_eq_one_div]
    field_simp
  simpa only [heq, inv_pow, Real.exp_neg, neg_div] using hlim

/-- A moving support produces a nontrivial optimal-error limit on the inverse-sample scale. -/
theorem tendsto_interval_binaryError {θ h : ℝ} (hθ : 0 < θ) (hh : 0 ≤ h)
    (π : ProbabilityMeasure Bool) :
    Tendsto (fun n : ℕ ↦
      (binaryError (iidLaw (intervalLaw θ hθ) n)
        (iidLaw (intervalLaw (θ + h / n)
          (add_pos_of_pos_of_nonneg hθ (div_nonneg hh (Nat.cast_nonneg n)))) n) π).toReal)
      atTop (𝓝 (min ((π : Measure Bool).real {false})
        ((π : Measure Bool).real {true} * Real.exp (-h / θ)))) := by
  simp_rw [intervalLaw_binaryError_toReal hθ _ (le_add_of_nonneg_right (div_nonneg hh
    (Nat.cast_nonneg _)))]
  exact tendsto_const_nhds.min (tendsto_const_nhds.mul (tendsto_interval_support_power hθ h))

theorem tendsto_interval_binaryError_equalPrior {θ h : ℝ} (hθ : 0 < θ) (hh : 0 ≤ h)
    (π : ProbabilityMeasure Bool) (hπ₀ : (π : Measure Bool).real {false} = 1 / 2)
    (hπ₁ : (π : Measure Bool).real {true} = 1 / 2) :
    Tendsto (fun n : ℕ ↦
      (binaryError (iidLaw (intervalLaw θ hθ) n)
        (iidLaw (intervalLaw (θ + h / n)
          (add_pos_of_pos_of_nonneg hθ (div_nonneg hh (Nat.cast_nonneg n)))) n) π).toReal)
      atTop (𝓝 (1 / 2 * Real.exp (-h / θ))) := by
  simp_rw [intervalLaw_binaryError_equalPrior hθ _ (le_add_of_nonneg_right (div_nonneg hh
    (Nat.cast_nonneg _))) π hπ₀ hπ₁]
  exact tendsto_const_nhds.mul (tendsto_interval_support_power hθ h)

/-- Balanced-prior local error lies strictly between zero and random guessing for `h > 0`. -/
theorem interval_local_error_nontrivial {θ h : ℝ} (hθ : 0 < θ) (hh : 0 < h) :
    0 < 1 / 2 * Real.exp (-h / θ) ∧ 1 / 2 * Real.exp (-h / θ) < 1 / 2 := by
  constructor
  · positivity
  · have he : Real.exp (-h / θ) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hh) hθ)
    linarith

end MonadFormal.Information
