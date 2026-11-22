import MonadFormal.Temporal.Variational.Paths

/-!
# The shifted-difference adjoint

Paper companion: `paper/MonadFormal/Temporal/Variational/Shift.tex`.
Changing variables in the forward-shift term produces a backward difference
on [δ,1]. Indicators retain the two distinct boundary supports; no path
extension or periodic boundary condition is used.
-/

namespace MonadFormal.Temporal.Variational.Interval

open MeasureTheory Set Filter

/-- The nonlocal force: backward difference minus forward difference on their supports. -/
noncomputable def shiftForce (δ : ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Icc δ 1).indicator (fun s ↦ x s - x (s - δ)) t -
    (Icc 0 (1 - δ)).indicator (fun s ↦ x (s + δ) - x s) t

/-- A continuous real function is square-integrable on the unit interval. -/
theorem continuous_memLp_unit {g : ℝ → ℝ} (hg : Continuous g) : MemLp g 2 unitMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn g (Icc (0 : ℝ) 1) from hg.continuousOn)
  apply MemLp.of_bound hg.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
  exact hC t ht

theorem shiftForce_memLp (δ : ℝ) {x : ℝ → ℝ} (hx : Continuous x) :
    MemLp (shiftForce δ x) 2 unitMeasure := by
  exact ((continuous_memLp_unit (hx.sub (hx.comp (continuous_id.sub continuous_const)))).indicator
    measurableSet_Icc).sub
      ((continuous_memLp_unit ((hx.comp (continuous_id.add_const δ)).sub hx)).indicator
        measurableSet_Icc)

/-- Translation exposes the different integration intervals of the two terms. -/
theorem shifted_pairing (δ : ℝ) {x h : ℝ → ℝ} (hx : Continuous x) (hh : Continuous h) :
    (∫ t in 0..1 - δ, (x (t + δ) - x t) * (h (t + δ) - h t)) =
      (∫ t in δ..1, (x t - x (t - δ)) * h t) -
        ∫ t in 0..1 - δ, (x (t + δ) - x t) * h t := by
  have hg : Continuous (fun t ↦ x (t + δ) - x t) :=
    (hx.comp (continuous_id.add_const δ)).sub hx
  have h₁ : IntervalIntegrable (fun t ↦ (x (t + δ) - x t) * h (t + δ)) volume 0 (1 - δ) :=
    (hg.mul (hh.comp (continuous_id.add_const δ))).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun t ↦ (x (t + δ) - x t) * h t) volume 0 (1 - δ) :=
    (hg.mul hh).intervalIntegrable _ _
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub h₁ h₂]
  congr 1
  simpa only [add_sub_cancel_right, zero_add, sub_add_cancel] using
    (intervalIntegral.integral_comp_add_right
      (fun t ↦ (x t - x (t - δ)) * h t) (a := 0) (b := 1 - δ) δ)

theorem unit_integral_eq_interval (g : ℝ → ℝ) :
    (∫ t, g t ∂unitMeasure) = ∫ t in 0..1, g t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_Icc_eq_integral_Ioc

/-- Integrating an indicator inside [0,1] retains its exact subinterval. -/
theorem unit_integral_indicator {l r : ℝ} (hl : 0 ≤ l) (hr : r ≤ 1)
    (g : ℝ → ℝ) :
    (∫ t, (Icc l r).indicator g t ∂unitMeasure) = ∫ t in Icc l r, g t := by
  rw [integral_indicator measurableSet_Icc]
  simp only [unitMeasure, Measure.restrict_restrict measurableSet_Icc]
  rw [inter_eq_left.mpr (Icc_subset_Icc hl hr)]

/-- The shifted-difference pairing equals the force paired with the unshifted variation. -/
theorem shiftForce_pairing {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    {x h : ℝ → ℝ} (hx : Continuous x) (hh : Continuous h) :
    (∫ t, shiftForce δ x t * h t ∂unitMeasure) =
      ∫ t, (x (t + δ) - x t) * (h (t + δ) - h t) ∂shiftMeasure δ := by
  have hp : Continuous (fun t ↦ (x t - x (t - δ)) * h t) :=
    (hx.sub (hx.comp (continuous_id.sub continuous_const))).mul hh
  have hf : Continuous (fun t ↦ (x (t + δ) - x t) * h t) :=
    ((hx.comp (continuous_id.add_const δ)).sub hx).mul hh
  have he : (fun t ↦ shiftForce δ x t * h t) =
      (fun t ↦ (Icc δ 1).indicator (fun s ↦ (x s - x (s - δ)) * h s) t -
        (Icc 0 (1 - δ)).indicator (fun s ↦ (x (s + δ) - x s) * h s) t) := by
    funext t
    simp only [shiftForce, indicator_mul_left]
    exact sub_mul _ _ _
  rw [he]
  rw [integral_sub
    (((continuous_memLp_unit hp).indicator measurableSet_Icc).integrable (by norm_num))
    (((continuous_memLp_unit hf).indicator measurableSet_Icc).integrable (by norm_num)),
    unit_integral_indicator hδ.1 le_rfl,
    unit_integral_indicator le_rfl (by linarith [hδ.1])]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδ.2,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hδ.2] : (0 : ℝ) ≤ 1 - δ),
    ← shifted_pairing δ hx hh]
  rw [intervalIntegral.integral_of_le (by linarith [hδ.2] : (0 : ℝ) ≤ 1 - δ)]
  change (∫ t in Ioc 0 (1 - δ), (x (t + δ) - x t) * (h (t + δ) - h t)) =
    ∫ t in Icc 0 (1 - δ), (x (t + δ) - x t) * (h (t + δ) - h t)
  exact integral_Icc_eq_integral_Ioc.symm

end MonadFormal.Temporal.Variational.Interval
