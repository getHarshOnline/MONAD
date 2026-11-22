import MonadFormal.Temporal.Variational.Regularity

/-!
# The nonlocal Euler equation

Paper companion: `paper/MonadFormal/Temporal/Variational/Euler.tex`.
The minimizing path has an absolutely continuous velocity, and its second
derivative equals `weight * shiftForce δ x` almost everywhere. The two
indicator supports are retained at the boundary; no pointwise equation is
asserted at their jump locations.
-/

namespace MonadFormal.Temporal.Variational.Interval

open MeasureTheory Set Filter InnerProductSpace

theorem path_continuous (a b : ℝ) (f : variationSpace) : Continuous (path a b f) :=
  (continuous_const.add (continuous_const.mul continuous_id)).add (primitive_continuous f)

/-- The operator-form weak term is the actual nonlocal force paired with the variation. -/
theorem shift_inner_eq_force {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (a b : ℝ) (f h : variationSpace) :
    inner ℝ (shiftCLM δ f + affineOffset δ a b) (shiftCLM δ h) =
      ∫ t, shiftForce δ (path a b f) t * primitive h t ∂unitMeasure := by
  rw [shiftForce_pairing hδ (path_continuous a b f) (primitive_continuous h), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [shifted_path_ae δ a b f, shiftCLM_apply_ae δ h] with t hf hh
  rw [hf, hh]
  simp [mul_comm]

/-- The unique minimizing coordinate yields a path with an absolutely continuous velocity
and the strong Euler equation almost everywhere. -/
theorem exists_minimizer_euler {δ weight : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (hw : 0 ≤ weight) (a b : ℝ) :
    ∃ f : variationSpace,
      (∀ h : variationSpace, intervalEnergy δ weight a b f ≤ intervalEnergy δ weight a b h) ∧
      ∃ v : ℝ → ℝ, Continuous v ∧ AbsolutelyContinuousOnInterval v 0 1 ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (path a b f) (v t) t) ∧
        (∀ᵐ t ∂unitMeasure, HasDerivAt v (weight * shiftForce δ (path a b f) t) t) ∧
        (∀ᵐ t ∂unitMeasure,
          deriv (deriv (path a b f)) t = weight * shiftForce δ (path a b f) t) ∧
        MemLp (deriv (deriv (path a b f))) 2 unitMeasure := by
  obtain ⟨f, hf, hstationary⟩ := exists_interval_stationary_minimizer δ a b hw
  have hg := shiftForce_memLp δ (path_continuous a b f)
  let g : Velocity := hg.toLp (shiftForce δ (path a b f))
  have he : g =ᵐ[unitMeasure] shiftForce δ (path a b f) := hg.coeFn_toLp
  have hweak : ∀ h : variationSpace, inner ℝ f h +
      weight * (∫ t, g t * primitive h t ∂unitMeasure) = 0 := by
    intro h
    have hi : (∫ t, g t * primitive h t ∂unitMeasure) =
        ∫ t, shiftForce δ (path a b f) t * primitive h t ∂unitMeasure := by
      apply integral_congr_ae
      exact he.mono (fun _ ht ↦ congrArg (fun z : ℝ ↦ z * _) ht)
    rw [hi, ← shift_inner_eq_force hδ a b f h]
    exact hstationary h
  obtain ⟨v, hv, hac, hd, ha⟩ := weak_path_regularity a b f g weight hweak
  have hforce : ∀ᵐ t ∂unitMeasure,
      HasDerivAt v (weight * shiftForce δ (path a b f) t) t := by
    filter_upwards [ha, he] with t ht heq
    simpa only [heq] using ht
  have hsecond : deriv (deriv (path a b f)) =ᵐ[unitMeasure]
      (fun t ↦ weight * shiftForce δ (path a b f) t) :=
    (second_derivative_ae hd hforce).mono (fun _ ht ↦ ht.deriv)
  exact ⟨f, hf, v, hv, hac, hd, hforce, hsecond, (hg.const_mul weight).ae_eq hsecond.symm⟩

/-- Where both shifted neighbours belong to the interval, both force terms are present. -/
theorem shiftForce_both {δ t : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (ht : δ ≤ t) (htδ : t ≤ 1 - δ) (x : ℝ → ℝ) :
    shiftForce δ x t = 2 * x t - x (t - δ) - x (t + δ) := by
  have hp : t ∈ Icc δ (1 : ℝ) := ⟨ht, by linarith [hδ.1]⟩
  have hf : t ∈ Icc (0 : ℝ) (1 - δ) := ⟨by linarith [hδ.1], htδ⟩
  simp only [shiftForce, indicator_of_mem hp, indicator_of_mem hf]
  ring

end MonadFormal.Temporal.Variational.Interval
