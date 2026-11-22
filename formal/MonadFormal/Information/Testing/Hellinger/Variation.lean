import MonadFormal.Information.Testing.Hellinger

/-!
# Hellinger and total variation

Paper companion: `paper/MonadFormal/Information/Testing/Hellinger/Variation.tex`.
The density formula is proved for MONAD's existing measurable-test total
variation; it is not a new definition of that distance.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A zero-mean density difference spends half its absolute mass on either sign. -/
theorem abs_setIntegral_le_half_integral_abs {f : X → ℝ} (hf : Integrable f μ)
    (hz : (∫ x, f x ∂μ) = 0) {A : Set X} (hA : MeasurableSet A) :
    |∫ x in A, f x ∂μ| ≤ (∫ x, |f x| ∂μ) / 2 := by
  have hs := integral_add_compl hA hf
  have ha := integral_add_compl hA hf.abs
  have hc : (∫ x in Aᶜ, f x ∂μ) = -(∫ x in A, f x ∂μ) := by linarith
  have h₁ := abs_integral_le_integral_abs (μ := μ.restrict A) (f := f)
  have h₂ := abs_integral_le_integral_abs (μ := μ.restrict Aᶜ) (f := f)
  rw [hc, abs_neg] at h₂
  linarith

/-- Cauchy–Schwarz for absolute products of actual L² representatives. -/
theorem integral_abs_mul_le_L2_norm (f g : Lp ℝ 2 μ) :
    (∫ x, |f x * g x| ∂μ) ≤ ‖f‖ * ‖g‖ := by
  let u := (Lp.memLp f).norm.toLp (fun x ↦ ‖f x‖)
  let v := (Lp.memLp g).norm.toLp (fun x ↦ ‖g x‖)
  have hu : ‖u‖ = ‖f‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), Lp.norm_def]
  have hv : ‖v‖ = ‖g‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable g), Lp.norm_def]
  have hi : (∫ x, |f x * g x| ∂μ) = ⟪u, v⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp f).norm.coeFn_toLp, (Lp.memLp g).norm.coeFn_toLp] with x hx hy
    dsimp only [u, v]
    rw [hx, hy]
    simp [abs_mul, Real.norm_eq_abs, mul_comm]
  rw [hi]
  simpa only [hu, hv] using real_inner_le_norm u v

namespace RootDensity

theorem density_diff_integrable (p q : RootDensity μ) :
    Integrable (fun x ↦ p.root x ^ 2 - q.root x ^ 2) μ :=
  (Lp.memLp p.root).integrable_sq.sub (Lp.memLp q.root).integrable_sq

theorem density_diff_integral (p q : RootDensity μ) :
    (∫ x, p.root x ^ 2 - q.root x ^ 2 ∂μ) = 0 := by
  rw [integral_sub (Lp.memLp p.root).integrable_sq (Lp.memLp q.root).integrable_sq,
    p.integral_sq, q.integral_sq, sub_self]

/-- The usual density formula equals the already-defined operational total variation. -/
theorem tv_eq_density_integral (p q : RootDensity μ) :
    Approximation.tv p.law q.law =
      ENNReal.ofReal ((∫ x, |p.root x ^ 2 - q.root x ^ 2| ∂μ) / 2) := by
  rw [Approximation.tv_eq_eventTV]
  apply le_antisymm
  · refine iSup_le fun A ↦ ?_
    rw [p.law_real_apply A.property, q.law_real_apply A.property,
      ← integral_sub (Lp.memLp p.root).integrable_sq.restrict
        (Lp.memLp q.root).integrable_sq.restrict]
    exact ENNReal.ofReal_le_ofReal
      (abs_setIntegral_le_half_integral_abs (p.density_diff_integrable q)
        (p.density_diff_integral q) A.property)
  · let f : X → ℝ := fun x ↦ p.root x ^ 2 - q.root x ^ 2
    let A : Set X := {x | 0 ≤ f x}
    have hm : Measurable f :=
      (Lp.stronglyMeasurable p.root).measurable.pow_const 2 |>.sub
        ((Lp.stronglyMeasurable q.root).measurable.pow_const 2)
    have hA : MeasurableSet A := measurableSet_le measurable_const hm
    have hf : Integrable f μ := p.density_diff_integrable q
    have hz : (∫ x, f x ∂μ) = 0 := p.density_diff_integral q
    have hi : (∫ x in A, f x ∂μ) = (∫ x, |f x| ∂μ) / 2 := by
      have he := integral_abs_eq_two_mul_integral_posPart_sub_integral hf
      have hg : (∫ x, (f x)⁺ ∂μ) = ∫ x in A, f x ∂μ := by
        rw [← integral_indicator hA]
        apply integral_congr_ae
        exact ae_of_all _ fun x ↦ by
          by_cases hx : 0 ≤ f x
          · simp [A, hx, PosPart.posPart]
          · simp [A, hx, PosPart.posPart, max_eq_right (le_of_lt (lt_of_not_ge hx))]
      rw [hg, hz, sub_zero] at he
      linarith
    have he := le_iSup (fun s : {s : Set X // MeasurableSet s} ↦
      ENNReal.ofReal |(p.law : Measure X).real s.val - (q.law : Measure X).real s.val|) ⟨A, hA⟩
    rw [p.law_real_apply hA, q.law_real_apply hA,
      ← integral_sub (Lp.memLp p.root).integrable_sq.restrict
        (Lp.memLp q.root).integrable_sq.restrict] at he
    change ENNReal.ofReal |∫ x in A, f x ∂μ| ≤ _ at he
    rw [hi, abs_of_nonneg (div_nonneg (integral_nonneg fun x ↦ abs_nonneg (f x)) (by norm_num))] at he
    exact he

theorem tv_toReal_eq_density_integral (p q : RootDensity μ) :
    (Approximation.tv p.law q.law).toReal = (∫ x, |p.root x ^ 2 - q.root x ^ 2| ∂μ) / 2 := by
  rw [tv_eq_density_integral, ENNReal.toReal_ofReal
    (div_nonneg (integral_nonneg fun x ↦ abs_nonneg _) (by norm_num))]

/-- Squared Hellinger distance is a lower bound on normalized total variation. -/
theorem hellingerSq_le_tv (p q : RootDensity μ) :
    p.hellingerSq q ≤ (Approximation.tv p.law q.law).toReal := by
  rw [hellingerSq_eq_integral, tv_toReal_eq_density_integral]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hi : Integrable (fun x ↦ (p.root x - q.root x) ^ 2) μ :=
    ((Lp.memLp p.root).sub (Lp.memLp q.root)).integrable_sq
  apply integral_mono_ae hi (p.density_diff_integrable q).abs
  filter_upwards [p.nonneg, q.nonneg] with x hp hq
  rcases le_total (p.root x) (q.root x) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ hp h 2))]
    nlinarith [mul_nonneg hp (sub_nonneg.mpr h)]
  · rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hq h 2))]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr h)]

/-- The complementary Hellinger bound retains the sharp affinity factor. -/
theorem tv_sq_le_hellingerSq (p q : RootDensity μ) :
    (Approximation.tv p.law q.law).toReal ^ 2 ≤ p.hellingerSq q * (2 - p.hellingerSq q) := by
  have hi : (∫ x, |p.root x ^ 2 - q.root x ^ 2| ∂μ) =
      ∫ x, |(p.root - q.root) x * (p.root + q.root) x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub p.root q.root, Lp.coeFn_add p.root q.root] with x hx hy
    rw [hx, hy]
    congr 1
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hb : (Approximation.tv p.law q.law).toReal ≤ ‖p.root - q.root‖ * ‖p.root + q.root‖ / 2 := by
    rw [tv_toReal_eq_density_integral, hi]
    exact div_le_div_of_nonneg_right (integral_abs_mul_le_L2_norm _ _) (by norm_num)
  have he : (‖p.root - q.root‖ * ‖p.root + q.root‖ / 2) ^ 2 =
      p.hellingerSq q * (2 - p.hellingerSq q) := by
    rw [div_pow, mul_pow, norm_sub_sq_real, norm_add_sq_real,
      p.norm_eq_one, q.norm_eq_one, hellingerSq_eq_one_sub_affinity]
    dsimp only [affinity]
    ring
  exact (pow_le_pow_left₀ ENNReal.toReal_nonneg hb 2).trans_eq he

end RootDensity

end MonadFormal.Information
