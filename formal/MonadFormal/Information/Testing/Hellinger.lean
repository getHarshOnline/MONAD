import MonadFormal.Approximation.Events
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Square-root densities and Hellinger geometry

Paper companion: `paper/MonadFormal/Information/Testing/Hellinger.tex`.
Nonnegative unit vectors in real L² define actual probability densities.
The Hellinger normalization is one half of the squared L² distance.
The `Variation` and `Regularity` children add operational distance bounds
and local differentiability, without changing this probability-law owner.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A square-root density relative to a declared common dominating measure. -/
structure RootDensity (μ : Measure X) where
  root : Lp ℝ 2 μ
  nonneg : ∀ᵐ x ∂μ, 0 ≤ root x
  norm_eq_one : ‖root‖ = 1

/-- The L² norm is the integral of the squared representative. -/
theorem integral_sq_L2 (f : Lp ℝ 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  simp [pow_two]

namespace RootDensity

@[ext] theorem ext {p q : RootDensity μ} (h : p.root = q.root) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem integral_sq (p : RootDensity μ) : (∫ x, p.root x ^ 2 ∂μ) = 1 := by
  rw [integral_sq_L2, p.norm_eq_one, one_pow]

/-- Squaring and weighting the reference measure constructs the represented probability law. -/
noncomputable def law (p : RootDensity μ) : ProbabilityMeasure X :=
  ⟨μ.withDensity (fun x ↦ ENNReal.ofReal (p.root x ^ 2)), ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (Lp.memLp p.root).integrable_sq
        (ae_of_all _ fun x ↦ sq_nonneg (p.root x)), p.integral_sq, ENNReal.ofReal_one]⟩⟩

theorem law_real_apply (p : RootDensity μ) {A : Set X} (hA : MeasurableSet A) :
    (p.law : Measure X).real A = ∫ x in A, p.root x ^ 2 ∂μ := by
  change (μ.withDensity (fun x ↦ ENNReal.ofReal (p.root x ^ 2)) A).toReal = _
  rw [withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal (Lp.memLp p.root).integrable_sq.restrict
      (ae_of_all _ fun x ↦ sq_nonneg (p.root x)),
    ENNReal.toReal_ofReal (integral_nonneg fun x ↦ sq_nonneg (p.root x))]

/-- A law has only one nonnegative unit square root in the reference L² space. -/
theorem law_injective : Function.Injective (law (μ := μ)) := by
  intro p q he
  apply RootDensity.ext
  apply Lp.ext
  have hp : AEMeasurable (fun x ↦ ENNReal.ofReal (p.root x ^ 2)) μ :=
    ((Lp.aestronglyMeasurable p.root).aemeasurable.pow_const 2).ennreal_ofReal
  have hq : AEMeasurable (fun x ↦ ENNReal.ofReal (q.root x ^ 2)) μ :=
    ((Lp.aestronglyMeasurable q.root).aemeasurable.pow_const 2).ennreal_ofReal
  have hf : (∫⁻ x, ENNReal.ofReal (p.root x ^ 2) ∂μ) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (Lp.memLp p.root).integrable_sq
      (ae_of_all _ fun x ↦ sq_nonneg (p.root x))]
    exact ENNReal.ofReal_ne_top
  have hd := (withDensity_eq_iff hp hq hf).mp (congrArg Subtype.val he)
  filter_upwards [hd, p.nonneg, q.nonneg] with x hx hp₀ hq₀
  have hs : p.root x ^ 2 = q.root x ^ 2 := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using congrArg ENNReal.toReal hx
  exact (sq_eq_sq₀ hp₀ hq₀).mp hs

/-- The affinity of two laws represented over the same measure. -/
noncomputable def affinity (p q : RootDensity μ) : ℝ := ⟪p.root, q.root⟫_ℝ

/-- Squared Hellinger distance, with range `[0,1]`. -/
noncomputable def hellingerSq (p q : RootDensity μ) : ℝ := ‖p.root - q.root‖ ^ 2 / 2

theorem affinity_eq_integral (p q : RootDensity μ) :
    p.affinity q = ∫ x, p.root x * q.root x ∂μ := by
  simp [affinity, L2.inner_def, mul_comm]

theorem affinity_nonneg (p q : RootDensity μ) : 0 ≤ p.affinity q := by
  rw [affinity_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards [p.nonneg, q.nonneg] with x hp hq using mul_nonneg hp hq

theorem affinity_le_one (p q : RootDensity μ) : p.affinity q ≤ 1 := by
  simpa only [affinity, p.norm_eq_one, q.norm_eq_one, mul_one] using real_inner_le_norm p.root q.root

theorem hellingerSq_eq_one_sub_affinity (p q : RootDensity μ) :
    p.hellingerSq q = 1 - p.affinity q := by
  dsimp only [hellingerSq, affinity]
  rw [norm_sub_sq_real, p.norm_eq_one, q.norm_eq_one]
  ring

theorem hellingerSq_bounds (p q : RootDensity μ) :
    0 ≤ p.hellingerSq q ∧ p.hellingerSq q ≤ 1 := by
  rw [hellingerSq_eq_one_sub_affinity]
  constructor
  · exact sub_nonneg.mpr (p.affinity_le_one q)
  · linarith [p.affinity_nonneg q]

theorem hellingerSq_eq_integral (p q : RootDensity μ) :
    p.hellingerSq q = (∫ x, (p.root x - q.root x) ^ 2 ∂μ) / 2 := by
  dsimp only [hellingerSq]
  rw [← integral_sq_L2]
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub p.root q.root] with x hx
  rw [hx]
  rfl

/-- Zero Hellinger distance means equality of the represented probability laws. -/
theorem hellingerSq_eq_zero_iff (p q : RootDensity μ) :
    p.hellingerSq q = 0 ↔ p.law = q.law := by
  constructor
  · intro h
    have hr : p.root = q.root := by
      simpa only [hellingerSq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false,
        sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] using h
    exact congrArg law (RootDensity.ext hr)
  · intro h
    have he := law_injective h
    subst q
    simp [hellingerSq]

end RootDensity

end MonadFormal.Information
