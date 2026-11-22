import MonadFormal.Temporal.Variational.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Recovering velocity regularity from the weak equation

Paper companion: `paper/MonadFormal/Temporal/Variational/Regularity.tex`.
The orthogonal complement of the mean-zero velocities consists of constants.
Integration by parts therefore turns a weak equation with an L² force into
an absolutely continuous representative of the velocity.
-/

namespace MonadFormal.Temporal.Variational.Interval

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

theorem endpoint_const (c : ℝ) : endpoint (Lp.const 2 unitMeasure c) = c := by
  change primitive (Lp.const 2 unitMeasure c) 1 = c
  rw [primitive_one_eq_integral]
  calc
    _ = ∫ _ : ℝ, c ∂unitMeasure := integral_congr_ae (Lp.coeFn_const 2 unitMeasure c)
    _ = c := by simp

theorem const_inner_variation (c : ℝ) (h : variationSpace) :
    inner ℝ (Lp.const 2 unitMeasure c) h.val = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ t, c * h.val t ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 unitMeasure c] with t ht
      simp [mul_comm]
    _ = 0 := by rw [integral_const_mul, variation_integral_zero, mul_zero]

/-- A velocity orthogonal to every endpoint-preserving variation is constant almost everywhere. -/
theorem eq_const_of_orthogonal (g : Velocity)
    (hg : ∀ h : variationSpace, inner ℝ g h.val = 0) :
    g = Lp.const 2 unitMeasure (endpoint g) := by
  let h : variationSpace := ⟨g - Lp.const 2 unitMeasure (endpoint g), by
    change endpoint (g - Lp.const 2 unitMeasure (endpoint g)) = 0
    rw [map_sub, endpoint_const, sub_self]⟩
  have hz : inner ℝ h.val h.val = 0 := by
    change inner ℝ (g - Lp.const 2 unitMeasure (endpoint g)) h.val = 0
    rw [inner_sub_left, hg h, const_inner_variation, sub_self]
  have he : h.val = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hz
  exact sub_eq_zero.mp he

/-- The continuous primitive viewed as an L² velocity, without imposing an endpoint condition. -/
noncomputable def primitiveLp (g : Velocity) : Velocity :=
  BoundedContinuousFunction.toLp 2 unitMeasure ℝ (boundedPrimitive g)

theorem primitiveLp_ae (g : Velocity) : primitiveLp g =ᵐ[unitMeasure] primitive g :=
  BoundedContinuousFunction.coeFn_toLp 2 unitMeasure ℝ _

/-- Integration by parts has no boundary term for an endpoint-preserving variation. -/
theorem primitive_pairing (g : Velocity) (h : variationSpace) :
    inner ℝ (primitiveLp g) h.val = -(∫ t, g t * primitive h t ∂unitMeasure) := by
  have hibp := (primitive_absolutelyContinuous g).integral_mul_deriv_eq_deriv_mul
    (primitive_absolutelyContinuous h)
  have hz : primitive h 1 = 0 := variation_terminal h
  have hzero : primitive g 0 = 0 := by simp [primitive]
  rw [hz, hzero, mul_zero, zero_mul, sub_self, zero_sub] at hibp
  have hleft : inner ℝ (primitiveLp g) h.val =
      ∫ t in 0..1, primitive g t * deriv (primitive h) t := by
    rw [L2.inner_def, ← unit_integral_eq_interval]
    apply integral_congr_ae
    filter_upwards [primitiveLp_ae g, primitive_hasDerivAt_ae h] with t hg hh
    simp [hg, hh.deriv, mul_comm]
  have hright : (∫ t in 0..1, deriv (primitive g) t * primitive h t) =
      ∫ t, g t * primitive h t ∂unitMeasure := by
    rw [← unit_integral_eq_interval]
    apply integral_congr_ae
    filter_upwards [primitive_hasDerivAt_ae g] with t ht
    rw [ht.deriv]
  rw [hleft, ← hright]
  exact hibp

/-- The weak equation determines the velocity as a constant plus an integrated force. -/
theorem weak_velocity_representation (f : variationSpace) (g : Velocity) (weight : ℝ)
    (hweak : ∀ h : variationSpace, inner ℝ f h +
      weight * (∫ t, g t * primitive h t ∂unitMeasure) = 0) :
    ∃ c : ℝ, f.val =ᵐ[unitMeasure] (fun t ↦ c + weight * primitive g t) := by
  let k : Velocity := f.val - weight • primitiveLp g
  have hk : k = Lp.const 2 unitMeasure (endpoint k) := eq_const_of_orthogonal k (by
    intro h
    change inner ℝ (f.val - weight • primitiveLp g) h.val = 0
    rw [inner_sub_left, real_inner_smul_left, primitive_pairing]
    have hw := hweak h
    change inner ℝ f.val h.val + weight * _ = 0 at hw
    linarith)
  refine ⟨endpoint k, ?_⟩
  have he : k =ᵐ[unitMeasure] (fun _ ↦ endpoint k) := by
    nth_rw 1 [hk]
    exact Lp.coeFn_const 2 unitMeasure (endpoint k)
  filter_upwards [he, Lp.coeFn_sub f.val (weight • primitiveLp g),
    Lp.coeFn_smul weight (primitiveLp g), primitiveLp_ae g] with t ht hs hm hp
  change k t = endpoint k at ht
  change k t = f.val t - (weight • primitiveLp g) t at hs
  simp only [Pi.smul_apply, smul_eq_mul] at hm
  rw [hm, hp] at hs
  linarith

/-- A continuous representative upgrades the primitive's derivative from almost everywhere
to every interior point. Endpoints need not admit two-sided derivatives. -/
theorem primitive_hasDerivAt_of_continuous (f : Velocity) {g : ℝ → ℝ}
    (hg : Continuous g) (hfg : f =ᵐ[unitMeasure] g)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt (primitive f) (g t) t := by
  apply (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  calc
    primitive f s = ∫ r in 0..s, g r ∂unitMeasure :=
      intervalIntegral.integral_congr_ae (hfg.mono (fun _ h _ ↦ h))
    _ = ∫ r in 0..s, g r := unit_integral_eq _ ⟨hs.1.le, hs.2.le⟩

/-- A weak solution has an absolutely continuous velocity; its acceleration equals the force
almost everywhere. This derives regularity rather than assuming a second derivative. -/
theorem weak_path_regularity (a b : ℝ) (f : variationSpace) (g : Velocity) (weight : ℝ)
    (hweak : ∀ h : variationSpace, inner ℝ f h +
      weight * (∫ t, g t * primitive h t ∂unitMeasure) = 0) :
    ∃ v : ℝ → ℝ, Continuous v ∧ AbsolutelyContinuousOnInterval v 0 1 ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (path a b f) (v t) t) ∧
      ∀ᵐ t ∂unitMeasure, HasDerivAt v (weight * g t) t := by
  obtain ⟨c, hc⟩ := weak_velocity_representation f g weight hweak
  let v : ℝ → ℝ := fun t ↦ (b - a) + (c + weight * primitive g t)
  have hv : Continuous v := continuous_const.add
    (continuous_const.add (continuous_const.mul (primitive_continuous g)))
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ (b - a) + c) 0 1 :=
      (show ContDiff ℝ 1 (fun _ : ℝ ↦ (b - a) + c) from
        contDiff_const).contDiffOn.absolutelyContinuousOnInterval
    convert hconst.add
      (AbsolutelyContinuousOnInterval.const_mul weight (primitive_absolutelyContinuous g)) using 1
    funext t
    exact (add_assoc _ _ _).symm
  · intro t ht
    have hd := primitive_hasDerivAt_of_continuous f.val
      (continuous_const.add (continuous_const.mul (primitive_continuous g))) hc ht
    simpa only [path, v, Pi.add_apply, id_eq, mul_one] using!
      (((hasDerivAt_id t).const_mul (b - a)).const_add a).add hd
  · filter_upwards [primitive_hasDerivAt_ae g] with t ht
    simpa only [v] using! ((ht.const_mul weight).const_add c).const_add (b - a)

/-- An interior derivative represented by `v` inherits its almost-everywhere derivative. -/
theorem second_derivative_ae {x v acceleration : ℝ → ℝ}
    (hx : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ᵐ t ∂unitMeasure, HasDerivAt v (acceleration t) t) :
    ∀ᵐ t ∂unitMeasure, HasDerivAt (deriv x) (acceleration t) t := by
  filter_upwards [ae_mem_interior, hv] with t ht hv
  apply hv.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact (hx s hs).deriv

end MonadFormal.Temporal.Variational.Interval
