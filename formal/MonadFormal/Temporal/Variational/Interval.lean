import MonadFormal.Temporal.Variational
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Interval paths represented by square-integrable velocities

Paper companion: `paper/MonadFormal/Temporal/Variational/Interval.tex`.
`Velocity` is L² on [0,1]. Integration gives the zero-initial-value primitive
`P f`; `variationSpace` is the closed subspace with `P f 1 = 0`.
The path is `x(t) = a + (b - a)t + P f(t)`, and `shiftCLM δ` represents
`P f(t + δ) - P f(t)`. This connects the Hilbert-space minimizer theorem to
the integral energy in `intervalEnergy_eq_integrals`.

Restricting the integration measure makes `P f` bounded on the whole line.
Extension by zero is only an integration device, not a physical boundary law.
-/

namespace MonadFormal.Temporal.Variational.Interval

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace BoundedContinuousFunction

/-- Lebesgue measure on the unit interval, of total mass one. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure, Real.volume_Icc]

instance : NullSingletonClass unitMeasure := by
  unfold unitMeasure
  infer_instance

/-- Velocities are equivalence classes modulo equality almost everywhere. -/
noncomputable abbrev Velocity := Lp ℝ 2 unitMeasure

theorem velocity_integrable (f : Velocity) : Integrable f unitMeasure :=
  (Lp.memLp f).integrable (by norm_num)

/-- Integration recovers the continuous path with initial value zero. -/
noncomputable def primitive (f : Velocity) (t : ℝ) : ℝ :=
  ∫ s in 0..t, f s ∂unitMeasure

theorem primitive_continuous (f : Velocity) : Continuous (primitive f) :=
  (velocity_integrable f).continuous_primitive 0

theorem primitive_bound (f : Velocity) (t : ℝ) : ‖primitive f t‖ ≤ ‖f‖ := by
  let χ : Velocity := indicatorConstLp 2 measurableSet_uIoc
    (measure_ne_top unitMeasure (uIoc 0 t)) 1
  have hχ : ‖χ‖ ≤ 1 := by
    dsimp [χ]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul]
    exact Real.rpow_le_one (measureReal_nonneg) measureReal_le_one (by positivity)
  calc
    ‖primitive f t‖ = ‖∫ s in uIoc 0 t, f s ∂unitMeasure‖ :=
      intervalIntegral.norm_integral_eq_norm_integral_uIoc _
    _ = ‖inner ℝ χ f‖ := by rw [L2.inner_indicatorConstLp_one]
    _ ≤ ‖χ‖ * ‖f‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖ := by nlinarith [norm_nonneg f]

/-- The primitive is bounded on the whole line because the measure is restricted. -/
noncomputable def boundedPrimitive (f : Velocity) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (primitive f)
    (primitive_continuous f) ‖f‖ (primitive_bound f)

theorem primitive_add (f g : Velocity) (t : ℝ) :
    primitive (f + g) t = primitive f t + primitive g t := by
  unfold primitive
  calc
    _ = ∫ s in 0..t, (f s + g s) ∂unitMeasure :=
      intervalIntegral.integral_congr_ae ((Lp.coeFn_add f g).mono (fun _ h _ ↦ h))
    _ = _ := intervalIntegral.integral_add
      (velocity_integrable f).intervalIntegrable (velocity_integrable g).intervalIntegrable

theorem primitive_smul (c : ℝ) (f : Velocity) (t : ℝ) :
    primitive (c • f) t = c • primitive f t := by
  unfold primitive
  calc
    _ = ∫ s in 0..t, c • f s ∂unitMeasure :=
      intervalIntegral.integral_congr_ae ((Lp.coeFn_smul c f).mono (fun _ h _ ↦ h))
    _ = _ := intervalIntegral.integral_smul c _

/-- A bounded linear primitive operator, with bound one. -/
noncomputable def primitiveCLM : Velocity →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := boundedPrimitive
      map_add' := fun f g ↦ BoundedContinuousFunction.ext (primitive_add f g)
      map_smul' := fun c f ↦ BoundedContinuousFunction.ext (primitive_smul c f) }
    1 (fun f ↦ by
      change ‖boundedPrimitive f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
        (primitive_continuous f) (norm_nonneg f) (primitive_bound f))

theorem primitiveCLM_apply (f : Velocity) (t : ℝ) :
    primitiveCLM f t = primitive f t := rfl

/-- Endpoint displacement is a continuous linear functional of the velocity. -/
noncomputable def endpoint : Velocity →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ 1).comp primitiveCLM

/-- Variations preserve both endpoints. -/
noncomputable def variationSpace : Submodule ℝ Velocity := endpoint.ker

instance : CompleteSpace variationSpace :=
  endpoint.isClosed_ker.completeSpace_coe

theorem variation_initial (f : variationSpace) : primitiveCLM f 0 = 0 := by
  simp [primitiveCLM_apply, primitive]

theorem variation_terminal (f : variationSpace) : primitiveCLM f 1 = 0 :=
  f.property

/-- The output measure is restricted to points with an admitted forward shift. -/
noncomputable def shiftMeasure (δ : ℝ) : Measure ℝ :=
  volume.restrict (Icc 0 (1 - δ))

instance (δ : ℝ) : IsFiniteMeasure (shiftMeasure δ) := by
  unfold shiftMeasure
  infer_instance

/-- Shifted difference, before inclusion into the output Hilbert space. -/
noncomputable def differenceCLM (δ : ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun t ↦ t + δ, continuous_id.add_const δ⟩ - ContinuousLinearMap.id ℝ _

/-- Shifted difference on endpoint-preserving velocities, valued in L²([0,1-δ]). -/
noncomputable def shiftCLM (δ : ℝ) : variationSpace →L[ℝ] Lp ℝ 2 (shiftMeasure δ) :=
  (BoundedContinuousFunction.toLp 2 (shiftMeasure δ) ℝ).comp
    ((differenceCLM δ).comp (primitiveCLM.comp variationSpace.subtypeL))

theorem shiftCLM_apply_ae (δ : ℝ) (f : variationSpace) :
    shiftCLM δ f =ᵐ[shiftMeasure δ]
      (fun t ↦ primitive f (t + δ) - primitive f t) :=
  BoundedContinuousFunction.coeFn_toLp 2 (shiftMeasure δ) ℝ _

/-- The affine path contributes a constant shifted difference. -/
noncomputable def affineOffset (δ a b : ℝ) : Lp ℝ 2 (shiftMeasure δ) :=
  Lp.const 2 (shiftMeasure δ) ((b - a) * δ)

/-- Energy in endpoint-constrained velocity coordinates. -/
noncomputable def intervalEnergy (δ weight a b : ℝ) (f : variationSpace) : ℝ :=
  (b - a) ^ 2 / 2 + energy (shiftCLM δ) weight (affineOffset δ a b) f

/-- The endpoint-constrained integral energy has one minimizing velocity class. -/
theorem exists_unique_interval_minimizer (δ a b : ℝ) {weight : ℝ} (hw : 0 ≤ weight) :
    ∃! f : variationSpace, ∀ g : variationSpace,
      intervalEnergy δ weight a b f ≤ intervalEnergy δ weight a b g := by
  obtain ⟨f, hf, huniq⟩ := exists_unique_minimizer (shiftCLM δ) hw (affineOffset δ a b)
  refine ⟨f, fun g ↦ ?_, fun g hg ↦ huniq g ?_⟩
  · simpa only [intervalEnergy, add_le_add_iff_left] using hf g
  · intro h
    exact (add_le_add_iff_left _).mp (hg h)

/-- A minimizing velocity satisfies the weak Euler equation for every variation. -/
theorem exists_interval_stationary_minimizer (δ a b : ℝ) {weight : ℝ}
    (hw : 0 ≤ weight) :
    ∃ f : variationSpace,
      (∀ g : variationSpace, intervalEnergy δ weight a b f ≤ intervalEnergy δ weight a b g) ∧
      ∀ h : variationSpace, inner ℝ f h +
        weight * inner ℝ (shiftCLM δ f + affineOffset δ a b) (shiftCLM δ h) = 0 := by
  obtain ⟨f, hf⟩ := exists_stationary (shiftCLM δ) hw (affineOffset δ a b)
  refine ⟨f, fun g ↦ ?_, hf⟩
  simpa only [intervalEnergy, add_le_add_iff_left] using
    minimizes_of_stationary (shiftCLM δ) hw (affineOffset δ a b) f hf g

/-- Extension by zero converts restricted-measure integration to ordinary integration. -/
noncomputable def extendedVelocity (f : Velocity) : ℝ → ℝ :=
  (Icc 0 1).indicator f

theorem extendedVelocity_integrable (f : Velocity) : Integrable (extendedVelocity f) :=
  IntegrableOn.integrable_indicator (velocity_integrable f) measurableSet_Icc

theorem primitive_eq_integral (f : Velocity) (t : ℝ) :
    primitive f t = ∫ s in 0..t, extendedVelocity f s := by
  simp only [primitive, extendedVelocity, intervalIntegral,
    integral_indicator measurableSet_Icc, unitMeasure,
    Measure.restrict_restrict measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Ioc, inter_comm]

/-- Square-integrable velocities integrate to absolutely continuous paths. -/
theorem primitive_absolutelyContinuous (f : Velocity) :
    AbsolutelyContinuousOnInterval (primitive f) 0 1 := by
  simp_rw [show primitive f = (fun t ↦ ∫ s in 0..t, extendedVelocity f s) from
    funext (primitive_eq_integral f)]
  exact IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (extendedVelocity_integrable f).intervalIntegrable (by simp)

/-- The primitive recovers its velocity almost everywhere on the unit interval. -/
theorem primitive_hasDerivAt_ae (f : Velocity) :
    ∀ᵐ t ∂unitMeasure, HasDerivAt (primitive f) (f t) t := by
  have hd := LocallyIntegrable.ae_hasDerivAt_integral
    (extendedVelocity_integrable f).locallyIntegrable
  have hm : ∀ᵐ t ∂unitMeasure, t ∈ Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [ae_restrict_of_ae hd, hm] with t ht htm
  rw [funext (primitive_eq_integral f)]
  simpa only [extendedVelocity, indicator_of_mem htm] using ht 0

/-- The affine endpoint path plus an endpoint-preserving variation. -/
noncomputable def path (a b : ℝ) (f : variationSpace) (t : ℝ) : ℝ :=
  a + (b - a) * t + primitive f t

theorem path_endpoints (a b : ℝ) (f : variationSpace) :
    path a b f 0 = a ∧ path a b f 1 = b := by
  have hf := variation_terminal f
  change primitive f 1 = 0 at hf
  constructor
  · simp [path, primitive]
  · simp [path, hf]

theorem path_hasDerivAt_ae (a b : ℝ) (f : variationSpace) :
    ∀ᵐ t ∂unitMeasure, HasDerivAt (path a b f) ((b - a) + f.val t) t := by
  filter_upwards [primitive_hasDerivAt_ae f] with t ht
  simpa only [path, Pi.add_apply, id_eq, mul_one] using!
    (((hasDerivAt_id t).const_mul (b - a)).const_add a).add ht

theorem path_absolutelyContinuous (a b : ℝ) (f : variationSpace) :
    AbsolutelyContinuousOnInterval (path a b f) 0 1 := by
  have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ a + (b - a) * t) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  exact hlin.contDiffOn.absolutelyContinuousOnInterval.add (primitive_absolutelyContinuous f)

theorem primitive_one_eq_integral (f : Velocity) :
    primitive f 1 = ∫ t, f t ∂unitMeasure := by
  rw [primitive, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [unitMeasure, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Icc_self]
  exact integral_Icc_eq_integral_Ioc.symm

theorem variation_integral_zero (f : variationSpace) : ∫ t, f.val t ∂unitMeasure = 0 := by
  rw [← primitive_one_eq_integral]
  exact variation_terminal f

theorem integral_sq_eq_norm_sq {μ : Measure ℝ} (f : Lp ℝ 2 μ) :
    (∫ t, (f t) ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext t
  simp [Real.norm_eq_abs, sq_abs]

/-- The mean-zero variation removes the kinetic cross term. -/
theorem kinetic_integral (a b : ℝ) (f : variationSpace) :
    (∫ t, ((b - a) + f.val t) ^ 2 ∂unitMeasure) = (b - a) ^ 2 + ‖f‖ ^ 2 := by
  have hc : Integrable (fun _ : ℝ ↦ (b - a) ^ 2) unitMeasure := integrable_const _
  have hl := (velocity_integrable f).const_mul (2 * (b - a))
  have hs := (Lp.memLp f.val).integrable_sq
  calc
    _ = ∫ t, ((b - a) ^ 2 + 2 * (b - a) * f.val t + (f.val t) ^ 2)
        ∂unitMeasure := by congr 1; ext t; ring
    _ = _ := by
      have hsum := integral_add (hc.add hl) hs
      simp only [Pi.add_apply] at hsum
      rw [hsum, integral_add hc hl, integral_const_mul,
        variation_integral_zero, integral_sq_eq_norm_sq]
      simp

theorem shifted_path_ae (δ a b : ℝ) (f : variationSpace) :
    (shiftCLM δ f + affineOffset δ a b) =ᵐ[shiftMeasure δ]
      (fun t ↦ path a b f (t + δ) - path a b f t) := by
  filter_upwards [Lp.coeFn_add (shiftCLM δ f) (affineOffset δ a b),
    shiftCLM_apply_ae δ f, Lp.coeFn_const 2 (shiftMeasure δ) ((b - a) * δ)] with t ht hs hb
  change affineOffset δ a b t = (b - a) * δ at hb
  rw [ht, Pi.add_apply, hs, hb]
  simp only [path]
  ring

/-- The coordinate energy is exactly the kinetic plus shifted-path integral. -/
theorem intervalEnergy_eq_integrals (δ weight a b : ℝ) (f : variationSpace) :
    intervalEnergy δ weight a b f =
      (∫ t, ((b - a) + f.val t) ^ 2 ∂unitMeasure) / 2 +
      weight / 2 * ∫ t, (path a b f (t + δ) - path a b f t) ^ 2 ∂shiftMeasure δ := by
  have hshift : (∫ t, (path a b f (t + δ) - path a b f t) ^ 2 ∂shiftMeasure δ) =
      ‖shiftCLM δ f + affineOffset δ a b‖ ^ 2 := by
    rw [← integral_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [shifted_path_ae δ a b f] with t ht
    exact congrArg (fun y : ℝ ↦ y ^ 2) ht.symm
  rw [kinetic_integral, hshift]
  unfold intervalEnergy energy
  ring

end MonadFormal.Temporal.Variational.Interval
