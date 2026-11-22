import MonadFormal.Temporal.Variational.Interval

/-!
# Endpoint-constrained paths and velocity coordinates

Paper companion: `paper/MonadFormal/Temporal/Variational/Paths.tex`.
An admissible path is absolutely continuous on [0,1], has a square-integrable
derivative, and takes the prescribed endpoint values. Equality is required
only on [0,1]; values outside that interval carry no boundary condition.
-/

namespace MonadFormal.Temporal.Variational.Interval

open MeasureTheory Set Filter
open scoped Topology

/-- The one-dimensional H¹ path class in its absolutely continuous representative. -/
structure Admissible (a b : ℝ) (x : ℝ → ℝ) : Prop where
  absolutelyContinuous : AbsolutelyContinuousOnInterval x 0 1
  derivative_memLp : MemLp (deriv x) 2 unitMeasure
  initial : x 0 = a
  terminal : x 1 = b

theorem unit_integral_eq (g : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s in 0..t, g s ∂unitMeasure) = ∫ s in 0..t, g s := by
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
  simp only [unitMeasure, Measure.restrict_restrict measurableSet_Ioc]
  rw [inter_eq_left.mpr (show Ioc 0 t ⊆ Icc (0 : ℝ) 1 from
    fun _ hs ↦ ⟨hs.1.le, hs.2.trans ht.2⟩)]

theorem ae_mem_interior : ∀ᵐ t ∂unitMeasure, t ∈ Ioo (0 : ℝ) 1 := by
  rw [unitMeasure, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact ae_restrict_mem measurableSet_Ioo

/-- Equality of paths on the interval gives equality of their derivatives almost everywhere. -/
theorem deriv_eq_ae_of_eqOn {x y : ℝ → ℝ} (hxy : EqOn x y (Icc (0 : ℝ) 1)) :
    deriv x =ᵐ[unitMeasure] deriv y := by
  filter_upwards [ae_mem_interior] with t ht
  have he : x =ᶠ[𝓝 t] y := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hxy ⟨hs.1.le, hs.2.le⟩
  exact he.deriv_eq

/-- A path on [0,1] determines its endpoint-preserving velocity uniquely. -/
theorem path_injective (a b : ℝ) {f g : variationSpace}
    (hfg : EqOn (path a b f) (path a b g) (Icc (0 : ℝ) 1)) : f = g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [deriv_eq_ae_of_eqOn hfg, path_hasDerivAt_ae a b f,
    path_hasDerivAt_ae a b g] with t ht hf hg
  rw [hf.deriv, hg.deriv] at ht
  exact add_left_cancel ht

/-- Every constructed path has the declared H¹ regularity and endpoints. -/
theorem path_admissible (a b : ℝ) (f : variationSpace) : Admissible a b (path a b f) := by
  refine ⟨path_absolutelyContinuous a b f, ?_, (path_endpoints a b f).1,
    (path_endpoints a b f).2⟩
  have hm := (memLp_const (b - a) : MemLp (fun _ : ℝ ↦ b - a) 2 unitMeasure).add
    (Lp.memLp f.val)
  apply hm.ae_eq
  filter_upwards [path_hasDerivAt_ae a b f] with t ht
  exact ht.deriv.symm

/-- Subtract the affine slope before integrating an admissible path's derivative. -/
theorem primitive_centered_derivative {a b : ℝ} {x : ℝ → ℝ} (hx : Admissible a b x)
    (v : Velocity) (hv : v =ᵐ[unitMeasure] (fun t ↦ deriv x t - (b - a)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    primitive v t = x t - a - (b - a) * t := by
  have hac : AbsolutelyContinuousOnInterval x 0 t := hx.absolutelyContinuous.mono (by
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl ht.2)
  calc
    _ = ∫ s in 0..t, (deriv x s - (b - a)) ∂unitMeasure :=
      intervalIntegral.integral_congr_ae (hv.mono (fun _ h _ ↦ h))
    _ = ∫ s in 0..t, (deriv x s - (b - a)) := unit_integral_eq _ ht
    _ = _ := by
      rw [intervalIntegral.integral_sub hac.intervalIntegrable_deriv intervalIntegrable_const,
        hac.integral_deriv_eq_sub, intervalIntegral.integral_const, hx.initial]
      simp only [sub_zero, smul_eq_mul]
      ring

/-- Velocity coordinates cover every admissible path, uniquely on the unit interval. -/
theorem exists_unique_velocity {a b : ℝ} {x : ℝ → ℝ} (hx : Admissible a b x) :
    ∃! f : variationSpace, EqOn (path a b f) x (Icc (0 : ℝ) 1) := by
  have hm := hx.derivative_memLp.sub (memLp_const (b - a))
  let v : Velocity := hm.toLp (fun t ↦ deriv x t - (b - a))
  have hv : v =ᵐ[unitMeasure] (fun t ↦ deriv x t - (b - a)) := hm.coeFn_toLp
  have hzero : primitive v 1 = 0 := by
    rw [primitive_centered_derivative hx v hv (by norm_num), hx.terminal]
    ring
  let f : variationSpace := ⟨v, hzero⟩
  have hf : EqOn (path a b f) x (Icc (0 : ℝ) 1) := by
    intro t ht
    change a + (b - a) * t + primitive v t = x t
    rw [primitive_centered_derivative hx v hv ht]
    ring
  exact ⟨f, hf, fun g hg ↦ path_injective a b (hg.trans hf.symm)⟩

/-- Kinetic energy plus the squared difference across an admitted forward shift. -/
noncomputable def pathEnergy (δ weight : ℝ) (x : ℝ → ℝ) : ℝ :=
  (∫ t, (deriv x t) ^ 2 ∂unitMeasure) / 2 +
    weight / 2 * ∫ t, (x (t + δ) - x t) ^ 2 ∂shiftMeasure δ

/-- The path functional and its velocity-coordinate expression coincide. -/
theorem pathEnergy_path (δ weight a b : ℝ) (f : variationSpace) :
    pathEnergy δ weight (path a b f) = intervalEnergy δ weight a b f := by
  rw [intervalEnergy_eq_integrals]
  unfold pathEnergy
  congr 2
  apply integral_congr_ae
  filter_upwards [path_hasDerivAt_ae a b f] with t ht
  rw [ht.deriv]

/-- Only the restriction of a path to [0,1] enters its energy. -/
theorem pathEnergy_congr {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) (weight : ℝ)
    {x y : ℝ → ℝ} (hxy : EqOn x y (Icc (0 : ℝ) 1)) :
    pathEnergy δ weight x = pathEnergy δ weight y := by
  have hd : (∫ t, (deriv x t) ^ 2 ∂unitMeasure) =
      ∫ t, (deriv y t) ^ 2 ∂unitMeasure := by
    apply integral_congr_ae
    exact (deriv_eq_ae_of_eqOn hxy).mono (fun _ h ↦ congrArg (fun z : ℝ ↦ z ^ 2) h)
  have hs : (∫ t, (x (t + δ) - x t) ^ 2 ∂shiftMeasure δ) =
      ∫ t, (y (t + δ) - y t) ^ 2 ∂shiftMeasure δ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := Icc (0 : ℝ) (1 - δ))
      measurableSet_Icc] with t ht
    rw [hxy ⟨by linarith [ht.1, hδ.1], by linarith [ht.2]⟩,
      hxy ⟨ht.1, by linarith [ht.2, hδ.1]⟩]
  simp only [pathEnergy, hd, hs]

/-- A minimizer exists in the full admissible path class and is unique on [0,1]. -/
theorem exists_unique_path_minimizer {δ weight : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1)
    (hw : 0 ≤ weight) (a b : ℝ) :
    ∃ x : ℝ → ℝ, Admissible a b x ∧
      (∀ y : ℝ → ℝ, Admissible a b y → pathEnergy δ weight x ≤ pathEnergy δ weight y) ∧
      ∀ y : ℝ → ℝ, Admissible a b y →
        (∀ z : ℝ → ℝ, Admissible a b z → pathEnergy δ weight y ≤ pathEnergy δ weight z) →
        EqOn y x (Icc (0 : ℝ) 1) := by
  obtain ⟨f, hf, huniq⟩ := exists_unique_interval_minimizer δ a b hw
  refine ⟨path a b f, path_admissible a b f, ?_, ?_⟩
  · intro y hy
    obtain ⟨g, hg, _⟩ := exists_unique_velocity hy
    rw [← pathEnergy_congr hδ weight hg, pathEnergy_path, pathEnergy_path]
    exact hf g
  · intro y hy hmin
    obtain ⟨g, hg, _⟩ := exists_unique_velocity hy
    have hgf : g = f := huniq g (by
      intro k
      have hk := hmin (path a b k) (path_admissible a b k)
      rw [← pathEnergy_congr hδ weight hg, pathEnergy_path, pathEnergy_path] at hk
      exact hk)
    exact hg.symm.trans (by rw [hgf]; exact fun _ _ ↦ rfl)

end MonadFormal.Temporal.Variational.Interval
