import MonadFormal.Information.Testing.Hellinger.Variation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# From square-root regularity to density regularity

Paper companion: `paper/MonadFormal/Information/Testing/Hellinger/Regularity.tex`.
Multiplication sends L² × L² continuously into L¹. Its product rule gives
the density derivative and the first-order total-variation coefficient.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- L² differentiability of square-root densities at a scalar parameter.
The derivative is the half-score-weighted root when a score representation exists. -/
def HasRootDerivAt (p : ℝ → RootDensity μ) (v : Lp ℝ 2 μ) (θ : ℝ) : Prop :=
  HasDerivAt (fun t ↦ (p t).root) v θ

/-- Normalization forces the root derivative to be tangent to the unit sphere. -/
theorem HasRootDerivAt.orthogonal {p : ℝ → RootDensity μ} {v : Lp ℝ 2 μ} {θ : ℝ}
    (hp : HasRootDerivAt p v θ) : ⟪(p θ).root, v⟫_ℝ = 0 := by
  have hd := hp.norm_sq
  simp only [(p _).norm_eq_one, one_pow] at hd
  have he := hd.unique (hasDerivAt_const θ (1 : ℝ))
  linarith

/-- The quadratic Hellinger coefficient follows from the derivative; it is not an axiom. -/
theorem HasRootDerivAt.hellinger_limit {p : ℝ → RootDensity μ} {v : Lp ℝ 2 μ} {θ : ℝ}
    (hp : HasRootDerivAt p v θ) :
    Tendsto (fun h : ℝ ↦ (p (θ + h)).hellingerSq (p θ) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (‖v‖ ^ 2 / 2)) := by
  have ht := hp.tendsto_slope_zero.norm.pow 2
  have he (h : ℝ) :
      (p (θ + h)).hellingerSq (p θ) / h ^ 2 =
        ‖h⁻¹ • ((p (θ + h)).root - (p θ).root)‖ ^ 2 / 2 := by
    simp only [RootDensity.hellingerSq, norm_smul, Real.norm_eq_abs, abs_inv, mul_pow,
      inv_pow, sq_abs]
    field_simp
  simp_rw [he]
  exact ht.div_const 2

/-- The integrable product of two square-integrable functions. -/
noncomputable def l2Product (f g : Lp ℝ 2 μ) : Lp ℝ 1 μ :=
  ((Lp.memLp f).integrable_mul (Lp.memLp g)).toL1 (fun x ↦ f x * g x)

theorem l2Product_coe (f g : Lp ℝ 2 μ) :
    l2Product f g =ᵐ[μ] (fun x ↦ f x * g x) :=
  ((Lp.memLp f).integrable_mul (Lp.memLp g)).coeFn_toL1

theorem l2Product_norm_le (f g : Lp ℝ 2 μ) : ‖l2Product f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [l2Product, L1.norm_of_fun_eq_integral_norm]
  simpa only [Real.norm_eq_abs] using integral_abs_mul_le_L2_norm f g

theorem l2Product_comm (f g : Lp ℝ 2 μ) : l2Product f g = l2Product g f := by
  apply Lp.ext
  filter_upwards [l2Product_coe f g, l2Product_coe g f] with x hx hy
  rw [hx, hy, mul_comm]

/-- Continuous multiplication, with its L²-to-L¹ norm bound proved by Cauchy–Schwarz. -/
noncomputable def l2ProductCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  (LinearMap.mk₂ ℝ l2Product
    (fun f g k ↦ by
      apply Lp.ext
      filter_upwards [l2Product_coe (f + g) k, l2Product_coe f k, l2Product_coe g k,
        Lp.coeFn_add f g, Lp.coeFn_add (l2Product f k) (l2Product g k)] with x h₁ h₂ h₃ h₄ h₅
      simp only [h₁, h₂, h₃, h₄, h₅, Pi.add_apply, add_mul])
    (fun c f g ↦ by
      apply Lp.ext
      filter_upwards [l2Product_coe (c • f) g, l2Product_coe f g, Lp.coeFn_smul c f,
        Lp.coeFn_smul c (l2Product f g)] with x h₁ h₂ h₃ h₄
      simp only [h₁, h₂, h₃, h₄, Pi.smul_apply, smul_eq_mul, mul_assoc])
    (fun f g k ↦ by
      apply Lp.ext
      filter_upwards [l2Product_coe f (g + k), l2Product_coe f g, l2Product_coe f k,
        Lp.coeFn_add g k, Lp.coeFn_add (l2Product f g) (l2Product f k)] with x h₁ h₂ h₃ h₄ h₅
      simp only [h₁, h₂, h₃, h₄, h₅, Pi.add_apply, mul_add])
    (fun c f g ↦ by
      apply Lp.ext
      filter_upwards [l2Product_coe f (c • g), l2Product_coe f g, Lp.coeFn_smul c g,
        Lp.coeFn_smul c (l2Product f g)] with x h₁ h₂ h₃ h₄
      simp only [h₁, h₂, h₃, h₄, Pi.smul_apply, smul_eq_mul]
      ring)).mkContinuous₂ 1 (fun f g ↦ by
        simpa only [LinearMap.mk₂_apply, one_mul] using l2Product_norm_le f g)

namespace RootDensity

/-- The represented density as an L¹ element, with the same square-root owner as `law`. -/
noncomputable def density (p : RootDensity μ) : Lp ℝ 1 μ := l2Product p.root p.root

theorem density_coe (p : RootDensity μ) : p.density =ᵐ[μ] (fun x ↦ p.root x ^ 2) := by
  simpa only [density, pow_two] using l2Product_coe p.root p.root

theorem tv_eq_density_norm (p q : RootDensity μ) :
    (Approximation.tv p.law q.law).toReal = ‖p.density - q.density‖ / 2 := by
  rw [tv_toReal_eq_density_integral, L1.norm_eq_integral_norm]
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub p.density q.density, p.density_coe, q.density_coe] with x h₁ h₂ h₃
  simp only [h₁, h₂, h₃, Pi.sub_apply, Real.norm_eq_abs]

end RootDensity

/-- The L² square-root derivative induces an actual L¹ density derivative. -/
theorem HasRootDerivAt.density_deriv {p : ℝ → RootDensity μ} {v : Lp ℝ 2 μ} {θ : ℝ}
    (hp : HasRootDerivAt p v θ) :
    HasDerivAt (fun t ↦ (p t).density) ((2 : ℝ) • l2Product (p θ).root v) θ := by
  have hL := (l2ProductCLM (μ := μ)).hasFDerivAt.comp_hasDerivAt θ hp
  have hd := hL.clm_apply hp
  convert hd using 1
  · rfl
  · change (2 : ℝ) • l2Product (p θ).root v = l2Product v (p θ).root + l2Product (p θ).root v
    rw [l2Product_comm v, two_smul]

/-- Local total variation has a first-order coefficient; Hellinger squared has a second-order one. -/
theorem HasRootDerivAt.tv_limit {p : ℝ → RootDensity μ} {v : Lp ℝ 2 μ} {θ : ℝ}
    (hp : HasRootDerivAt p v θ) :
    Tendsto (fun h : ℝ ↦ (Approximation.tv (p (θ + h)).law (p θ).law).toReal / |h|)
      (𝓝[≠] 0) (𝓝 ‖l2Product (p θ).root v‖) := by
  have ht := hp.density_deriv.tendsto_slope_zero.norm
  have he (h : ℝ) :
      (Approximation.tv (p (θ + h)).law (p θ).law).toReal / |h| =
        ‖h⁻¹ • ((p (θ + h)).density - (p θ).density)‖ / 2 := by
    rw [RootDensity.tv_eq_density_norm, norm_smul, Real.norm_eq_abs, abs_inv]
    ring
  simp_rw [he]
  convert ht.div_const 2 using 1
  simp [norm_smul]

end MonadFormal.Information
