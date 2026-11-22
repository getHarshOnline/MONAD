import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Coercive quadratic variational problems

Paper companion: `paper/MonadFormal/Temporal/Variational.tex`.
The bounded operator `T : V →L[ℝ] W` and affine offset `b : W` determine
`energy`. Coercivity gives a stationary point; the exact energy gap gives
its unique minimality. The interval construction is in the `Interval` child.

`weight` denotes the paper's λ; the bare symbol is reserved by Lean.
-/

namespace MonadFormal.Temporal.Variational

open InnerProductSpace
open scoped RealInnerProductSpace

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Quadratic energy with affine offset `b`; positivity is a theorem hypothesis. -/
noncomputable def energy (T : V →L[ℝ] W) (weight : ℝ) (b : W) (u : V) : ℝ :=
  ‖u‖ ^ 2 / 2 + weight / 2 * ‖T u + b‖ ^ 2

/-- The bounded bilinear form associated to the quadratic part. -/
noncomputable def form (T : V →L[ℝ] W) (weight : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  innerSL ℝ + weight • (innerSL ℝ).bilinearComp T T

omit [CompleteSpace V] in
theorem form_apply (T : V →L[ℝ] W) (weight : ℝ) (u v : V) :
    form T weight u v = ⟪u, v⟫_ℝ + weight * ⟪T u, T v⟫_ℝ := rfl

omit [CompleteSpace V] in
theorem form_coercive (T : V →L[ℝ] W) {weight : ℝ} (hw : 0 ≤ weight) :
    IsCoercive (form T weight) := by
  refine ⟨1, zero_lt_one, fun u ↦ ?_⟩
  rw [form_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg hw (sq_nonneg ‖T u‖)]

/-- **Lax--Milgram:** nonnegative weight gives a solution of the weak Euler equation. -/
theorem exists_stationary (T : V →L[ℝ] W) {weight : ℝ} (hw : 0 ≤ weight) (b : W) :
    ∃ u : V, ∀ h : V, ⟪u, h⟫_ℝ + weight * ⟪T u + b, T h⟫_ℝ = 0 := by
  let ℓ : V →L[ℝ] ℝ := -weight • (innerSL ℝ b).comp T
  let g := (toDual ℝ V).symm ℓ
  let e := (form_coercive T hw).continuousLinearEquivOfBilin
  refine ⟨e.symm g, fun h ↦ ?_⟩
  have he := (form_coercive T hw).continuousLinearEquivOfBilin_apply (e.symm g) h
  change ⟪e (e.symm g), h⟫_ℝ = form T weight (e.symm g) h at he
  rw [e.apply_symm_apply, form_apply] at he
  have hg : ⟪g, h⟫_ℝ = -weight * ⟪b, T h⟫_ℝ := toDual_symm_apply
  rw [inner_add_left]
  linarith

omit [CompleteSpace V] in
/-- Exact energy gap; stationarity removes the linear cross term. -/
theorem energy_gap (T : V →L[ℝ] W) (weight : ℝ) (b : W) (u h : V)
    (hu : ∀ v : V, ⟪u, v⟫_ℝ + weight * ⟪T u + b, T v⟫_ℝ = 0) :
    energy T weight b (u + h) - energy T weight b u =
      (‖h‖ ^ 2 + weight * ‖T h‖ ^ 2) / 2 := by
  unfold energy
  rw [map_add, add_right_comm (T u) (T h) b, norm_add_sq_real, norm_add_sq_real]
  nlinarith [hu h]

omit [CompleteSpace V] in
/-- Stationarity implies global minimality when the penalty weight is nonnegative. -/
theorem minimizes_of_stationary (T : V →L[ℝ] W) {weight : ℝ} (hw : 0 ≤ weight)
    (b : W) (u : V)
    (hu : ∀ h : V, ⟪u, h⟫_ℝ + weight * ⟪T u + b, T h⟫_ℝ = 0) :
    ∀ v : V, energy T weight b u ≤ energy T weight b v := by
  intro v
  have hg := energy_gap T weight b u (v - u) hu
  simp only [add_sub_cancel] at hg
  nlinarith [sq_nonneg ‖v - u‖, mul_nonneg hw (sq_nonneg ‖T (v - u)‖)]

/-- Nonnegative weight gives a unique global minimizer on the Hilbert space. -/
theorem exists_unique_minimizer (T : V →L[ℝ] W) {weight : ℝ} (hw : 0 ≤ weight) (b : W) :
    ∃! u : V, ∀ v : V, energy T weight b u ≤ energy T weight b v := by
  obtain ⟨u, hu⟩ := exists_stationary T hw b
  have hmin := minimizes_of_stationary T hw b u hu
  refine ⟨u, hmin, fun v hv ↦ ?_⟩
  have hg := energy_gap T weight b u (v - u) hu
  simp only [add_sub_cancel] at hg
  have hn : ‖v - u‖ ^ 2 = 0 := by
    nlinarith [hmin v, hv u, sq_nonneg ‖v - u‖,
      mul_nonneg hw (sq_nonneg ‖T (v - u)‖)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

end MonadFormal.Temporal.Variational
