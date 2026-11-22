import MonadFormal.Temporal
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# A mixed advance-delay boundary example

Paper companion: `paper/MonadFormal/Temporal/MixedBoundary.tex`.
The two half-intervals obey an ordinary coupled system, but their joining
condition is a boundary constraint. Resonance can make that constraint
inconsistent. Endpoint regularity is stated rather than inferred.
-/

namespace MonadFormal.Temporal.MixedBoundary

open MeasureTheory Set
open scoped Topology

/-- First half of the explicit split-system solution. -/
noncomputable def left (α β s : ℝ) : ℝ :=
  Real.cosh (α * s) - 1 + β * Real.sinh (α * s)

/-- Second half, expressed in the same local coordinate. -/
noncomputable def right (α β s : ℝ) : ℝ :=
  Real.sinh (α * s) + β * Real.cosh (α * s)

@[simp] theorem left_zero (α β : ℝ) : left α β 0 = 0 := by simp [left]

@[simp] theorem right_zero (α β : ℝ) : right α β 0 = β := by simp [right]

theorem left_derivative (α β s : ℝ) :
    HasDerivAt (left α β) (α * right α β s) s := by
  have h := (hasDerivAt_id s).const_mul α
  convert! (h.cosh.sub_const 1).add (h.sinh.const_mul β) using 1
  dsimp [left, right]
  ring

theorem right_derivative (α β s : ℝ) :
    HasDerivAt (right α β) (α * (left α β s + 1)) s := by
  have h := (hasDerivAt_id s).const_mul α
  convert! h.sinh.add (h.cosh.const_mul β) using 1
  dsimp [left, right]
  ring

/-- Scalar uniqueness derived by an integrating factor, not an assumed ODE solver. -/
theorem scalar_solution {z : ℝ → ℝ} {α t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn z (Icc 0 t))
    (hz : ∀ s ∈ Ioo 0 t, HasDerivAt z (α * z s) s) :
    z t = z 0 * Real.exp (α * t) := by
  have hd : ∀ s ∈ Ioo 0 t,
      HasDerivAt (fun r ↦ z r * Real.exp (-α * r)) 0 s := by
    intro s hs
    have he := ((hasDerivAt_id s).const_mul (-α)).exp
    convert! (hz s hs).mul he using 1
    dsimp
    ring
  have hwc : ContinuousOn (fun r ↦ z r * Real.exp (-α * r)) (Icc 0 t) :=
    hc.mul ((continuous_const.mul continuous_id).rexp.continuousOn)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hwc hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume 0 t)
  simp only [intervalIntegral.integral_zero, mul_zero, Real.exp_zero, mul_one] at hi
  have hw : z t * Real.exp (-α * t) = z 0 := by linarith
  calc
    z t = (z t * Real.exp (-α * t)) * Real.exp (α * t) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ = z 0 * Real.exp (α * t) := by rw [hw]

/-- All split-system solutions with the stated initial value have the explicit form. -/
theorem split_solution {u v : ℝ → ℝ} {α t : ℝ} (ht : 0 ≤ t)
    (hcu : ContinuousOn u (Icc 0 t)) (hcv : ContinuousOn v (Icc 0 t))
    (hu : ∀ s ∈ Ioo 0 t, HasDerivAt u (α * v s) s)
    (hv : ∀ s ∈ Ioo 0 t, HasDerivAt v (α * (u s + 1)) s)
    (h0 : u 0 = 0) :
    u t = left α (v 0) t ∧ v t = right α (v 0) t := by
  have hp := scalar_solution (z := fun s ↦ u s + 1 + v s) (α := α) ht
    ((hcu.add continuousOn_const).add hcv)
    (fun s hs ↦ by convert! ((hu s hs).add_const 1).add (hv s hs) using 1; ring)
  have hm := scalar_solution (z := fun s ↦ u s + 1 - v s) (α := -α) ht
    ((hcu.add continuousOn_const).sub hcv)
    (fun s hs ↦ by convert! ((hu s hs).add_const 1).sub (hv s hs) using 1; ring)
  simp only [h0, zero_add] at hp hm
  simp only [left, right, Real.cosh_eq, Real.sinh_eq, neg_mul] at *
  constructor <;> linarith

/-- Continuity at the half-interval seam is a scalar boundary equation. -/
theorem join_iff (α β : ℝ) :
    left α β (1 / 2) = right α β 0 ↔
      (1 - Real.sinh (α / 2)) * β = Real.cosh (α / 2) - 1 := by
  simp only [left, right_zero, mul_one_div]
  constructor <;> intro h <;> linarith

/-- Away from resonance, exactly one coefficient joins the two halves. -/
theorem join_unique {α : ℝ} (h : Real.sinh (α / 2) ≠ 1) (β : ℝ) :
    left α β (1 / 2) = right α β 0 ↔
      β = (Real.cosh (α / 2) - 1) / (1 - Real.sinh (α / 2)) := by
  rw [join_iff, eq_div_iff (sub_ne_zero.mpr (Ne.symm h)), mul_comm]

/-- At resonance the joining equation has no solution. -/
theorem no_join_at_resonance {α : ℝ} (h : Real.sinh (α / 2) = 1) (β : ℝ) :
    left α β (1 / 2) ≠ right α β 0 := by
  intro hj
  have hc : Real.cosh (α / 2) = 1 := by
    have he := (join_iff α β).mp hj
    rw [h] at he
    linarith
  have hi := Real.cosh_sq_sub_sinh_sq (α / 2)
  rw [h, hc] at hi
  norm_num at hi

theorem resonant_parameter : Real.sinh ((2 * Real.arsinh 1) / 2) = 1 := by
  simp

/-- Nonexistence applies to every regular split solution, not just an ansatz. -/
theorem no_split_at_resonance {u v : ℝ → ℝ} {α : ℝ}
    (hα : Real.sinh (α / 2) = 1)
    (hcu : ContinuousOn u (Icc 0 (1 / 2 : ℝ)))
    (hcv : ContinuousOn v (Icc 0 (1 / 2 : ℝ)))
    (hu : ∀ s ∈ Ioo 0 (1 / 2 : ℝ), HasDerivAt u (α * v s) s)
    (hv : ∀ s ∈ Ioo 0 (1 / 2 : ℝ), HasDerivAt v (α * (u s + 1)) s)
    (h0 : u 0 = 0) (hj : u (1 / 2) = v 0) : False := by
  have hs := split_solution (by norm_num : (0 : ℝ) ≤ 1 / 2) hcu hcv hu hv h0
  apply no_join_at_resonance hα (v 0)
  simpa only [right_zero] using hs.1.symm.trans hj

/-- Piecewise path with zero history and unit future; endpoint jumps are not hidden. -/
noncomputable def path (α β t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 / 2 then left α β t
  else if t ≤ 1 then right α β (t - 1 / 2) else 1

theorem path_history (α β : ℝ) {t : ℝ} (ht : t ≤ 0) : path α β t = 0 := by
  simp [path, ht]

theorem path_left (α β : ℝ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 2) :
    path α β t = left α β t := by
  rw [path, ite_eq_right (not_le.mpr h0), ite_eq_left h1]

theorem path_right (α β : ℝ) {t : ℝ} (h0 : 1 / 2 < t) (h1 : t ≤ 1) :
    path α β t = right α β (t - 1 / 2) := by
  rw [path, ite_eq_right (by linarith : ¬t ≤ 0), ite_eq_right (not_le.mpr h0), ite_eq_left h1]

theorem path_future (α β : ℝ) {t : ℝ} (ht : 1 < t) : path α β t = 1 := by
  rw [path, ite_eq_right (by linarith : ¬t ≤ 0), ite_eq_right (by linarith : ¬t ≤ 1 / 2),
    ite_eq_right (not_le.mpr ht)]

/-- The assembled path solves the mixed equation on the first open half. -/
theorem path_equation_left (α β : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 (1 / 2 : ℝ)) :
    HasDerivAt (path α β)
      (α * (path α β (t - 1 / 2) + path α β (t + 1 / 2))) t := by
  have hd : HasDerivAt (path α β) (α * right α β t) t :=
    (left_derivative α β t).congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact path_left α β hs.1 hs.2.le)
  rw [path_history α β (by linarith [ht.2] : t - 1 / 2 ≤ 0),
    path_right α β (by linarith [ht.1] : 1 / 2 < t + 1 / 2)
      (by linarith [ht.2] : t + 1 / 2 ≤ 1)]
  simpa only [add_sub_cancel_right, zero_add] using hd

/-- The assembled path solves the mixed equation on the second open half. -/
theorem path_equation_right (α β : ℝ) {t : ℝ} (ht : t ∈ Ioo (1 / 2 : ℝ) 1) :
    HasDerivAt (path α β)
      (α * (path α β (t - 1 / 2) + path α β (t + 1 / 2))) t := by
  have hd : HasDerivAt (fun s ↦ right α β (s - 1 / 2))
      (α * (left α β (t - 1 / 2) + 1)) t := by
    simpa only [mul_one, Function.comp_def, id_eq] using
      (right_derivative α β (t - 1 / 2)).comp t ((hasDerivAt_id t).sub_const (1 / 2))
  have hp := hd.congr_of_eventuallyEq (f₁ := path α β) (by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact path_right α β hs.1 hs.2.le)
  rw [path_left α β (by linarith [ht.1] : 0 < t - 1 / 2)
      (by linarith [ht.2] : t - 1 / 2 ≤ 1 / 2),
    path_future α β (by linarith [ht.1] : 1 < t + 1 / 2)]
  exact hp

/-- Matching the unit future continuously is an additional condition. -/
theorem terminal_match_iff {α β : ℝ} (h : Real.sinh (α / 2) ≠ 1)
    (hj : left α β (1 / 2) = right α β 0) :
    right α β (1 / 2) = 1 ↔ Real.cosh (α / 2) = 2 * Real.sinh (α / 2) := by
  have he := (join_iff α β).mp hj
  have hi := Real.cosh_sq_sub_sinh_sq (α / 2)
  have hm : right α β (1 / 2) * (1 - Real.sinh (α / 2)) =
      1 + Real.sinh (α / 2) - Real.cosh (α / 2) := by
    simp only [right, mul_one_div]
    nlinarith [congrArg (fun r ↦ Real.cosh (α / 2) * r) he]
  constructor
  · intro hr
    rw [hr] at hm
    linarith
  · intro hc
    have hprod : (right α β (1 / 2) - 1) * (1 - Real.sinh (α / 2)) = 0 := by
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr (Ne.symm h)))

theorem path_continuousOn {α β : ℝ} (hj : left α β (1 / 2) = right α β 0) :
    ContinuousOn (path α β) (Icc 0 1) := by
  have hl : Continuous (left α β) := continuous_iff_continuousAt.mpr
    (fun s ↦ (left_derivative α β s).continuousAt)
  have hr : Continuous (fun s ↦ right α β (s - 1 / 2)) :=
    (continuous_iff_continuousAt.mpr (fun s ↦ (right_derivative α β s).continuousAt)).comp
      (continuous_id.sub continuous_const)
  have hg := hl.if_le hr continuous_id (continuous_const : Continuous (fun _ : ℝ ↦ (1 / 2 : ℝ)))
    (by intro s hs; dsimp at hs; subst s; simpa only [sub_self] using hj)
  apply hg.continuousOn.congr
  intro s hs
  by_cases hz : s ≤ 0
  · have he : s = 0 := le_antisymm hz hs.1
    subst s
    simp [path, left_zero]
  · by_cases hh : s ≤ 1 / 2
    · simp only [path, id_eq, hz, hh, ite_false, ite_true]
    · simp only [path, id_eq, hz, hh, hs.2, ite_false, ite_true]

theorem terminal_parameter_iff (α : ℝ) :
    Real.cosh (α / 2) = 2 * Real.sinh (α / 2) ↔ α = Real.log 3 := by
  have hi : Real.exp (α / 2) * Real.exp (-(α / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hs : Real.exp (α / 2) * Real.exp (α / 2) = Real.exp α := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp := Real.exp_pos (α / 2)
  simp only [Real.cosh_eq, Real.sinh_eq]
  constructor
  · intro h
    have he : Real.exp α = 3 := by
      nlinarith [congrArg (fun r ↦ Real.exp (α / 2) * r) h]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)] at he
    exact Real.exp_injective he
  · intro h
    have he : Real.exp α = 3 := by rw [h, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    have hm : Real.exp (α / 2) = 3 * Real.exp (-(α / 2)) := by
      nlinarith [congrArg (fun r ↦ Real.exp (-(α / 2)) * r) hs]
    linarith

/-- The declared solution class does not require differentiability at the seam. -/
def IsSolution (α : ℝ) (x : ℝ → ℝ) : Prop :=
    ContinuousOn x (Icc 0 1) ∧ x 0 = 0 ∧
      (∀ t ≤ 0, x t = 0) ∧ (∀ t, 1 < t → x t = 1) ∧
      (∀ t ∈ Ioo 0 (1 / 2 : ℝ) ∪ Ioo (1 / 2 : ℝ) 1,
        HasDerivAt x (α * (x (t - 1 / 2) + x (t + 1 / 2))) t)

/-- Existence outside resonance, including boundary data, continuity and both equations. -/
theorem exists_mixed_solution {α : ℝ} (h : Real.sinh (α / 2) ≠ 1) :
    ∃ x : ℝ → ℝ, IsSolution α x := by
  let β := (Real.cosh (α / 2) - 1) / (1 - Real.sinh (α / 2))
  have hj := (join_unique h β).mpr rfl
  refine ⟨path α β, path_continuousOn hj, path_history α β le_rfl,
    fun t ht ↦ path_history α β ht, fun t ht ↦ path_future α β ht, ?_⟩
  intro t ht
  rcases ht with ht | ht
  · exact path_equation_left α β ht
  · exact path_equation_right α β ht

/-- Every continuous mixed-equation solution supplies the split-system obstruction. -/
theorem no_mixed_at_resonance {x : ℝ → ℝ} {α : ℝ}
    (hα : Real.sinh (α / 2) = 1)
    (hc : ContinuousOn x (Icc 0 1)) (h0 : x 0 = 0)
    (hh : ∀ t ≤ 0, x t = 0) (hf : ∀ t, 1 < t → x t = 1)
    (he : ∀ t ∈ Ioo 0 (1 / 2 : ℝ) ∪ Ioo (1 / 2 : ℝ) 1,
      HasDerivAt x (α * (x (t - 1 / 2) + x (t + 1 / 2))) t) : False := by
  have hcu : ContinuousOn x (Icc 0 (1 / 2 : ℝ)) :=
    hc.mono (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩)
  have hcv : ContinuousOn (fun s ↦ x (s + 1 / 2)) (Icc 0 (1 / 2 : ℝ)) :=
    hc.comp (continuous_id.add_const (1 / 2)).continuousOn (by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  apply no_split_at_resonance (u := x) (v := fun s ↦ x (s + 1 / 2)) hα hcu hcv
  · intro s hs
    have hd := he s (Or.inl hs)
    simpa only [hh (s - 1 / 2) (by linarith [hs.2]), zero_add] using hd
  · intro s hs
    have hd := he (s + 1 / 2) (Or.inr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hp := hd.comp s ((hasDerivAt_id s).add_const (1 / 2))
    simpa only [Function.comp_def, id_eq, mul_one, add_sub_cancel_right,
      hf (s + 1 / 2 + 1 / 2) (by linarith [hs.1])] using hp
  · exact h0
  · simp

/-- Exact existence criterion for the declared boundary and regularity class. -/
theorem solution_exists_iff (α : ℝ) :
    (∃ x : ℝ → ℝ, IsSolution α x) ↔ Real.sinh (α / 2) ≠ 1 := by
  constructor
  · rintro ⟨x, hc, h0, hh, hf, he⟩ hα
    exact no_mixed_at_resonance hα hc h0 hh hf he
  · exact exists_mixed_solution

end MonadFormal.Temporal.MixedBoundary
