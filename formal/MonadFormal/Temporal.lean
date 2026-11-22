import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Exact elimination of a hidden linear component

Paper companion: `paper/MonadFormal/Temporal.tex`.
Operator exponentials and Bochner integrals are genuine Banach-space objects.
Past-memory and terminal-value formulas come from the same coupled ODE;
neither formula proves a new causal mechanism or an affordable state encoding.
-/

namespace MonadFormal.Temporal

open MeasureTheory Set

variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The ordinary operator-exponential propagator of a bounded generator. -/
noncomputable def flow (D : V →L[ℝ] V) (t : ℝ) : V →L[ℝ] V :=
  NormedSpace.exp (t • D)

omit [CompleteSpace V] in
@[simp] theorem flow_zero (D : V →L[ℝ] V) : flow D 0 = 1 := by
  simp [flow, NormedSpace.exp_zero]

theorem continuous_flow (D : V →L[ℝ] V) : Continuous (flow D) :=
  (differentiable_exp_smul_const ℝ D).continuous

theorem flow_derivative (D : V →L[ℝ] V) (t : ℝ) :
    HasDerivAt (flow D) (flow D t * D) t :=
  hasDerivAt_exp_smul_const D t

theorem backward_flow_derivative (D : V →L[ℝ] V) (t s : ℝ) :
    HasDerivAt (fun r ↦ flow D (t - r)) (-(flow D (t - s) * D)) s := by
  simpa only [Function.comp_def, zero_sub, neg_smul, one_smul] using
    (flow_derivative D (t - s)).scomp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))

theorem weighted_forcing_integrable (D : V →L[ℝ] V) {f : ℝ → V}
    {a b : ℝ} (hf : ContinuousOn f (uIcc a b)) (t : ℝ) :
    IntervalIntegrable (fun s ↦ flow D (t - s) (f s)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact ((continuous_flow D).comp (continuous_const.sub continuous_id)).continuousOn.clm_apply hf

/-- Differentiate the integrating factor; the hidden-state terms cancel. -/
theorem integrating_factor_derivative (D : V →L[ℝ] V) {v f : ℝ → V} (t s : ℝ)
    (hv : HasDerivAt v (f s + D (v s)) s) :
    HasDerivAt (fun r ↦ flow D (t - r) (v r)) (flow D (t - s) (f s)) s := by
  convert (backward_flow_derivative D t s).clm_apply hv using 1
  simp only [neg_apply, mul_apply_eq_comp, map_add]
  abel

/-- Variation of constants on an arbitrary oriented interval. -/
theorem variation_of_constants (D : V →L[ℝ] V) {v f : ℝ → V} {a t : ℝ}
    (hf : ContinuousOn f (uIcc a t))
    (hv : ∀ s ∈ uIcc a t, HasDerivAt v (f s + D (v s)) s) :
    v t = flow D (t - a) (v a) + ∫ s in a..t, flow D (t - s) (f s) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs ↦ integrating_factor_derivative D t s (hv s hs))
    (weighted_forcing_integrable D hf t)
  simp only [sub_self, flow_zero, one_apply_eq_self] at hi
  exact (sub_eq_iff_eq_add.mp hi.symm).trans (add_comm _ _)

/-- The same formula, anchored at a terminal value, reverses the integral. -/
theorem terminal_variation_of_constants (D : V →L[ℝ] V) {v f : ℝ → V} {t T : ℝ}
    (hf : ContinuousOn f (uIcc t T))
    (hv : ∀ s ∈ uIcc t T, HasDerivAt v (f s + D (v s)) s) :
    v t = flow D (t - T) (v T) - ∫ s in t..T, flow D (t - s) (f s) := by
  have h := variation_of_constants D (a := T) (t := t)
    (by simpa only [uIcc_comm] using hf) (by simpa only [uIcc_comm] using hv)
  rw [intervalIntegral.integral_symm] at h
  simpa only [sub_eq_add_neg] using h

/-- Exact past-memory equation after eliminating v from a coupled linear system. -/
theorem memory_equation (A : U →L[ℝ] U) (B : V →L[ℝ] U)
    (C : U →L[ℝ] V) (D : V →L[ℝ] V) {u : ℝ → U} {v : ℝ → V} {a t : ℝ}
    (hc : ContinuousOn u (uIcc a t))
    (hu : HasDerivAt u (A (u t) + B (v t)) t)
    (hv : ∀ s ∈ uIcc a t, HasDerivAt v (C (u s) + D (v s)) s) :
    HasDerivAt u (A (u t) + B (flow D (t - a) (v a)) +
      ∫ s in a..t, B (flow D (t - s) (C (u s)))) t := by
  have hC : ContinuousOn (fun s ↦ C (u s)) (uIcc a t) := C.continuous.comp_continuousOn hc
  have h := variation_of_constants D hC hv
  convert hu using 1
  rw [h, map_add, ← B.intervalIntegral_comp_comm (weighted_forcing_integrable D hC t)]
  abel

/-- A terminally constrained hidden state gives a future integral, not an IVP law. -/
theorem terminal_equation (A : U →L[ℝ] U) (B : V →L[ℝ] U)
    (C : U →L[ℝ] V) (D : V →L[ℝ] V) {u : ℝ → U} {v : ℝ → V} {t T : ℝ}
    (hc : ContinuousOn u (uIcc t T))
    (hu : HasDerivAt u (A (u t) + B (v t)) t)
    (hv : ∀ s ∈ uIcc t T, HasDerivAt v (C (u s) + D (v s)) s) :
    HasDerivAt u (A (u t) + B (flow D (t - T) (v T)) -
      ∫ s in t..T, B (flow D (t - s) (C (u s)))) t := by
  have hC : ContinuousOn (fun s ↦ C (u s)) (uIcc t T) := C.continuous.comp_continuousOn hc
  have h := terminal_variation_of_constants D hC hv
  convert hu using 1
  rw [h, map_sub, ← B.intervalIntegral_comp_comm (weighted_forcing_integrable D hC t)]
  abel

omit [CompleteSpace U] [CompleteSpace V] in
/-- Enlarging the state to the pair recovers the ordinary coupled vector field. -/
theorem augmented_derivative (A : U →L[ℝ] U) (B : V →L[ℝ] U)
    (C : U →L[ℝ] V) (D : V →L[ℝ] V) {u : ℝ → U} {v : ℝ → V} {t : ℝ}
    (hu : HasDerivAt u (A (u t) + B (v t)) t)
    (hv : HasDerivAt v (C (u t) + D (v t)) t) :
    HasDerivAt (fun s ↦ (u s, v s)) (A (u t) + B (v t), C (u t) + D (v t)) t :=
  hu.prodMk hv

end MonadFormal.Temporal
