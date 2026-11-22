import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Entropy conservation under measure-preserving transport

Paper companion: `paper/MonadFormal/Entropy.tex`.
The analytic theorem is not replaced by a finite permutation example.
Integrability is retained explicitly so Lean's totalized integral cannot
silently turn an undefined physical entropy into a meaningful real value.
Quantum entropy requires a separately typed matrix/spectral theorem.
-/

namespace MonadFormal.Entropy

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

noncomputable def fine (μ : Measure X) (ρ : X → ℝ) : ℝ :=
  ∫ x, -(ρ x * Real.log (ρ x)) ∂μ

/-- An integrable observable keeps its integral under invertible,
measure-preserving transport, and remains integrable. -/
theorem observable_conservation (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (g : X → ℝ) (hg : Integrable g μ) :
    Integrable (g ∘ e.symm) μ ∧
      (∫ x, g (e.symm x) ∂μ) = ∫ x, g x ∂μ := by
  have hi := MeasurePreserving.symm e he
  exact ⟨hi.integrable_comp_of_integrable hg, hi.integral_comp' g⟩

/-- Fine-grained entropy is invariant whenever its integrand is integrable.
Real.log 0 is zero in Lean, agreeing with the continuous convention 0 log 0 = 0. -/
theorem fine_conservation (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (ρ : X → ℝ)
    (hρ : Integrable (fun x ↦ -(ρ x * Real.log (ρ x))) μ) :
    Integrable (fun x ↦ -((ρ ∘ e.symm) x * Real.log ((ρ ∘ e.symm) x))) μ ∧
      fine μ (ρ ∘ e.symm) = fine μ ρ := by
  exact observable_conservation μ e he (fun x ↦ -(ρ x * Real.log (ρ x))) hρ

end MonadFormal.Entropy
