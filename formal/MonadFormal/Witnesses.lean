import MonadFormal.Influence
import MonadFormal.Approximation.Events
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite witnesses separating distinct claims

Paper companion: `paper/MonadFormal/Witnesses.tex`.
The lists below are equally weighted finite ensembles. Count equality on
supports of equal length is the exact marginal-probability comparison; no
floating-point testing is used. These examples establish obstructions,
not a new causal calculus or a physical emergence mechanism.
-/

namespace MonadFormal.Witnesses

open MeasureTheory ProbabilityTheory Approximation
open scoped ENNReal

def evenSupport : List Bit3 :=
  [(false, false, false), (false, true, true),
   (true, false, true), (true, true, false)]

def oddSupport : List Bit3 :=
  [(false, false, true), (false, true, false),
   (true, false, false), (true, true, true)]

def bit (i : Fin 3) (x : Bit3) : Bool :=
  match i.val with
  | 0 => x.1
  | 1 => x.2.1
  | _ => x.2.2

def pairCount (support : List Bit3) (i j : Fin 3) (u v : Bool) : Nat :=
  (support.filter (fun x ↦ bit i x == u && bit j x == v)).length

def parity (x : Bit3) : Bool := x.1.xor (x.2.1.xor x.2.2)

theorem equal_support_sizes : evenSupport.length = 4 ∧ oddSupport.length = 4 := by
  decide

theorem every_pair_marginal_equal :
    ∀ i j : Fin 3, i ≠ j → ∀ u v : Bool,
      pairCount evenSupport i j u v = 1 ∧ pairCount oddSupport i j u v = 1 := by
  decide

theorem opposite_joint_parity :
    (∀ x ∈ evenSupport, parity x = false) ∧
    (∀ x ∈ oddSupport, parity x = true) := by
  decide

theorem pair_budget_not_joint_budget : 4 + 4 ≤ (10 : Nat) ∧ ¬ 4 + 4 + 4 ≤ (10 : Nat) := by
  decide

def macroInput (x : Nat × Nat) : Nat := x.1 + x.2
def macroOutput (x : Nat × Nat) : Nat := x.1 + 2 * x.2

theorem same_macro_input_different_output :
    macroInput (1, 0) = macroInput (0, 1) ∧
    macroOutput (1, 0) ≠ macroOutput (0, 1) := by
  decide

theorem no_macro_response :
    ¬ ∃ f : Nat → Nat, ∀ x, macroOutput x = f (macroInput x) := by
  intro ⟨f, hf⟩
  have h₁ := hf (1, 0)
  have h₂ := hf (0, 1)
  have h := h₁.trans h₂.symm
  change (1 : Nat) = 2 at h
  contradiction

theorem binary_total_variation (p q : ℝ) :
    (|p - q| + |(1 - p) - (1 - q)|) / 2 = |p - q| := by
  have h : (1 - p) - (1 - q) = -(p - q) := by ring
  rw [h, abs_neg]
  ring

noncomputable def bernoulli (p : unitInterval) : ProbabilityMeasure Bool :=
  ⟨bernoulliMeasure true false p, inferInstance⟩

/-- The arithmetic witness is the general measure-theoretic TV, not a proxy metric. -/
theorem bernoulli_tv (p q : unitInterval) :
    tv (bernoulli p) (bernoulli q) = ENNReal.ofReal |(p : ℝ) - q| := by
  have expectation (r : unitInterval) (f : Bool → ℝ) :
      (∫ b, f b ∂bernoulli r) = (r : ℝ) * f true + (1 - r) * f false := by
    change (∫ b, f b ∂bernoulliMeasure true false r) = _
    simpa only [smul_eq_mul] using integral_bernoulliMeasure true false r f
  apply le_antisymm
  · refine iSup_le fun f ↦ ENNReal.ofReal_le_ofReal ?_
    rw [expectation p f.val, expectation q f.val]
    have hb : |f.val true - f.val false| ≤ 1 := by
      have ht := f.property.2 true
      have hf := f.property.2 false
      rw [abs_le]; constructor <;> linarith
    calc
      |(p : ℝ) * f.val true + (1 - p) * f.val false -
          ((q : ℝ) * f.val true + (1 - q) * f.val false)|
          = |(p : ℝ) - q| * |f.val true - f.val false| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |(p : ℝ) - q| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = |(p : ℝ) - q| := mul_one _
  · let f : Test Bool := ⟨fun b ↦ if b then 1 else 0, measurable_of_countable _,
      fun b ↦ by cases b <;> norm_num⟩
    have h := test_le_tv (bernoulli p) (bernoulli q) f
    simpa [expectation, f] using h

/-- A distance threshold need not be transitive, even for Bernoulli TV. -/
theorem approximate_closeness_not_transitive :
    |(0 : ℝ) - 2 / 5| ≤ 1 / 2 ∧
    |(2 / 5 : ℝ) - 4 / 5| ≤ 1 / 2 ∧
    ¬ |(0 : ℝ) - 4 / 5| ≤ 1 / 2 := by
  norm_num

theorem approximate_tv_not_transitive :
    ∃ μ ν ξ : ProbabilityMeasure Bool,
      tv μ ν ≤ (1 : ℝ≥0∞) / 2 ∧ tv ν ξ ≤ (1 : ℝ≥0∞) / 2 ∧
        ¬ tv μ ξ ≤ (1 : ℝ≥0∞) / 2 := by
  refine ⟨bernoulli 0, bernoulli ⟨2 / 5, by norm_num, by norm_num⟩,
    bernoulli ⟨4 / 5, by norm_num, by norm_num⟩, ?_⟩
  have half : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  simp only [bernoulli_tv, ← half,
    ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  exact approximate_closeness_not_transitive

/-- Reliable discrimination at error 1/5 need not pass a TV threshold 9/10. -/
theorem recordable_but_undetected :
    (0 : ℝ) ≤ 1 / 5 ∧ (1 / 5 : ℝ) < 1 / 2 ∧
    1 - (1 / 5 : ℝ) ≤ 4 / 5 ∧ (1 / 5 : ℝ) ≤ 1 / 5 ∧
    |(4 / 5 : ℝ) - 1 / 5| = 3 / 5 ∧
    ¬ (9 / 10 : ℝ) ≤ |(4 / 5 : ℝ) - 1 / 5| := by
  norm_num

end MonadFormal.Witnesses
