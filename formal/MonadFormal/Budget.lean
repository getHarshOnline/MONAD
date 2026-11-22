import MonadFormal.Sandbox
import Std

/-!
# Budgeted continuation equivalence

Actions are total deterministic maps. Costs are nonnegative natural numbers.
The residual law and one-step characterization permit zero costs; an acyclic
implementation of the characterization additionally needs positive costs.
Partial actions require separate, observable admission/failure semantics.

Paper companion: `paper/MonadFormal/Budget.tex`.
-/

namespace MonadFormal.Budget

variable {X A P O : Type}

def cost (c : A → Nat) : List A → Nat
  | [] => 0
  | a :: w => c a + cost c w

def run (step : A → X → X) : List A → X → X
  | [], x => x
  | a :: w, x => run step w (step a x)

def Indist (step : A → X → X) (c : A → Nat)
    (probe : P → X → O) (b : Nat) (x y : X) : Prop :=
  ∀ p w, cost c w ≤ b → probe p (run step w x) = probe p (run step w y)

def family (step : A → X → X) (c : A → Nat)
    (probe : P → X → O) (b : Nat) : ProbeFamily X where
  I := {w : List A // cost c w ≤ b} × P
  O := fun _ ↦ O
  f := fun i x ↦ probe i.2 (run step i.1.val x)

theorem indist_iff_family (step : A → X → X) (c : A → Nat)
    (probe : P → X → O) (b : Nat) (x y : X) :
    Indist step c probe b x y ↔ indist (family step c probe b) x y := by
  constructor
  · intro h ⟨⟨w, hw⟩, p⟩
    exact h p w hw
  · intro h p w hw
    exact h (⟨w, hw⟩, p)

theorem residual (step : A → X → X) (c : A → Nat)
    (probe : P → X → O) {a : A} {b : Nat} {x y : X}
    (ha : c a ≤ b) (hxy : Indist step c probe b x y) :
    Indist step c probe (b - c a) (step a x) (step a y) := by
  intro p w hw
  have hadmit : cost c (a :: w) ≤ b := by
    change c a + cost c w ≤ b
    omega
  exact hxy p (a :: w) hadmit

theorem budget_mono (step : A → X → X) (c : A → Nat)
    (probe : P → X → O) {b₁ b₂ : Nat} {x y : X}
    (hb : b₁ ≤ b₂) (hxy : Indist step c probe b₂ x y) :
    Indist step c probe b₁ x y := by
  intro p w hw
  exact hxy p w (Nat.le_trans hw hb)

theorem present (step : A → X → X) (c : A → Nat)
    (probe : P → X → O) {b : Nat} {x y : X}
    (hxy : Indist step c probe b x y) (p : P) : probe p x = probe p y :=
  hxy p [] (Nat.zero_le b)

/-- Exact one-step recurrence. Positivity is needed to compute it by ascending
budget, not for this logical equivalence. -/
theorem one_step_iff (step : A → X → X) (c : A → Nat)
    (probe : P → X → O) (b : Nat) (x y : X) :
    Indist step c probe b x y ↔
      (∀ p, probe p x = probe p y) ∧
      ∀ a, c a ≤ b → Indist step c probe (b - c a) (step a x) (step a y) := by
  constructor
  · intro h
    exact ⟨present step c probe h, fun a ha ↦ residual step c probe ha h⟩
  · intro ⟨hnow, hnext⟩ p w hw
    cases w with
    | nil => exact hnow p
    | cons a w =>
      have ha : c a ≤ b := by change c a + cost c w ≤ b at hw; omega
      have hr : cost c w ≤ b - c a := by
        change c a + cost c w ≤ b at hw
        omega
      exact hnext a ha p w hr

theorem positive_cost_residual_lt (c : A → Nat) (hpos : ∀ a, 0 < c a)
    {a : A} {b : Nat} (ha : c a ≤ b) : b - c a < b := by
  have := hpos a
  omega

theorem cost_append (c : A → Nat) (u v : List A) :
    cost c (u ++ v) = cost c u + cost c v := by
  induction u with
  | nil => simp [cost]
  | cons a u ih => simp [cost, ih, Nat.add_assoc]

theorem run_append (step : A → X → X) (u v : List A) (x : X) :
    run step (u ++ v) x = run step v (run step u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => exact ih (step a x)

end MonadFormal.Budget
