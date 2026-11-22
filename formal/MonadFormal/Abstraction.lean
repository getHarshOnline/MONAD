import MonadFormal.Quotient
import MonadFormal.Budget

/-!
# Partition abstraction and backward completeness

Sets are represented by predicates. `saturate q S` is the concretization of
the direct-image abstraction of `S`. The theorem proves the exact powerset
translation; it does not identify arbitrary abstract domains with partitions.

Paper companion: `paper/MonadFormal/Abstraction.tex`.
-/

namespace MonadFormal

variable {X Y Z : Type}

def saturate (q : X → Y) (S : X → Prop) (x : X) : Prop :=
  ∃ y, S y ∧ q y = q x

def abstractPost (r : X → Z) (step : X → X) (S : X → Prop) (z : Z) : Prop :=
  ∃ x, S x ∧ r (step x) = z

theorem backward_complete_iff (q : X → Y) (r : X → Z) (step : X → X) :
    (∀ S z, abstractPost r step S z ↔ abstractPost r step (saturate q S) z) ↔
      (∀ x y, q x = q y → r (step x) = r (step y)) := by
  constructor
  · intro h x y hxy
    have hsat : abstractPost r step (saturate q (fun u ↦ u = x)) (r (step y)) :=
      ⟨y, ⟨x, rfl, hxy⟩, rfl⟩
    obtain ⟨u, hu, heq⟩ := (h (fun u ↦ u = x) (r (step y))).mpr hsat
    cases hu
    exact heq
  · intro h S z
    constructor
    · intro ⟨x, hx, heq⟩
      exact ⟨x, ⟨x, hx, rfl⟩, heq⟩
    · intro ⟨x, ⟨y, hy, hxy⟩, heq⟩
      exact ⟨y, hy, (h y x hxy).trans heq⟩

/-- Budgeted continuation gives an exact backward-completeness instance with
different input and residual-output quotient domains. -/
theorem budget_backward_complete {A P O : Type}
    (step : A → X → X) (c : A → Nat) (probe : P → X → O)
    {a : A} {b : Nat} (ha : c a ≤ b) :
    ∀ S z,
      abstractPost (toQuot (Budget.family step c probe (b - c a))) (step a) S z ↔
      abstractPost (toQuot (Budget.family step c probe (b - c a))) (step a)
        (saturate (toQuot (Budget.family step c probe b)) S) z := by
  apply (backward_complete_iff _ _ _).mpr
  intro x y hxy
  apply (toQuot_eq_iff _ _ _).mpr
  apply (Budget.indist_iff_family _ _ _ _ _ _).mp
  apply Budget.residual step c probe ha
  apply (Budget.indist_iff_family _ _ _ _ _ _).mpr
  exact (toQuot_eq_iff _ _ _).mp hxy

end MonadFormal
