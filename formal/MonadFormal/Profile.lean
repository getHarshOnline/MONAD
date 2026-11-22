import MonadFormal.Sandbox

/-!
# Protocol-record correspondence

Paper companion: `paper/MonadFormal/Profile.tex`.
This module is the definitional interface, not a probability-model axiom.
The codomain O may be a type of distributions; its measurable/probability
structure belongs to the selected profile rather than to this exact calculus.
-/

namespace MonadFormal.Profile

variable {X Z K P O V : Type}

def recordFamily (protocol : K → X → Z) (record : P → Z → O) : ProbeFamily X where
  I := K × P
  O := fun _ ↦ O
  f := fun i x ↦ record i.2 (protocol i.1 x)

theorem record_equivalence (protocol : K → X → Z) (record : P → Z → O) (x y : X) :
    indist (recordFamily protocol record) x y ↔
      ∀ k p, record p (protocol k x) = record p (protocol k y) := by
  constructor
  · intro h k p
    exact h (k, p)
  · intro h i
    exact h i.1 i.2

/-- Postprocessing cannot distinguish equal record distributions. -/
theorem decision_rules_preserve_indist (protocol : K → X → Z)
    (record : P → Z → O) (decision : O → V) {x y : X}
    (h : indist (recordFamily protocol record) x y) (k : K) (p : P) :
    decision (record p (protocol k x)) = decision (record p (protocol k y)) :=
  congrArg decision (h (k, p))

end MonadFormal.Profile
