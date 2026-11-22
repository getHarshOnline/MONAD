import MonadFormal.Sandbox

/-!
# The universal compression obstruction

Paper companion: `paper/MonadFormal/NoGo.tex`.

Encoding note. The statement quantifies over extensions followed by
probes. The sandbox absorbs each composite `p ∘ e_*` into one family
member. This is faithful: only the composites act on the carrier.
-/

namespace MonadFormal

variable {X Y : Type}

/-- A family is jointly separating when it separates every pair of
distinct points. -/
def JointlySeparating (F : ProbeFamily X) : Prop :=
  ∀ x y : X, x ≠ y → ∃ i : F.I, F.f i x ≠ F.f i y

/-- The no-go result. If the family is jointly separating and the
compression is sufficient for it, then the compression is injective.
Unrestricted openness plus perfect future-safe compression gives no
nontrivial compression. -/
theorem no_go {F : ProbeFamily X} {q : X → Y}
    (hsep : JointlySeparating F) (hsuf : Sufficient F q) :
    Function.Injective q := by
  intro x y hq
  refine Classical.byContradiction fun hne ↦ ?_
  obtain ⟨i, hi⟩ := hsep x y hne
  exact hi (indist_of_sufficient hsuf hq i)

end MonadFormal
