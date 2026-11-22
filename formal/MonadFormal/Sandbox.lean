/-!
# The minimal exact distinction calculus

Carriers are types. Probes are functions. Families are index-typed.

Both present and continuation-sensitive observations quantify over a
family of functions out of the carrier. The present relation uses the
probe family. The continuation-sensitive relation uses the family of
continuation-probe composites. This file uses one structure for both.
The family instance selects the relation.

Paper companion: `paper/MonadFormal/Sandbox.tex`.
-/

namespace MonadFormal

/-- A family of probes on a carrier `X`.
`I` is the probe index. `O i` is the codomain of probe `i`. -/
structure ProbeFamily (X : Type) where
  I : Type
  O : I → Type
  f : (i : I) → X → O i

variable {X Y : Type}

/-- Indistinguishability under a probe family.
The selected family determines whether the relation compares present
observations or continuation-probe composites. -/
def indist (F : ProbeFamily X) (x y : X) : Prop :=
  ∀ i : F.I, F.f i x = F.f i y

/-- Indistinguishability is reflexive. With symmetry and transitivity
this makes `indist` an equivalence relation, which grounds the
quotient below. -/
theorem indist_refl (F : ProbeFamily X) (x : X) : indist F x x :=
  fun _ ↦ rfl

/-- Indistinguishability is symmetric. -/
theorem indist_symm {F : ProbeFamily X} {x y : X}
    (h : indist F x y) : indist F y x :=
  fun i ↦ (h i).symm

/-- Indistinguishability is transitive. -/
theorem indist_trans {F : ProbeFamily X} {x y z : X}
    (h₁ : indist F x y) (h₂ : indist F y z) : indist F x z :=
  fun i ↦ (h₁ i).trans (h₂ i)

/-- A function `f` factors through a compression `q`. -/
def Factors {O : Type} (f : X → O) (q : X → Y) : Prop :=
  ∃ g : Y → O, ∀ x, f x = g (q x)

/-- A compression `q` is sufficient for a family `F` when every probe
factors through `q`. -/
def Sufficient (F : ProbeFamily X) (q : X → Y) : Prop :=
  ∀ i : F.I, Factors (F.f i) q

/-- Any sufficient compression refines indistinguishability.
This is the coarsest-quotient direction: no
sufficient compression separates less than the quotient by `indist`. -/
theorem indist_of_sufficient {F : ProbeFamily X} {q : X → Y}
    (h : Sufficient F q) {x y : X} (hq : q x = q y) : indist F x y := by
  intro i
  obtain ⟨g, hg⟩ := h i
  rw [hg x, hg y, hq]

/-- The quotient of the carrier by indistinguishability. -/
def IndistQuot (F : ProbeFamily X) : Type :=
  Quot (indist F)

/-- The canonical map onto the quotient. -/
def toQuot (F : ProbeFamily X) : X → IndistQuot F :=
  Quot.mk (indist F)

/-- The canonical quotient map is sufficient.
Together with `indist_of_sufficient` this is the sandbox form of
coarsest-quotient result: the quotient by `indist` is a sufficient
compression. -/
theorem toQuot_sufficient (F : ProbeFamily X) :
    Sufficient F (toQuot F) := by
  intro i
  refine ⟨Quot.lift (F.f i) ?_, ?_⟩
  · intro x y h
    exact h i
  · intro x
    rfl

end MonadFormal
