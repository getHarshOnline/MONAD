import MonadFormal.Sandbox

/-!
# Continuation monotonicity

Paper companion: `paper/MonadFormal/Monotonicity.tex`.

Encoding note. A larger family is the sum of the base family and an
extra family. This encodes the inclusion of families without dependent
rewriting.
-/

namespace MonadFormal

variable {X : Type}

/-- The extension of a probe family by an extra family. -/
def ProbeFamily.extend (F G : ProbeFamily X) : ProbeFamily X where
  I := F.I ⊕ G.I
  O := fun i ↦
    match i with
    | .inl a => F.O a
    | .inr b => G.O b
  f := fun i ↦
    match i with
    | .inl a => F.f a
    | .inr b => G.f b

/-- Indistinguishability under the larger family
implies indistinguishability under the base family. A larger
continuation family can only preserve or refine the relation. -/
theorem indist_mono {F G : ProbeFamily X} {x y : X}
    (h : indist (F.extend G) x y) : indist F x y :=
  fun i ↦ h (.inl i)

end MonadFormal
