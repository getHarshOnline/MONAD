import MonadFormal.Sandbox
import MonadFormal.Monotonicity
import MonadFormal.NoGo

/-!
# A finite witness for class splitting on an unchanged carrier

Paper companion: `paper/MonadFormal/Counterexample.tex`.
This is old-bit revelation, not evidence that a new degree of freedom arose.

The carrier is `Bool`. The base family is empty. The extension adds
the identity probe. The base relation identifies `true` and `false`.
The extended relation separates them. One equivalence class splits.
The constant compression is sufficient before the extension and not
sufficient after it.
-/

namespace MonadFormal

/-- The empty probe family on `Bool`. -/
def emptyFamily : ProbeFamily Bool where
  I := Empty
  O := fun i ↦ i.elim
  f := fun i ↦ i.elim

/-- The identity probe family on `Bool`. -/
def idFamily : ProbeFamily Bool where
  I := Unit
  O := fun _ ↦ Bool
  f := fun _ x ↦ x

/-- Under the empty family, `true` and `false` are indistinguishable. -/
theorem base_indist : indist emptyFamily true false :=
  fun i ↦ i.elim

/-- Under the extended family, `true` and `false` are distinguishable.
The class splits. -/
theorem extended_split :
    ¬ indist (emptyFamily.extend idFamily) true false := by
  intro h
  exact Bool.noConfusion (h (.inr ()))

/-- The constant compression to `Unit`. -/
def constCompression : Bool → Unit := fun _ ↦ ()

/-- The constant compression is sufficient for the empty family. -/
theorem const_sufficient_before : Sufficient emptyFamily constCompression :=
  fun i ↦ i.elim

/-- The constant compression is not sufficient after the extension.
The prior compression silently destroyed a distinction that the
extension requires. -/
theorem const_insufficient_after :
    ¬ Sufficient (emptyFamily.extend idFamily) constCompression := by
  intro h
  obtain ⟨g, hg⟩ := h (.inr ())
  have : true = false := by
    have h₁ := hg true
    have h₂ := hg false
    exact h₁.trans h₂.symm
  exact Bool.noConfusion this

/-- The identity family is jointly separating. -/
theorem idFamily_separating : JointlySeparating idFamily := by
  intro x y hne
  exact ⟨(), hne⟩

/-- The no-go result, instantiated. Any compression sufficient for the
identity family on `Bool` is injective. -/
theorem no_go_on_bool {Y : Type} (q : Bool → Y)
    (h : Sufficient idFamily q) : Function.Injective q :=
  no_go idFamily_separating h

end MonadFormal
