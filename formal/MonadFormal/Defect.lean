import MonadFormal.Sandbox

/-!
# The extension defect and compression stability

Paper companion: `paper/MonadFormal/Defect.tex`.

Encoding note. An extension `e : C → C'` contributes the pulled-back
family with members `f' ∘ e` for the probes `f'` of the target family.
The defect collects the members that do not factor through the
compression.
-/

namespace MonadFormal

variable {X X' Y : Type}

/-- The pullback of a target family along an extension transport. -/
def ProbeFamily.pullback (F' : ProbeFamily X') (e : X → X') :
    ProbeFamily X where
  I := F'.I
  O := F'.O
  f := fun i ↦ F'.f i ∘ e

/-- Probe `i` is in the extension defect of `(e, q)` when its pullback
does not factor through `q`. -/
def InDefect (F' : ProbeFamily X') (e : X → X') (q : X → Y)
    (i : F'.I) : Prop :=
  ¬ Factors ((F'.pullback e).f i) q

/-- The defect is empty. -/
def DefectEmpty (F' : ProbeFamily X') (e : X → X') (q : X → Y) : Prop :=
  ∀ i : F'.I, ¬ InDefect F' e q i

/-- The defect of `(e, q)` is empty if and only if `q` remains
sufficient for the pulled-back family. This is a definitional baseline,
not a theorem about finding or obtaining an optimal repair. -/
theorem defectEmpty_iff_sufficient (F' : ProbeFamily X') (e : X → X')
    (q : X → Y) :
    DefectEmpty F' e q ↔ Sufficient (F'.pullback e) q := by
  constructor
  · intro h i
    exact Classical.byContradiction fun hn ↦ h i hn
  · intro h i hd
    exact hd (h i)

end MonadFormal
