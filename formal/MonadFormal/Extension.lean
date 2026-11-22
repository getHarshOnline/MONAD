import MonadFormal.Defect

/-!
# Extension-stable compression

Paper companion: `paper/MonadFormal/Extension.tex`.

The closure observation types the openness postulate: an extension
whose pulled-back probes all factor through the old quotient cannot
split a class, so class splitting needs enlargement of the admitted
family, not another member of an already covered family. The
non-recovery obstruction separates detecting a loss from repairing
it. The fiber-constancy criterion is the elementary baseline for restricted
extension classes. Reuse of this baseline is a result, not a novelty deficit.
-/

namespace MonadFormal

variable {X X' Y Y' : Type}

/-- Closure observation. If every probe of the pulled-back family
factors through the quotient of the old family, then states the old
family identifies stay identified by the pulled-back family. An
extension covered by the old closure cannot split a class. -/
theorem indist_pullback_of_factors {F : ProbeFamily X}
    {F' : ProbeFamily X'} {e : X → X'}
    (hcov : ∀ i, Factors ((F'.pullback e).f i) (toQuot F))
    {x y : X} (h : indist F x y) : indist (F'.pullback e) x y := by
  intro i
  obtain ⟨g, hg⟩ := hcov i
  rw [hg x, hg y]
  exact congrArg g (Quot.sound h)

/-- Non-recovery obstruction. If a compression merges two states that
a later compression separates after the extension, then no map
recovers the later compression from the earlier one. Detecting a lost
distinction does not recover it; a repair must name where the missing
information comes from. -/
theorem no_recovery {q : X → Y} {q' : X' → Y'} {e : X → X'}
    {x y : X} (hq : q x = q y) (hsep : q' (e x) ≠ q' (e y)) :
    ¬ ∃ t : Y → Y', ∀ z, t (q z) = q' (e z) := by
  intro ⟨t, ht⟩
  exact hsep (by rw [← ht x, ← ht y, hq])

/-- For a surjective compression, a
probe factors through it exactly when the probe is constant on every
fiber. -/
theorem factors_iff_fiber_const {O : Type} {q : X → Y}
    (hq : Function.Surjective q) (f : X → O) :
    Factors f q ↔ ∀ x y, q x = q y → f x = f y := by
  constructor
  · intro ⟨g, hg⟩ x y hxy
    rw [hg x, hg y, hxy]
  · intro h
    refine ⟨fun b ↦ f (hq b).choose, fun x ↦ ?_⟩
    exact h x (hq (q x)).choose (hq (q x)).choose_spec.symm

end MonadFormal
