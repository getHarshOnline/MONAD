import MonadFormal.Quotient

/-!
# Semantic refinement and accessible information

Pairing retained and newly requested values is the least semantic refinement.
It does not manufacture the newly requested value. Recovery is a factorization
through the actually accessible information. The final example distinguishes
pullback adequacy on old states from distinctions outside the embedded carrier.

Paper companion: `paper/MonadFormal/Refinement.tex`.
-/

namespace MonadFormal

variable {X Y Z W : Type}

theorem factors_trans {f : X → W} {q : X → Y} {r : X → Z}
    (hf : Factors f q) (hq : Factors q r) : Factors f r := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨h, hh⟩ := hq
  exact ⟨g ∘ h, fun x ↦ by rw [hg x, hh x]; rfl⟩

def refine (q : X → Y) (r : X → Z) : X → Y × Z := fun x ↦ (q x, r x)

theorem refine_fibers (q : X → Y) (r : X → Z) (x y : X) :
    refine q r x = refine q r y ↔ q x = q y ∧ r x = r y := by
  simp [refine]

theorem refine_preserves (q : X → Y) (r : X → Z) :
    Factors q (refine q r) ∧ Factors r (refine q r) :=
  ⟨⟨Prod.fst, fun _ ↦ rfl⟩, ⟨Prod.snd, fun _ ↦ rfl⟩⟩

/-- Least refinement is ordered by factorization, not by allocation size. -/
theorem refine_least (q : X → Y) (r : X → Z) (s : X → W)
    (hq : Factors q s) (hr : Factors r s) : Factors (refine q r) s := by
  obtain ⟨g, hg⟩ := hq
  obtain ⟨h, hh⟩ := hr
  exact ⟨fun z ↦ (g z, h z), fun x ↦ by
    change (q x, r x) = (g (s x), h (s x))
    rw [hg x, hh x]⟩

/-- A required refinement is obtainable exactly when its two components are
obtainable from the declared accessible information. -/
theorem refine_obtainable_iff (q : X → Y) (r : X → Z) (available : X → W) :
    Factors (refine q r) available ↔
      Factors q available ∧ Factors r available := by
  constructor
  · intro h
    exact ⟨factors_trans (refine_preserves q r).1 h,
      factors_trans (refine_preserves q r).2 h⟩
  · intro h
    exact refine_least q r available h.1 h.2

/-- Later processing of retained information cannot split a retained fiber. -/
theorem processing_preserves_fibers (available : X → Y) (process : Y → Z)
    {x y : X} (h : available x = available y) :
    process (available x) = process (available y) := congrArg process h

/-- An extra target bit is invisible on the embedded old carrier. -/
def carrierEmbedding : Unit → Unit × Bool := fun x ↦ (x, false)

theorem extra_bit_pullback_factors :
    Factors (Prod.snd ∘ carrierEmbedding) (fun _ : Unit ↦ ()) :=
  ⟨fun _ ↦ false, fun _ ↦ rfl⟩

theorem extra_bit_separates_new_states :
    (Prod.snd ((), false) : Bool) ≠ Prod.snd ((), true) := by decide

theorem extra_state_outside_image :
    ¬ ∃ x, carrierEmbedding x = ((), true) := by
  intro ⟨x, h⟩
  have : false = true := congrArg Prod.snd h
  exact Bool.noConfusion this

end MonadFormal
