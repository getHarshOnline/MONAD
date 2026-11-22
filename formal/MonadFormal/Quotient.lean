import MonadFormal.Extension

/-!
# Exact observational quotients

The canonical quotient is sufficient and has the universal property of the
coarsest sufficient representation. The uniqueness statement is about
surjective, exact representations, not arbitrary codomains with unused values.
No finiteness, computational efficiency, or physical access is inferred.

Paper companion: `paper/MonadFormal/Quotient.tex`.
-/

namespace MonadFormal

variable {X Y Z : Type}

theorem toQuot_eq_iff (F : ProbeFamily X) (x y : X) :
    toQuot F x = toQuot F y ↔ indist F x y := by
  constructor
  · exact indist_of_sufficient (toQuot_sufficient F)
  · exact Quot.sound

theorem toQuot_surjective (F : ProbeFamily X) :
    Function.Surjective (toQuot F) := by
  intro z
  induction z using Quot.inductionOn with
  | h x => exact ⟨x, rfl⟩

/-- Fiber-constant functions descend uniquely through a surjection. -/
theorem unique_descent {O : Type} {q : X → Y}
    (hq : Function.Surjective q) (f : X → O)
    (hf : ∀ x y, q x = q y → f x = f y) :
    ∃ g : Y → O, (∀ x, f x = g (q x)) ∧
      ∀ h : Y → O, (∀ x, f x = h (q x)) → h = g := by
  obtain ⟨g, hg⟩ := (factors_iff_fiber_const hq f).mpr hf
  refine ⟨g, hg, ?_⟩
  intro h hh
  funext y
  obtain ⟨x, rfl⟩ := hq y
  exact (hh x).symm.trans (hg x)

/-- Every sufficient surjective representation determines the quotient,
and that comparison map is unique. This is semantic, not bit-cost minimality. -/
theorem quotient_universal (F : ProbeFamily X) (q : X → Y)
    (hq : Function.Surjective q) (hs : Sufficient F q) :
    ∃ g : Y → IndistQuot F, (∀ x, toQuot F x = g (q x)) ∧
      ∀ h : Y → IndistQuot F,
        (∀ x, toQuot F x = h (q x)) → h = g := by
  apply unique_descent hq
  intro x y hxy
  exact Quot.sound (indist_of_sufficient hs hxy)

/-- Surjective representations with the same fibers differ by a bijective
relabeling, expressed by explicit mutually inverse comparison maps. -/
theorem same_fibers_relabeling (q : X → Y) (r : X → Z)
    (hq : Function.Surjective q) (hr : Function.Surjective r)
    (hf : ∀ x y, q x = q y ↔ r x = r y) :
    ∃ g : Y → Z, ∃ h : Z → Y,
      (∀ x, g (q x) = r x) ∧ (∀ x, h (r x) = q x) ∧
      (∀ y, h (g y) = y) ∧ (∀ z, g (h z) = z) := by
  obtain ⟨g, hg⟩ := (factors_iff_fiber_const hq r).mpr
    (fun x y hxy ↦ (hf x y).mp hxy)
  obtain ⟨h, hh⟩ := (factors_iff_fiber_const hr q).mpr
    (fun x y hxy ↦ (hf x y).mpr hxy)
  refine ⟨g, h, fun x ↦ (hg x).symm, fun x ↦ (hh x).symm, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hq y
    rw [← hg x, ← hh x]
  · intro z
    obtain ⟨x, rfl⟩ := hr z
    rw [← hh x, ← hg x]

end MonadFormal
