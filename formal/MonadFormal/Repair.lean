import MonadFormal.Refinement
import Std

/-!
# Obtainable repair by an adaptive measurement tree

Measurements are exact, nondestructive reads of an available source. A branch
depends only on the observed value. Budget is a worst-case bound, not an
expected cost. Semantic refinement alone supplies no measurement interface.

Paper companion: `paper/MonadFormal/Repair.tex`.
-/

namespace MonadFormal.Repair

inductive Tree (J O V : Type) where
  | answer : V → Tree J O V
  | query : J → (O → Tree J O V) → Tree J O V

variable {X J O V : Type}

def evaluate (m : J → X → O) : Tree J O V → X → V
  | .answer v, _ => v
  | .query j next, x => evaluate m (next (m j x)) x

def Within (w : J → Nat) : Tree J O V → Nat → Prop
  | .answer _, _ => True
  | .query j next, b => w j ≤ b ∧ ∀ o, Within w (next o) (b - w j)

def Correct (m : J → X → O) (target : X → V) (S : X → Prop)
    (t : Tree J O V) : Prop := ∀ x, S x → evaluate m t x = target x

def Feasible (m : J → X → O) (w : J → Nat) (target : X → V)
    (S : X → Prop) (b : Nat) : Prop :=
  ∃ t, Within w t b ∧ Correct m target S t

/-- The state compatible with a query result is a fiber intersection. -/
def branch (S : X → Prop) (m : J → X → O) (j : J) (o : O) : X → Prop :=
  fun x ↦ S x ∧ m j x = o

theorem correct_query_iff (m : J → X → O) (target : X → V)
    (S : X → Prop) (j : J) (next : O → Tree J O V) :
    Correct m target S (.query j next) ↔
      ∀ o, Correct m target (branch S m j o) (next o) := by
  constructor
  · intro h o x ⟨hx, ho⟩
    have he := h x hx
    change evaluate m (next (m j x)) x = target x at he
    simpa [ho] using he
  · intro h x hx
    exact h (m j x) x ⟨hx, rfl⟩

/-- Exact decision-tree feasibility recurrence. `Repair.Optimal` supplies
minimum-cost attainment and cardinality-founded recursion after pruning
nonsplitting queries. Feasibility alone does not establish termination. -/
theorem feasible_iff (m : J → X → O) (w : J → Nat) (target : X → V)
    (S : X → Prop) (b : Nat) :
    Feasible m w target S b ↔
      (∃ v, ∀ x, S x → target x = v) ∨
      ∃ j, w j ≤ b ∧ ∀ o, Feasible m w target (branch S m j o) (b - w j) := by
  constructor
  · intro ⟨t, hb, hc⟩
    cases t with
    | answer v => exact Or.inl ⟨v, fun x hx ↦ (hc x hx).symm⟩
    | query j next =>
      exact Or.inr ⟨j, hb.1, fun o ↦
        ⟨next o, hb.2 o, (correct_query_iff m target S j next).mp hc o⟩⟩
  · intro h
    rcases h with ⟨v, hv⟩ | ⟨j, hj, hn⟩
    · exact ⟨.answer v, True.intro, fun x hx ↦ (hv x hx).symm⟩
    · classical
      let next := fun o ↦ (hn o).choose
      refine ⟨.query j next, ⟨hj, fun o ↦ (hn o).choose_spec.1⟩, ?_⟩
      exact (correct_query_iff m target S j next).mpr
        (fun o ↦ (hn o).choose_spec.2)

/-- An adaptive tree cannot distinguish states that every available
measurement identifies. This includes adaptive choice of the next query. -/
theorem indistinguishable_evaluation (m : J → X → O) (t : Tree J O V)
    {x y : X} (h : ∀ j, m j x = m j y) : evaluate m t x = evaluate m t y := by
  induction t with
  | answer v => rfl
  | query j next ih =>
    change evaluate m (next (m j x)) x = evaluate m (next (m j y)) y
    rw [h j]
    exact ih (m j y)

theorem no_repair_from_identical_measurements (m : J → X → O)
    (target : X → V) (S : X → Prop) {x y : X}
    (hx : S x) (hy : S y) (hm : ∀ j, m j x = m j y)
    (ht : target x ≠ target y) : ¬ ∃ t, Correct m target S t := by
  intro ⟨t, h⟩
  exact ht ((h x hx).symm.trans ((indistinguishable_evaluation m t hm).trans (h y hy)))

/-- Positive-cost queries cannot occur in a zero-budget tree. -/
theorem zero_budget_iff_constant (m : J → X → O) (w : J → Nat)
    (hpos : ∀ j, 0 < w j) (target : X → V) (S : X → Prop) :
    (∃ t, Within w t 0 ∧ Correct m target S t) ↔
      ∃ v, ∀ x, S x → target x = v := by
  constructor
  · intro ⟨t, hb, ht⟩
    cases t with
    | answer v => exact ⟨v, fun x hx ↦ (ht x hx).symm⟩
    | query j next =>
      have hle : w j ≤ 0 := hb.1
      have hlt := hpos j
      omega
  · intro ⟨v, h⟩
    exact ⟨.answer v, True.intro, fun x hx ↦ (h x hx).symm⟩

/-- With free queries, only the free-query information constrains zero-cost
repair. Positive-cost observations cannot be used at budget zero. -/
theorem zero_budget_respects_free_fibers (m : J → X → O) (w : J → Nat)
    (t : Tree J O V) (hb : Within w t 0) {x y : X}
    (hf : ∀ j, w j = 0 → m j x = m j y) :
    evaluate m t x = evaluate m t y := by
  induction t with
  | answer v => rfl
  | query j next ih =>
    have hz : w j = 0 := Nat.eq_zero_of_le_zero hb.1
    change evaluate m (next (m j x)) x = evaluate m (next (m j y)) y
    rw [hf j hz]
    exact ih (m j y) (by simpa [hz] using hb.2 (m j y))

def freeBitTree : Tree Unit Bool Bool := .query () (fun b ↦ .answer b)

theorem free_bit_costs_zero : Within (fun _ : Unit ↦ 0) freeBitTree 0 := by
  exact ⟨Nat.le_refl 0, fun _ ↦ True.intro⟩

theorem free_bit_recovers :
    Correct (fun _ : Unit ↦ id) id (fun _ : Bool ↦ True) freeBitTree := by
  intro x _
  rfl

theorem free_bit_not_in_constant_storage :
    ¬ Factors (id : Bool → Bool) (fun _ : Bool ↦ ()) := by
  intro ⟨g, h⟩
  have : true = false := (h true).trans (h false).symm
  exact Bool.noConfusion this

end MonadFormal.Repair
