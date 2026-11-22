import MonadFormal.Repair
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Minimum-cost repair and productive queries

The value is the least feasible worst-case budget, with infinity for
impossibility. It is not an analyst-side refinement or an expected cost.
Only queries splitting the current compatible set need to be considered.

Paper companion: `paper/MonadFormal/Repair/Optimal.tex`.
-/

namespace MonadFormal.Repair

variable {X J O V : Type}

def worstCost [Fintype O] (w : J → Nat) : Tree J O V → Nat
  | .answer _ => 0
  | .query j next => w j + Finset.univ.sup (fun o ↦ worstCost w (next o))

theorem within_iff_worstCost_le [Fintype O] (w : J → Nat)
    (t : Tree J O V) (b : Nat) : Within w t b ↔ worstCost w t ≤ b := by
  induction t generalizing b with
  | answer v => simp [Within, worstCost]
  | query j next ih =>
    constructor
    · intro h
      have hs : Finset.univ.sup (fun o ↦ worstCost w (next o)) ≤ b - w j :=
        Finset.sup_le_iff.mpr (fun o _ ↦ (ih o (b - w j)).mp (h.2 o))
      change w j + Finset.univ.sup (fun o ↦ worstCost w (next o)) ≤ b
      have hw := h.1
      omega
    · intro h
      change w j + Finset.univ.sup (fun o ↦ worstCost w (next o)) ≤ b at h
      refine ⟨by omega, fun o ↦ (ih o (b - w j)).mpr ?_⟩
      have ho := Finset.le_sup (f := fun o ↦ worstCost w (next o))
        (Finset.mem_univ o)
      omega

theorem within_mono (w : J → Nat) (t : Tree J O V) {a b : Nat}
    (hab : a ≤ b) (h : Within w t a) : Within w t b := by
  induction t generalizing a b with
  | answer v => trivial
  | query j next ih =>
    exact ⟨h.1.trans hab, fun o ↦ ih o (Nat.sub_le_sub_right hab (w j)) (h.2 o)⟩

theorem feasible_mono (m : J → X → O) (w : J → Nat) (target : X → V)
    (S : X → Prop) {a b : Nat} (hab : a ≤ b)
    (h : Feasible m w target S a) : Feasible m w target S b := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, within_mono w t hab ht, hc⟩

def Splits (m : J → X → O) (S : X → Prop) (j : J) : Prop :=
  ∃ x y, S x ∧ S y ∧ m j x ≠ m j y

/-- Remove nonsplitting roots until the first productive query. The induction
is on the original well-founded tree, not on a possibly zero query cost. -/
theorem feasible_split_iff [Nonempty V] (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop) (b : Nat)
    (hn : ¬ ∃ v, ∀ x, S x → target x = v) :
    Feasible m w target S b ↔
      ∃ j, Splits m S j ∧ w j ≤ b ∧
        ∀ o, Feasible m w target (branch S m j o) (b - w j) := by
  classical
  constructor
  · rintro ⟨t, hb, hc⟩
    induction t generalizing b with
    | answer v => exact (hn ⟨v, fun x hx ↦ (hc x hx).symm⟩).elim
    | query j next ih =>
      by_cases hs : Splits m S j
      · exact ⟨j, hs, hb.1, fun o ↦
          ⟨next o, hb.2 o, (correct_query_iff m target S j next).mp hc o⟩⟩
      · have hex : ∃ x, S x := by
          by_contra h
          exact hn ⟨Classical.choice inferInstance, fun x hx ↦ (h ⟨x, hx⟩).elim⟩
        obtain ⟨x₀, hx₀⟩ := hex
        have he : ∀ x, S x → m j x = m j x₀ := by
          intro x hx
          by_contra h
          exact hs ⟨x, x₀, hx, hx₀, h⟩
        have hc' : Correct m target S (next (m j x₀)) := by
          intro x hx
          have h := hc x hx
          change evaluate m (next (m j x)) x = target x at h
          simpa [he x hx] using h
        exact ih (m j x₀) b
          (within_mono w _ (Nat.sub_le b (w j)) (hb.2 (m j x₀))) hc'
  · rintro ⟨j, _, hj, hc⟩
    exact (feasible_iff m w target S b).mpr (Or.inr ⟨j, hj, hc⟩)

/-- The least feasible budget. An empty feasible-budget set has value infinity. -/
noncomputable def optimalCost (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop) : ℕ∞ :=
  ⨅ b : {b : Nat // Feasible m w target S b}, (b.val : ℕ∞)

theorem inf_le_nat_iff {I : Type} (f : I → ℕ∞) (b : Nat) :
    (⨅ i, f i) ≤ (b : ℕ∞) ↔ ∃ i, f i ≤ (b : ℕ∞) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    obtain ⟨i, hi⟩ := ENat.exists_eq_iInf f
    constructor
    · intro hb
      exact ⟨i, hi ▸ hb⟩
    · rintro ⟨j, hj⟩
      exact (iInf_le f j).trans hj

theorem optimalCost_le_iff (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop) (b : Nat) :
    optimalCost m w target S ≤ (b : ℕ∞) ↔ Feasible m w target S b := by
  rw [optimalCost, inf_le_nat_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, hab⟩
    exact feasible_mono m w target S (ENat.natCast_le_natCast.mp hab) ha
  · intro hb
    exact ⟨⟨b, hb⟩, le_rfl⟩

theorem optimalCost_attained (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop)
    (h : optimalCost m w target S ≠ ⊤) :
    ∃ b : Nat, optimalCost m w target S = (b : ℕ∞) ∧ Feasible m w target S b := by
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp h
  exact ⟨b, hb.symm, (optimalCost_le_iff m w target S b).mp hb.symm.le⟩

theorem optimal_tree [Fintype O] (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop)
    (h : optimalCost m w target S ≠ ⊤) :
    ∃ t, Correct m target S t ∧
      (worstCost w t : ℕ∞) = optimalCost m w target S := by
  obtain ⟨b, hb, t, ht, hc⟩ := optimalCost_attained m w target S h
  refine ⟨t, hc, le_antisymm ?_ ?_⟩
  · rw [hb]
    exact ENat.natCast_le_natCast.mpr ((within_iff_worstCost_le w t b).mp ht)
  · exact (optimalCost_le_iff m w target S (worstCost w t)).mpr
      ⟨t, (within_iff_worstCost_le w t _).mpr le_rfl, hc⟩

theorem optimalCost_eq_top_iff (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop) :
    optimalCost m w target S = ⊤ ↔ ¬ ∃ b, Feasible m w target S b := by
  constructor
  · intro ht ⟨b, hb⟩
    have h := (optimalCost_le_iff m w target S b).mpr hb
    simp [ht] at h
  · intro hn
    by_contra h
    obtain ⟨b, _, hb⟩ := optimalCost_attained m w target S h
    exact hn ⟨b, hb⟩

theorem nat_add_le_nat_iff (a b : Nat) (c : ℕ∞) :
    (a : ℕ∞) + c ≤ (b : ℕ∞) ↔ a ≤ b ∧ c ≤ ((b - a : Nat) : ℕ∞) := by
  cases c with
  | top => simp
  | coe c =>
    norm_cast
    omega

theorem eq_of_same_nat_bounds {a b : ℕ∞}
    (h : ∀ n : Nat, a ≤ (n : ℕ∞) ↔ b ≤ (n : ℕ∞)) : a = b := by
  apply le_antisymm
  · cases b with
    | top => exact le_top
    | coe n => exact (h n).mpr le_rfl
  · cases a with
    | top => exact le_top
    | coe n => exact (h n).mp le_rfl

/-- Exact Bellman value. The infimum of an empty query set is infinity.
No positive-cost assumption is needed: pruning, not spending, supplies progress. -/
theorem optimalCost_bellman [Nonempty V] (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop)
    (hn : ¬ ∃ v, ∀ x, S x → target x = v) :
    optimalCost m w target S =
      ⨅ j : {j : J // Splits m S j},
        (w j.val : ℕ∞) + ⨆ o, optimalCost m w target (branch S m j.val o) := by
  apply eq_of_same_nat_bounds
  intro b
  rw [optimalCost_le_iff, feasible_split_iff m w target S b hn, inf_le_nat_iff]
  simp_rw [nat_add_le_nat_iff, iSup_le_iff, optimalCost_le_iff]
  constructor
  · rintro ⟨j, hs, hj, hc⟩
    exact ⟨⟨j, hs⟩, hj, hc⟩
  · rintro ⟨⟨j, hs⟩, hj, hc⟩
    exact ⟨j, hs, hj, hc⟩

theorem optimalCost_constant (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : X → Prop)
    (h : ∃ v, ∀ x, S x → target x = v) : optimalCost m w target S = 0 := by
  apply le_antisymm _ bot_le
  exact (optimalCost_le_iff m w target S 0).mpr
    ((feasible_iff m w target S 0).mpr (Or.inl h))

theorem optimalCost_empty [Nonempty V] (m : J → X → O) (w : J → Nat)
    (target : X → V) : optimalCost m w target (fun _ ↦ False) = 0 := by
  exact optimalCost_constant m w target _
    ⟨Classical.choice inferInstance, fun _ h ↦ h.elim⟩

theorem constant_iff_pairwise [Nonempty V] (target : X → V) (S : X → Prop) :
    (∃ v, ∀ x, S x → target x = v) ↔
      ∀ x y, S x → S y → target x = target y := by
  classical
  constructor
  · rintro ⟨v, hv⟩ x y hx hy
    exact (hv x hx).trans (hv y hy).symm
  · intro h
    by_cases hn : ∃ x, S x
    · obtain ⟨x, hx⟩ := hn
      exact ⟨target x, fun y hy ↦ h y x hy hx⟩
    · exact ⟨Classical.choice inferInstance, fun x hx ↦ (hn ⟨x, hx⟩).elim⟩

theorem split_branch_card_lt [DecidableEq O] (m : J → X → O)
    (S : Finset X) {j : J} (hs : Splits m (fun x ↦ x ∈ S) j) (o : O) :
    (S.filter (fun x ↦ m j x = o)).card < S.card := by
  apply Finset.card_lt_card
  apply Finset.filter_ssubset.mpr
  obtain ⟨x, y, hx, hy, hne⟩ := hs
  by_cases ho : m j x = o
  · exact ⟨y, hy, fun he ↦ hne (ho.trans he.symm)⟩
  · exact ⟨x, hx, ho⟩

/-- A cardinality-founded recursive specification. With finite query and
outcome sets its infimum and supremum are finite min/max operations. This
definition does not claim an extracted, optimized executable solver. -/
noncomputable def finiteCost [DecidableEq O] (m : J → X → O) (w : J → Nat)
    (target : X → V) (S : Finset X) : ℕ∞ := by
  classical
  exact if ∃ v, ∀ x, x ∈ S → target x = v then 0 else
    ⨅ j : {j : J // Splits m (fun x ↦ x ∈ S) j},
      (w j.val : ℕ∞) + ⨆ o,
        finiteCost m w target (S.filter (fun x ↦ m j.val x = o))
termination_by S.card
decreasing_by exact split_branch_card_lt m S j.property o

theorem finiteCost_eq_optimal [Nonempty V] [DecidableEq O]
    (m : J → X → O) (w : J → Nat) (target : X → V) (S : Finset X) :
    finiteCost m w target S = optimalCost m w target (fun x ↦ x ∈ S) := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    rw [finiteCost]
    split_ifs with hc
    · exact (optimalCost_constant m w target (fun x ↦ x ∈ S) hc).symm
    · rw [optimalCost_bellman m w target (fun x ↦ x ∈ S) hc]
      apply iInf_congr
      intro j
      congr 1
      apply iSup_congr
      intro o
      rw [ih _ (hn ▸ split_branch_card_lt m S j.property o) _ rfl]
      congr 1
      funext x
      exact propext (Finset.mem_filter)

end MonadFormal.Repair
