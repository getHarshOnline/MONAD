import MonadFormal.Repair
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Exact supplements with retained side information

The encoder sees the original state; the decoder sees only its supplement
and the retained representation. This is an explicit information-access
assumption, not a recovery procedure from erased data.

Paper companion: `paper/MonadFormal/Repair/Supplement.tex`.
-/

namespace MonadFormal.Repair

variable {X Q R A : Type}

def HasSupplement (q : X → Q) (r : X → R) (A : Type) : Prop :=
  ∃ encode : X → A, ∃ decode : Q → A → R,
    ∀ x, decode (q x) (encode x) = r x

theorem supplement_relabel {B : Type} (q : X → Q) (r : X → R) (e : A ≃ B)
    (h : HasSupplement q r A) : HasSupplement q r B := by
  obtain ⟨encode, decode, hc⟩ := h
  exact ⟨fun x ↦ e (encode x), fun y b ↦ decode y (e.symm b),
    fun x ↦ by simpa using hc x⟩

def fiberTargets [Fintype X] [DecidableEq Q] [DecidableEq R]
    (q : X → Q) (r : X → R) (y : Q) : Finset R :=
  (Finset.univ.filter (fun x ↦ q x = y)).image r

theorem target_mem_fiber [Fintype X] [DecidableEq Q] [DecidableEq R]
    (q : X → Q) (r : X → R) (x : X) : r x ∈ fiberTargets q r (q x) := by
  exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

theorem supplement_lower_bound [Fintype X] [Fintype A]
    [DecidableEq Q] [DecidableEq R] (q : X → Q) (r : X → R)
    (h : HasSupplement q r A) (y : Q) :
    (fiberTargets q r y).card ≤ Fintype.card A := by
  classical
  obtain ⟨encode, decode, hc⟩ := h
  have hs : fiberTargets q r y ⊆ Finset.univ.image (decode y) := by
    intro v hv
    obtain ⟨x, hx, hrv⟩ := Finset.mem_image.mp hv
    have hq : q x = y := (Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr
      ⟨encode x, Finset.mem_univ _, by simpa [hq] using (hc x).trans hrv⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem supplement_upper_bound [Fintype X] [DecidableEq Q] [DecidableEq R]
    [Nonempty R] (q : X → Q) (r : X → R) (k : Nat)
    (hk : ∀ y, (fiberTargets q r y).card ≤ k) : HasSupplement q r (Fin k) := by
  classical
  let code (y : Q) : {v : R // v ∈ fiberTargets q r y} → Fin k :=
    fun v ↦ Fin.castLE (hk y) ((fiberTargets q r y).equivFin v)
  have hinj : ∀ y, Function.Injective (code y) := by
    intro y a b h
    apply (fiberTargets q r y).equivFin.injective
    apply Fin.ext
    exact congrArg (fun z : Fin k ↦ z.val) h
  let encode : X → Fin k := fun x ↦ code (q x) ⟨r x, target_mem_fiber q r x⟩
  let decode : Q → Fin k → R := fun y a ↦
    if h : ∃ v, code y v = a then h.choose.val else Classical.choice inferInstance
  refine ⟨encode, decode, fun x ↦ ?_⟩
  have hx : ∃ v, code (q x) v = encode x :=
    ⟨⟨r x, target_mem_fiber q r x⟩, rfl⟩
  simp only [decode, dite_eq_left hx]
  exact congrArg Subtype.val (hinj (q x) hx.choose_spec)

/-- Exact alphabet feasibility, including an empty latent carrier. -/
theorem supplement_iff [Fintype X] [DecidableEq Q] [DecidableEq R]
    [Nonempty R] (q : X → Q) (r : X → R) (k : Nat) :
    HasSupplement q r (Fin k) ↔ ∀ y, (fiberTargets q r y).card ≤ k := by
  constructor
  · intro h y
    simpa using supplement_lower_bound q r h y
  · exact supplement_upper_bound q r k

def supplementSize [Fintype X] [Fintype Q] [DecidableEq Q] [DecidableEq R]
    (q : X → Q) (r : X → R) : Nat :=
  Finset.univ.sup (fun y ↦ (fiberTargets q r y).card)

theorem supplementSize_le_iff [Fintype X] [Fintype Q]
    [DecidableEq Q] [DecidableEq R] [Nonempty R]
    (q : X → Q) (r : X → R) (k : Nat) :
    supplementSize q r ≤ k ↔ HasSupplement q r (Fin k) := by
  rw [supplement_iff, supplementSize, Finset.sup_le_iff]
  simp

theorem supplement_minimum [Fintype X] [Fintype Q]
    [DecidableEq Q] [DecidableEq R] [Nonempty R] (q : X → Q) (r : X → R) :
    HasSupplement q r (Fin (supplementSize q r)) ∧
      ∀ k, HasSupplement q r (Fin k) → supplementSize q r ≤ k := by
  exact ⟨(supplementSize_le_iff q r _).mp le_rfl,
    fun k h ↦ (supplementSize_le_iff q r k).mpr h⟩

/-- Fixed-length binary communication; Nat.clog also gives zero bits for an
empty carrier, where no ordinary real logarithm of the zero alphabet exists. -/
theorem supplement_bits_iff [Fintype X] [Fintype Q]
    [DecidableEq Q] [DecidableEq R] [Nonempty R]
    (q : X → Q) (r : X → R) (b : Nat) :
    HasSupplement q r (Fin (2 ^ b)) ↔ Nat.clog 2 (supplementSize q r) ≤ b := by
  rw [← supplementSize_le_iff, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]

theorem supplement_binary_iff [Fintype X] [Fintype Q]
    [DecidableEq Q] [DecidableEq R] [Nonempty R]
    (q : X → Q) (r : X → R) (b : Nat) :
    HasSupplement q r (Fin b → Bool) ↔ Nat.clog 2 (supplementSize q r) ≤ b := by
  let e : (Fin b → Bool) ≃ Fin (2 ^ b) := Fintype.equivFinOfCardEq (by simp)
  constructor
  · intro h
    exact (supplement_bits_iff q r b).mp (supplement_relabel q r e h)
  · intro h
    exact supplement_relabel q r e.symm ((supplement_bits_iff q r b).mpr h)

theorem supplement_minimum_bits [Fintype X] [Fintype Q]
    [DecidableEq Q] [DecidableEq R] [Nonempty R] (q : X → Q) (r : X → R) :
    HasSupplement q r (Fin (Nat.clog 2 (supplementSize q r)) → Bool) ∧
      ∀ b, HasSupplement q r (Fin b → Bool) → Nat.clog 2 (supplementSize q r) ≤ b := by
  exact ⟨(supplement_binary_iff q r _).mpr le_rfl,
    fun b h ↦ (supplement_binary_iff q r b).mp h⟩

theorem known_query_one_bit (n : Nat) (i : Fin n) :
    ∃ encode : (Fin n → Bool) → Bool, ∃ decode : Bool → Bool,
      ∀ x, decode (encode x) = x i := by
  exact ⟨fun x ↦ x i, id, fun _ ↦ rfl⟩

theorem all_queries_force_injective {n : Nat} (encode : (Fin n → Bool) → A)
    (decode : A → Fin n → Bool) (hc : ∀ x i, decode (encode x) i = x i) :
    Function.Injective encode := by
  intro x y he
  funext i
  exact (hc x i).symm.trans ((congrArg (fun a ↦ decode a i) he).trans (hc y i))

theorem all_queries_alphabet_bound [Fintype A] {n : Nat}
    (encode : (Fin n → Bool) → A) (decode : A → Fin n → Bool)
    (hc : ∀ x i, decode (encode x) i = x i) : 2 ^ n ≤ Fintype.card A := by
  simpa using Fintype.card_le_of_injective encode (all_queries_force_injective encode decode hc)

theorem all_queries_need_n_bits {n b : Nat}
    (encode : (Fin n → Bool) → (Fin b → Bool))
    (decode : (Fin b → Bool) → Fin n → Bool)
    (hc : ∀ x i, decode (encode x) i = x i) : n ≤ b := by
  have h : 2 ^ n ≤ 2 ^ b := by simpa using all_queries_alphabet_bound encode decode hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

theorem storing_n_bits_answers_all (n : Nat) :
    ∃ encode : (Fin n → Bool) → (Fin n → Bool),
      ∃ decode : (Fin n → Bool) → Fin n → Bool,
        ∀ x i, decode (encode x) i = x i := by
  exact ⟨id, id, fun _ _ ↦ rfl⟩

end MonadFormal.Repair
