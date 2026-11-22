/-!
# A finite influence model without transitivity

Detectable intervention influence in a finite deterministic
sub-profile. Paper companion: `paper/MonadFormal/Influence.tex`.

Encoding note. The record path in the worked model is deterministic
and noiseless, and one trial suffices, so a detectable change is an
inequality of records at the preparation. Every event is recordable
in this sub-profile, so the reliable-record requirement is automatic
and the influence definition keeps only the intervention pair.
-/

namespace MonadFormal

/-- An event: a Boolean predicate on the carrier. -/
abbrev Event (X : Type) := X → Bool

/-- A finite deterministic sub-profile: the allowed operations and
the preparation state. Coarse-graining and the record channel are the
identity, so records are states. -/
structure Profile (X : Type) where
  allowed : (X → X) → Prop
  prep : X

variable {X : Type}

/-- `U` is an admissible intervention on `A` at value `a`: an allowed
operation that sets `A` to `a` on every state. -/
def Interv (P : Profile X) (A : Event X) (a : Bool) (U : X → X) : Prop :=
  P.allowed U ∧ ∀ x, A (U x) = a

/-- Detectable intervention influence: some admissible intervention
pair on `A` changes the record of `B` at the preparation. -/
def Influences (P : Profile X) (A B : Event X) : Prop :=
  ∃ U₁ U₀, Interv P A true U₁ ∧ Interv P A false U₀ ∧
    B (U₁ P.prep) ≠ B (U₀ P.prep)

/-- Protocol monotonicity, sandbox form. A profile that allows every
operation of a poorer one and keeps the preparation detects at least
the same influences. Paper: resource monotonicity from
protocol-class inclusion. -/
theorem influences_mono {X : Type} {P P' : Profile X}
    (hall : ∀ U, P.allowed U → P'.allowed U)
    (hprep : P'.prep = P.prep) {A B : Event X}
    (h : Influences P A B) : Influences P' A B := by
  obtain ⟨U₁, U₀, ⟨ha₁, hs₁⟩, ⟨ha₀, hs₀⟩, hne⟩ := h
  exact ⟨U₁, U₀, ⟨hall U₁ ha₁, hs₁⟩, ⟨hall U₀ ha₀, hs₀⟩,
    by rw [hprep]; exact hne⟩

/-! The three-bit worked model. States are `(a, b, c)`. -/

/-- The carrier of the worked model. -/
abbrev Bit3 := Bool × Bool × Bool

/-- The event reading the first bit. -/
def eventA : Event Bit3 := fun x ↦ x.1

/-- The event reading the second bit. -/
def eventB : Event Bit3 := fun x ↦ x.2.1

/-- The event reading the third bit. -/
def eventC : Event Bit3 := fun x ↦ x.2.2

/-- Intervene on `A`: the mechanism propagates `b = a` and
`c = a xor b = false`. -/
def intA (a : Bool) : Bit3 → Bit3 := fun _ ↦ (a, a, false)

/-- Intervene on `B` alone: `a` is kept and `c = a xor b`. -/
def intB (b : Bool) : Bit3 → Bit3 := fun x ↦ (x.1, b, x.1.xor b)

/-- The worked model: the identity and the four interventions are
allowed; the preparation is the zero state. -/
def model : Profile Bit3 where
  allowed U := U = id ∨ (∃ a, U = intA a) ∨ (∃ b, U = intB b)
  prep := (false, false, false)

/-- Influence of `A` on `B`: the pair `intA true`, `intA false` moves
the record of `B` from `true` to `false`. -/
theorem influences_A_B : Influences model eventA eventB :=
  ⟨intA true, intA false,
    ⟨Or.inr (Or.inl ⟨true, rfl⟩), fun _ ↦ rfl⟩,
    ⟨Or.inr (Or.inl ⟨false, rfl⟩), fun _ ↦ rfl⟩,
    Bool.noConfusion⟩

/-- Influence of `B` on `C`: the pair `intB true`, `intB false` moves
the record of `C` from `true` to `false`. -/
theorem influences_B_C : Influences model eventB eventC :=
  ⟨intB true, intB false,
    ⟨Or.inr (Or.inr ⟨true, rfl⟩), fun _ ↦ rfl⟩,
    ⟨Or.inr (Or.inr ⟨false, rfl⟩), fun _ ↦ rfl⟩,
    Bool.noConfusion⟩

/-- The only admissible interventions on `A` are the two `intA`
maps: the identity and the `intB` maps do not set `A` constantly. -/
theorem interv_A_eq {U : Bit3 → Bit3} {a : Bool}
    (h : Interv model eventA a U) : U = intA a := by
  obtain ⟨hall, hset⟩ := h
  obtain rfl | ⟨g, rfl⟩ | ⟨g, rfl⟩ := hall
  · have h₁ := hset (true, true, true)
    have h₀ := hset (false, false, false)
    rw [← h₁] at h₀
    exact Bool.noConfusion h₀
  · have hg := hset (false, false, false)
    rw [show g = a from hg]
  · have h₁ := hset (true, true, true)
    have h₀ := hset (false, false, false)
    rw [← h₁] at h₀
    exact Bool.noConfusion h₀

/-- Path cancellation: no admissible intervention pair on `A` changes
the record of `C`, so influence is not transitive in the model. -/
theorem not_influences_A_C : ¬ Influences model eventA eventC := by
  intro h
  obtain ⟨U₁, U₀, h₁, h₀, hne⟩ := h
  rw [interv_A_eq h₁, interv_A_eq h₀] at hne
  exact hne rfl

end MonadFormal
