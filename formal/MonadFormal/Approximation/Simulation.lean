import MonadFormal.Approximation

/-!
# Uniform simulation deficiency and decision transfer

Paper companion: `paper/MonadFormal/Approximation/Simulation.tex`.
The same simulator is used at every parameter. Infima need not be attained.
These are forward simulation bounds, not the converse randomization theorem,
and they do not identify simulation error with repair cost or causal transport.
-/

namespace MonadFormal.Approximation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ X Y Z A : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace A]

abbrev Experiment (Θ X : Type*) [MeasurableSpace X] := Θ → ProbabilityMeasure X

/-- The parameter is outside the choice of randomization: one common kernel. -/
noncomputable def simulationError (K : Randomization X Y)
    (E : Experiment Θ X) (F : Experiment Θ Y) : ℝ≥0∞ :=
  ⨆ θ, tv (K.apply (E θ)) (F θ)

/-- Directed Markov-kernel deficiency, not a symmetric distance by definition. -/
noncomputable def deficiency (E : Experiment Θ X) (F : Experiment Θ Y) : ℝ≥0∞ :=
  ⨅ K : Randomization X Y, simulationError K E F

theorem simulationError_le_one (K : Randomization X Y)
    (E : Experiment Θ X) (F : Experiment Θ Y) : simulationError K E F ≤ 1 :=
  iSup_le fun θ ↦ tv_le_one (K.apply (E θ)) (F θ)

theorem pointwise_le_simulationError (K : Randomization X Y)
    (E : Experiment Θ X) (F : Experiment Θ Y) (θ : Θ) :
    tv (K.apply (E θ)) (F θ) ≤ simulationError K E F :=
  le_iSup (fun θ ↦ tv (K.apply (E θ)) (F θ)) θ

theorem deficiency_le_simulationError (E : Experiment Θ X) (F : Experiment Θ Y)
    (K : Randomization X Y) : deficiency E F ≤ simulationError K E F :=
  iInf_le _ K

theorem deficiency_le_one [Nonempty Y] (E : Experiment Θ X) (F : Experiment Θ Y) :
    deficiency E F ≤ 1 := by
  classical
  let K : Randomization X Y := ⟨Kernel.const X (Measure.dirac (Classical.choice
    (inferInstance : Nonempty Y))), inferInstance⟩
  exact (deficiency_le_simulationError E F K).trans (simulationError_le_one K E F)

theorem deficiency_of_exact (E : Experiment Θ X) (F : Experiment Θ Y)
    (K : Randomization X Y) (h : ∀ θ, K.apply (E θ) = F θ) : deficiency E F = 0 := by
  apply le_antisymm _ zero_le
  refine (deficiency_le_simulationError E F K).trans ?_
  exact iSup_le fun θ ↦ by rw [h θ, tv_self]

theorem deficiency_self (E : Experiment Θ X) : deficiency E E = 0 := by
  apply deficiency_of_exact E E ⟨Kernel.id, inferInstance⟩
  intro θ
  apply Subtype.ext
  simp [Randomization.apply, Kernel.id, Measure.deterministic_comp_eq_map]

theorem simulationError_comp (E : Experiment Θ X) (F : Experiment Θ Y)
    (G : Experiment Θ Z) (K : Randomization X Y) (L : Randomization Y Z) :
    simulationError (L.comp K) E G ≤ simulationError K E F + simulationError L F G := by
  unfold simulationError
  refine iSup_le fun θ ↦ ?_
  rw [L.apply_comp K (E θ)]
  calc
    tv (L.apply (K.apply (E θ))) (G θ)
        ≤ tv (L.apply (K.apply (E θ))) (L.apply (F θ)) + tv (L.apply (F θ)) (G θ) :=
      tv_triangle _ _ _
    _ ≤ tv (K.apply (E θ)) (F θ) + tv (L.apply (F θ)) (G θ) :=
      add_le_add (tv_processing L (K.apply (E θ)) (F θ)) le_rfl
    _ ≤ simulationError K E F + simulationError L F G :=
      add_le_add (pointwise_le_simulationError K E F θ)
        (pointwise_le_simulationError L F G θ)

/-- Composition holds without assuming that either infimum has a minimizer. -/
theorem deficiency_triangle (E : Experiment Θ X) (F : Experiment Θ Y)
    (G : Experiment Θ Z) : deficiency E G ≤ deficiency E F + deficiency F G := by
  apply ENNReal.le_iInf_add_iInf
  intro K L
  exact (deficiency_le_simulationError E G (L.comp K)).trans
    (simulationError_comp E F G K L)

/-- Pointwise risk of a randomized decision procedure for a bounded loss. -/
noncomputable def risk (E : Experiment Θ X) (D : Randomization X A)
    (loss : Θ → Test A) (θ : Θ) : ℝ :=
  ∫ a, (loss θ).val a ∂D.apply (E θ)

/-- A common simulator transfers every bounded decision rule uniformly. -/
theorem risk_transfer (E : Experiment Θ X) (F : Experiment Θ Y)
    (K : Randomization X Y) (D : Randomization Y A) (loss : Θ → Test A) (θ : Θ) :
    ENNReal.ofReal |risk E (D.comp K) loss θ - risk F D loss θ| ≤
      simulationError K E F := by
  unfold risk
  rw [D.apply_comp K (E θ)]
  exact ((test_le_tv _ _ (loss θ)).trans (tv_processing D _ _)).trans
    (pointwise_le_simulationError K E F θ)

theorem risk_transfer_real (E : Experiment Θ X) (F : Experiment Θ Y)
    (K : Randomization X Y) (D : Randomization Y A) (loss : Θ → Test A)
    {ε : ℝ} (hε : 0 ≤ ε) (hK : simulationError K E F ≤ ENNReal.ofReal ε) (θ : Θ) :
    |risk E (D.comp K) loss θ - risk F D loss θ| ≤ ε := by
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp ((risk_transfer E F K D loss θ).trans hK)

/-- The quantifiers matter: K is chosen before the loss, decision rule and parameter. -/
theorem deficiency_risk_transfer (E : Experiment Θ X) (F : Experiment Θ Y)
    {τ : ℝ≥0∞} (h : deficiency E F < τ) :
    ∃ K : Randomization X Y, simulationError K E F < τ ∧
      ∀ (D : Randomization Y A) (loss : Θ → Test A) (θ : Θ),
        ENNReal.ofReal |risk E (D.comp K) loss θ - risk F D loss θ| < τ := by
  obtain ⟨K, hK⟩ := iInf_lt_iff.mp h
  exact ⟨K, hK, fun D loss θ ↦ (risk_transfer E F K D loss θ).trans_lt hK⟩

/-- A real-valued δ + ε statement, with no fictitious optimal kernel. -/
theorem deficiency_risk_transfer_epsilon [Nonempty Y]
    (E : Experiment Θ X) (F : Experiment Θ Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Randomization X Y, ∀ (D : Randomization Y A) (loss : Θ → Test A) (θ : Θ),
      |risk E (D.comp K) loss θ - risk F D loss θ| < (deficiency E F).toReal + ε := by
  have hfin : deficiency E F ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (deficiency_le_one E F)
  have hτ : deficiency E F < ENNReal.ofReal ((deficiency E F).toReal + ε) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr (lt_add_of_pos_right _ hε)
  obtain ⟨K, _, hK⟩ := deficiency_risk_transfer (A := A) E F hτ
  refine ⟨K, fun D loss θ ↦ ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp (hK D loss θ)

end MonadFormal.Approximation
