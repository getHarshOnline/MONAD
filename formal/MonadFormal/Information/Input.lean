import MonadFormal.Information.Likelihood
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Deterministic input coarse-graining

Paper companion: `paper/MonadFormal/Information/Input.tex`.
The information identity needs only measurability. Separate disintegration
results describe reconstruction of a law, not an operational decoder that
recovers the original microstate.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set
open Approximation
open scoped ENNReal

variable {X M Y : Type*} [MeasurableSpace X] [MeasurableSpace M] [MeasurableSpace Y]

/-- A disintegration reconstructs the joint law, not the original state pointwise. -/
theorem reconstruct_input_joint (K : Randomization M Y) (R : Randomization M X)
    (μ : ProbabilityMeasure X) (q : X → M) (hq : Measurable q)
    (hR : (μ.map q : Measure M) ⊗ₘ R.val =
      (μ : Measure X).map (fun x ↦ (q x, x))) :
    (R.val ×ₖ K.val) ∘ₘ (μ.map q : Measure M) =
      (μ : Measure X) ⊗ₘ (K.comap q hq).val := by
  apply Measure.ext_prod
  intro s t hs ht
  let F : M × X → ℝ≥0∞ := fun p ↦ s.indicator (fun _ ↦ 1) p.2 * K.val p.1 t
  have hF : Measurable F :=
    ((measurable_const.indicator hs).comp measurable_snd).mul
      ((K.val.measurable_coe ht).comp measurable_fst)
  have hi := congrArg (fun ν : Measure (M × X) ↦ ∫⁻ p, F p ∂ν) hR
  have hm : (∫⁻ p, F p ∂(μ : Measure X).map (fun x ↦ (q x, x))) =
      ∫⁻ x, F (q x, x) ∂(μ : Measure X) :=
    lintegral_map hF (by fun_prop)
  rw [Measure.lintegral_compProd hF, hm] at hi
  simp only [F, lintegral_mul_const _ (measurable_const.indicator hs),
    lintegral_indicator_const hs, one_mul] at hi
  rw [Measure.bind_apply (hs.prod ht) (Kernel.aemeasurable _),
    Measure.compProd_apply_prod hs ht]
  simp only [Kernel.prod_apply, Measure.prod_prod]
  simp only [Randomization.comap, Kernel.comap_apply]
  rw [← lintegral_indicator hs]
  apply hi.trans
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s <;> simp [hx]

/-- Conditional independence and deterministic coarse-graining give equality, not just a bound. -/
theorem channelInfo_comap_eq_of_disintegration (K : Randomization M Y)
    (R : Randomization M X) (μ : ProbabilityMeasure X) (q : X → M) (hq : Measurable q)
    (hR : (μ.map q : Measure M) ⊗ₘ R.val =
      (μ : Measure X).map (fun x ↦ (q x, x))) :
    channelInfo (K.comap q hq) μ = channelInfo K (μ.map q) := by
  apply le_antisymm
  · let Id : Randomization Y Y := ⟨Kernel.id, inferInstance⟩
    have he : (R.val ∥ₖ Kernel.id) ∘ₘ ((μ.map q : Measure M) ⊗ₘ K.val) =
        (μ : Measure X) ⊗ₘ (K.comap q hq).val := by
      rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc, Kernel.parallelComp_comp_prod,
        Kernel.comp_id, Kernel.id_comp]
      exact reconstruct_input_joint K R μ q hq hR
    simpa only [Id, he, channelInfo] using
      mutualInfo_parallel_le R Id ((μ.map q : Measure M) ⊗ₘ K.val)
  · have h := mutualInfo_map_le ((μ : Measure X) ⊗ₘ (K.comap q hq).val) hq measurable_id
    simpa only [map_input_joint, channelInfo] using h

/-- A standard Borel microstate space supplies the needed conditional kernel. -/
theorem exists_input_disintegration [StandardBorelSpace X]
    (μ : ProbabilityMeasure X) (q : X → M) (hq : Measurable q) :
    ∃ R : Randomization M X, (μ.map q : Measure M) ⊗ₘ R.val =
      (μ : Measure X).map (fun x ↦ (q x, x)) := by
  let : Nonempty X := μ.nonempty
  let ρ : Measure (M × X) := (μ : Measure X).map (fun x ↦ (q x, x))
  have hfst : ρ.fst = (μ.map q : Measure M) := by
    exact Measure.fst_map_prodMk hq measurable_id
  refine ⟨⟨ρ.condKernel, inferInstance⟩, ?_⟩
  rw [← hfst]
  exact ρ.disintegrate ρ.condKernel

/-- Deterministic input coarse-graining preserves information on arbitrary measurable spaces. -/
theorem channelInfo_comap_eq (K : Randomization M Y)
    (μ : ProbabilityMeasure X) (q : X → M) (hq : Measurable q) :
    channelInfo (K.comap q hq) μ = channelInfo K (μ.map q) := by
  have ho : (K.comap q hq).val ∘ₘ (μ : Measure X) = K.val ∘ₘ (μ.map q : Measure M) := by
    change K.val.comap q hq ∘ₘ (μ : Measure X) = _
    rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map]
    rfl
  let L : Randomization M Y := ⟨Kernel.const M (K.val ∘ₘ (μ.map q : Measure M)), inferInstance⟩
  have hl : (L.comap q hq).val = Kernel.const X (K.val ∘ₘ (μ.map q : Measure M)) := by
    ext x s hs
    rfl
  rw [channelInfo_eq, channelInfo_eq, ho]
  have h := klDiv_input_joint K L μ q hq
  rw [hl] at h
  simpa only [L, Measure.compProd_const] using h

/-- The composite capacity cannot exceed the capacity over all admitted macrostate laws. -/
theorem capacity_comap_le (K : Randomization M Y)
    (q : X → M) (hq : Measurable q) (A : Set (ProbabilityMeasure X))
    (B : Set (ProbabilityMeasure M)) (hAB : ∀ μ ∈ A, μ.map q ∈ B) :
    capacity (K.comap q hq) A ≤ capacity K B := by
  refine iSup₂_le fun μ hμ ↦ ?_
  rw [channelInfo_comap_eq]
  exact channelInfo_le_capacity K (hAB μ hμ)

/-- Realizability of every admitted macrostate input law suffices for equality. -/
theorem capacity_comap_eq (K : Randomization M Y)
    (q : X → M) (hq : Measurable q) (A : Set (ProbabilityMeasure X))
    (B : Set (ProbabilityMeasure M)) (hAB : ∀ μ ∈ A, μ.map q ∈ B)
    (hBA : ∀ ν ∈ B, ∃ μ ∈ A, μ.map q = ν) :
    capacity (K.comap q hq) A = capacity K B := by
  apply le_antisymm (capacity_comap_le K q hq A B hAB)
  refine iSup₂_le fun ν hν ↦ ?_
  obtain ⟨μ, hμ, rfl⟩ := hBA ν hν
  rw [← channelInfo_comap_eq K μ q hq]
  exact channelInfo_le_capacity _ hμ

/-- Expected macrostate cost pulls back exactly along a measurable coarse-graining. -/
theorem map_mem_costAdmissible (μ : ProbabilityMeasure X) (q : X → M) (hq : Measurable q)
    (c : M → ℝ≥0∞) (hc : Measurable c) (b : ℝ≥0∞) :
    μ.map q ∈ costAdmissible c b ↔ μ ∈ costAdmissible (c ∘ q) b := by
  change (∫⁻ m, c m ∂(μ : Measure X).map q) ≤ b ↔ _
  rw [lintegral_map hc hq]
  rfl

theorem capacity_cost_comap_le (K : Randomization M Y)
    (q : X → M) (hq : Measurable q) (c : M → ℝ≥0∞) (hc : Measurable c) (b : ℝ≥0∞) :
    capacity (K.comap q hq) (costAdmissible (c ∘ q) b) ≤ capacity K (costAdmissible c b) :=
  capacity_comap_le K q hq _ _ fun μ hμ ↦ (map_mem_costAdmissible μ q hq c hc b).mpr hμ

/-- A measurable section realizes every macrostate law without changing its pulled-back cost. -/
theorem cost_law_realizable_of_section (q : X → M) (hq : Measurable q)
    (s : M → X) (hs : Measurable s) (hqs : Function.RightInverse s q)
    (c : M → ℝ≥0∞) (hc : Measurable c) (b : ℝ≥0∞)
    (ν : ProbabilityMeasure M) (hν : ν ∈ costAdmissible c b) :
    ∃ μ ∈ costAdmissible (c ∘ q) b, μ.map q = ν := by
  have he : (ν.map s).map q = ν := by
    apply Subtype.ext
    change ((ν : Measure M).map s).map q = (ν : Measure M)
    rw [Measure.map_map hq hs, show q ∘ s = id from funext hqs, Measure.map_id]
  refine ⟨ν.map s, ?_, he⟩
  apply (map_mem_costAdmissible _ q hq c hc b).mp
  rwa [he]

theorem capacity_cost_comap_eq_of_section
    (K : Randomization M Y) (q : X → M) (hq : Measurable q)
    (s : M → X) (hs : Measurable s) (hqs : Function.RightInverse s q)
    (c : M → ℝ≥0∞) (hc : Measurable c) (b : ℝ≥0∞) :
    capacity (K.comap q hq) (costAdmissible (c ∘ q) b) = capacity K (costAdmissible c b) :=
  capacity_comap_eq K q hq _ _
    (fun μ hμ ↦ (map_mem_costAdmissible μ q hq c hc b).mpr hμ)
    (fun ν hν ↦ cost_law_realizable_of_section q hq s hs hqs c hc b ν hν)

end MonadFormal.Information
