import MonadFormal.Approximation
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Mutual information and channel processing

Paper companion: `paper/MonadFormal/Information.tex`.
Mutual information is relative entropy of a joint probability law against
the product of its marginals. Values are extended nonnegative reals in nats;
infinite information is not silently converted to a real number.
The channel interface reuses `Approximation.Randomization`.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory InformationTheory
open Approximation
open scoped ENNReal

variable {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace W]

/-- Relative entropy against independence; used below on probability laws. -/
noncomputable def mutualInfo (ρ : Measure (X × Y)) : ℝ≥0∞ :=
  klDiv ρ (ρ.fst.prod ρ.snd)

/-- Separate measurable processing of either variable cannot increase information. -/
theorem mutualInfo_map_le (ρ : Measure (X × Y)) [IsFiniteMeasure ρ]
    {f : X → Z} {g : Y → W} (hf : Measurable f) (hg : Measurable g) :
    mutualInfo (ρ.map (Prod.map f g)) ≤ mutualInfo ρ := by
  have hfst : (ρ.map (Prod.map f g)).fst = ρ.fst.map f := by
    simp only [Measure.fst, Measure.map_map, hf, measurable_fst, hf.prodMap hg]
    rfl
  have hsnd : (ρ.map (Prod.map f g)).snd = ρ.snd.map g := by
    simp only [Measure.snd, Measure.map_map, hg, measurable_snd, hf.prodMap hg]
    rfl
  rw [mutualInfo, hfst, hsnd, Measure.map_prod_map _ _ hf hg]
  exact klDiv_map_le _ _ (hf.prodMap hg)

theorem mutualInfo_prod (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : mutualInfo (μ.prod ν) = 0 := by
  simp [mutualInfo]

theorem parallel_comp_prod (K : Randomization X Z) (L : Randomization Y W)
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (K.val ∥ₖ L.val) ∘ₘ μ.prod ν = (K.val ∘ₘ μ).prod (L.val ∘ₘ ν) := by
  have hc : Kernel.const Unit (μ.prod ν) = Kernel.const Unit μ ×ₖ Kernel.const Unit ν := by
    ext u s hs
    simp [Kernel.prod_apply]
  rw [Measure.comp_eq_comp_const_apply, hc, Kernel.parallelComp_comp_prod]
  simp [Kernel.prod_apply]

theorem fst_parallel_comp (K : Randomization X Z) (L : Randomization Y W)
    (ρ : Measure (X × Y)) : ((K.val ∥ₖ L.val) ∘ₘ ρ).fst = K.val ∘ₘ ρ.fst := by
  have hf : (K.val ∥ₖ L.val).fst = K.val.prodMkRight Y := by
    ext p s hs
    simp [Kernel.fst_apply, Kernel.parallelComp_apply]
  rw [Measure.fst, Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, hf,
    Kernel.prodMkRight, ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  rfl

theorem snd_parallel_comp (K : Randomization X Z) (L : Randomization Y W)
    (ρ : Measure (X × Y)) : ((K.val ∥ₖ L.val) ∘ₘ ρ).snd = L.val ∘ₘ ρ.snd := by
  have hs : (K.val ∥ₖ L.val).snd = L.val.prodMkLeft X := by
    ext p s hs
    simp [Kernel.snd_apply, Kernel.parallelComp_apply]
  rw [Measure.snd, Measure.map_comp _ _ measurable_snd, ← Kernel.snd_eq, hs,
    Kernel.prodMkLeft, ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  rfl

/-- Independent Markov processing of the two variables cannot increase information. -/
theorem mutualInfo_parallel_le (K : Randomization X Z) (L : Randomization Y W)
    (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] :
    mutualInfo ((K.val ∥ₖ L.val) ∘ₘ ρ) ≤ mutualInfo ρ := by
  rw [mutualInfo, fst_parallel_comp, snd_parallel_comp, ← parallel_comp_prod]
  exact klDiv_comp_right_le _ _ _

/-- The single-use information carried by a probability-preserving record channel. -/
noncomputable def channelInfo (K : Randomization X Y) (μ : ProbabilityMeasure X) : ℝ≥0∞ :=
  mutualInfo ((μ : Measure X) ⊗ₘ K.val)

theorem channelInfo_eq (K : Randomization X Y) (μ : ProbabilityMeasure X) :
    channelInfo K μ = klDiv ((μ : Measure X) ⊗ₘ K.val)
      ((μ : Measure X).prod (K.val ∘ₘ (μ : Measure X))) := by
  simp [channelInfo, mutualInfo]

/-- Postprocessing a record cannot increase its single-use information. -/
theorem channelInfo_postprocess (K : Randomization X Y) (L : Randomization Y Z)
    (μ : ProbabilityMeasure X) : channelInfo (L.comp K) μ ≤ channelInfo K μ := by
  let Id : Randomization X X := ⟨Kernel.id, inferInstance⟩
  simpa only [Id, Measure.parallelComp_comp_compProd, channelInfo, Randomization.comp] using
    mutualInfo_parallel_le Id L ((μ : Measure X) ⊗ₘ K.val)

/-- Single-letter constrained capacity over the declared admissible input laws.
This definition does not assert a repeated-use coding theorem. -/
noncomputable def capacity (K : Randomization X Y) (A : Set (ProbabilityMeasure X)) : ℝ≥0∞ :=
  ⨆ μ ∈ A, channelInfo K μ

/-- Input laws whose expected nonnegative cost fits the declared budget. -/
def costAdmissible (c : X → ℝ≥0∞) (b : ℝ≥0∞) : Set (ProbabilityMeasure X) :=
  {μ | (∫⁻ x, c x ∂(μ : Measure X)) ≤ b}

theorem channelInfo_le_capacity (K : Randomization X Y)
    {A : Set (ProbabilityMeasure X)} {μ : ProbabilityMeasure X} (hμ : μ ∈ A) :
    channelInfo K μ ≤ capacity K A :=
  le_iSup_of_le μ (le_iSup_of_le hμ le_rfl)

theorem capacity_mono (K : Randomization X Y)
    {A B : Set (ProbabilityMeasure X)} (h : A ⊆ B) : capacity K A ≤ capacity K B := by
  exact iSup₂_le fun μ hμ ↦ channelInfo_le_capacity K (h hμ)

theorem capacity_postprocess (K : Randomization X Y) (L : Randomization Y Z)
    (A : Set (ProbabilityMeasure X)) : capacity (L.comp K) A ≤ capacity K A := by
  exact iSup₂_le fun μ hμ ↦ (channelInfo_postprocess K L μ).trans
    (channelInfo_le_capacity K hμ)

end MonadFormal.Information
