import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Normalized total variation and Markov processing

Paper companion: `paper/MonadFormal/Approximation.tex`.
The variational definition uses all measurable tests valued in [0, 1],
not just a selected probe family. Thus its normalization is at most one.
No finiteness or discreteness assumption is imposed on the sample spaces.
-/

namespace MonadFormal.Approximation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- A measurable test, or a single parameter's bounded loss. -/
def Test (X : Type*) [MeasurableSpace X] :=
  {f : X → ℝ // Measurable f ∧ ∀ x, 0 ≤ f x ∧ f x ≤ 1}

theorem Test.integrable (f : Test X) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f.val μ := by
  refine (integrable_const (1 : ℝ)).mono' f.property.1.aestronglyMeasurable ?_
  exact ae_of_all μ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (f.property.2 x).1]
    exact (f.property.2 x).2

theorem Test.integral_bounds (f : Test X) (μ : Measure X) [IsProbabilityMeasure μ] :
    0 ≤ ∫ x, f.val x ∂μ ∧ (∫ x, f.val x ∂μ) ≤ 1 := by
  constructor
  · exact integral_nonneg fun x ↦ (f.property.2 x).1
  · calc
      (∫ x, f.val x ∂μ) ≤ ∫ _, (1 : ℝ) ∂μ :=
        integral_mono (f.integrable μ) (integrable_const 1) fun x ↦ (f.property.2 x).2
      _ = 1 := by simp

/-- Normalized total variation, in its bounded measurable test formulation. -/
noncomputable def tv (μ ν : ProbabilityMeasure X) : ℝ≥0∞ :=
  ⨆ f : Test X, ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν|

theorem test_le_tv (μ ν : ProbabilityMeasure X) (f : Test X) :
    ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν| ≤ tv μ ν :=
  le_iSup (fun f : Test X ↦ ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν|) f

theorem tv_le_one (μ ν : ProbabilityMeasure X) : tv μ ν ≤ 1 := by
  refine iSup_le fun f ↦ ?_
  have hμ := f.integral_bounds (μ : Measure X)
  have hν := f.integral_bounds (ν : Measure X)
  have h : |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  exact (ENNReal.ofReal_le_ofReal h).trans_eq (by simp)

theorem tv_self (μ : ProbabilityMeasure X) : tv μ μ = 0 := by
  simp [tv]

theorem tv_symm (μ ν : ProbabilityMeasure X) : tv μ ν = tv ν μ := by
  simp only [tv, abs_sub_comm]

theorem tv_triangle (μ ν ξ : ProbabilityMeasure X) : tv μ ξ ≤ tv μ ν + tv ν ξ := by
  refine iSup_le fun f ↦ ?_
  calc
    ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ξ|
        ≤ ENNReal.ofReal (|(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν| +
            |(∫ x, f.val x ∂ν) - ∫ x, f.val x ∂ξ|) :=
      ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ = ENNReal.ofReal |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν| +
        ENNReal.ofReal |(∫ x, f.val x ∂ν) - ∫ x, f.val x ∂ξ| :=
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ tv μ ν + tv ν ξ := add_le_add (test_le_tv μ ν f) (test_le_tv ν ξ f)

/-- Bundle only kernels that really preserve probability. -/
def Randomization (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] :=
  {K : Kernel X Y // IsMarkovKernel K}

instance (K : Randomization X Y) : IsMarkovKernel K.val := K.property

noncomputable def Randomization.apply (K : Randomization X Y)
    (μ : ProbabilityMeasure X) : ProbabilityMeasure Y :=
  ⟨K.val ∘ₘ (μ : Measure X), inferInstance⟩

noncomputable def Randomization.comp (L : Randomization Y Z) (K : Randomization X Y) :
    Randomization X Z := ⟨L.val ∘ₖ K.val, inferInstance⟩

/-- Relabel the input of a channel by a measurable map. -/
def Randomization.comap (K : Randomization Y Z) (q : X → Y) (hq : Measurable q) :
    Randomization X Z := ⟨K.val.comap q hq, inferInstance⟩

theorem Randomization.apply_comp (L : Randomization Y Z) (K : Randomization X Y)
    (μ : ProbabilityMeasure X) : (L.comp K).apply μ = L.apply (K.apply μ) := by
  apply Subtype.ext
  exact Measure.comp_assoc.symm

/-- Pull a test backwards through the simulator by conditional expectation. -/
noncomputable def Randomization.pull (K : Randomization X Y) (f : Test Y) : Test X :=
  ⟨fun x ↦ ∫ y, f.val y ∂K.val x,
    f.property.1.stronglyMeasurable.integral_kernel.measurable,
    fun x ↦ f.integral_bounds (K.val x)⟩

theorem Randomization.integral_apply (K : Randomization X Y)
    (μ : ProbabilityMeasure X) (f : Test Y) :
    (∫ y, f.val y ∂K.apply μ) = ∫ x, (K.pull f).val x ∂μ := by
  change (∫ y, f.val y ∂K.val ∘ₘ (μ : Measure X)) = _
  rw [Measure.comp_eq_comp_const_apply]
  exact Kernel.integral_comp (f.integrable _)

/-- Markov processing cannot increase normalized total variation. -/
theorem tv_processing (K : Randomization X Y) (μ ν : ProbabilityMeasure X) :
    tv (K.apply μ) (K.apply ν) ≤ tv μ ν := by
  refine iSup_le fun f ↦ ?_
  rw [K.integral_apply μ f, K.integral_apply ν f]
  exact test_le_tv μ ν (K.pull f)

end MonadFormal.Approximation
