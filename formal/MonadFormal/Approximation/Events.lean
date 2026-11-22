import MonadFormal.Approximation
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The event and test formulations of total variation coincide

Paper companion: `paper/MonadFormal/Approximation/Events.tex`.
Layer-cake integration proves the reverse bound; the test formulation is
not an assumed replacement for event-based total variation.
-/

namespace MonadFormal.Approximation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

noncomputable def eventTV (μ ν : ProbabilityMeasure X) : ℝ≥0∞ :=
  ⨆ s : {s : Set X // MeasurableSet s},
    ENNReal.ofReal |(μ : Measure X).real s.val - (ν : Measure X).real s.val|

noncomputable def Test.indicator (s : Set X) (hs : MeasurableSet s) : Test X := by
  classical
  refine ⟨s.indicator (fun _ ↦ (1 : ℝ)), measurable_const.indicator hs, ?_⟩
  intro x
  by_cases hx : x ∈ s <;> simp [hx]

theorem eventTV_le_tv (μ ν : ProbabilityMeasure X) : eventTV μ ν ≤ tv μ ν := by
  refine iSup_le fun s ↦ ?_
  simpa only [Test.indicator, integral_indicator_const _ s.property,
    smul_eq_mul, mul_one] using test_le_tv μ ν (Test.indicator s.val s.property)

/-- Tail probabilities are measurable tests as functions of the threshold. -/
noncomputable def Test.tail (f : Test X) (μ : ProbabilityMeasure X) : Test ℝ := by
  refine ⟨fun t ↦ (μ : Measure X).real {x | t ≤ f.val x}, ?_, ?_⟩
  · apply Antitone.measurable
    intro s t hst
    exact measureReal_mono fun x hx ↦ hst.trans hx
  · intro t
    refine ⟨measureReal_nonneg, ?_⟩
    calc
      (μ : Measure X).real {x | t ≤ f.val x} ≤ (μ : Measure X).real univ :=
        measureReal_mono (subset_univ _)
      _ = 1 := by simp

theorem Test.integral_eq_integral_tail (f : Test X) (μ : ProbabilityMeasure X) :
    (∫ x, f.val x ∂μ) = ∫ t in Ioc (0 : ℝ) 1, (f.tail μ).val t :=
  (f.integrable (μ : Measure X)).integral_eq_integral_Ioc_meas_le
    (ae_of_all _ fun x ↦ (f.property.2 x).1)
    (ae_of_all _ fun x ↦ (f.property.2 x).2)

theorem tv_eq_eventTV (μ ν : ProbabilityMeasure X) : tv μ ν = eventTV μ ν := by
  apply le_antisymm _ (eventTV_le_tv μ ν)
  have hfin : eventTV μ ν ≠ ∞ := ne_top_of_le_ne_top (by simp) <|
    (eventTV_le_tv μ ν).trans (tv_le_one μ ν)
  refine iSup_le fun f ↦ ?_
  have pointwise (t : ℝ) : |(f.tail μ).val t - (f.tail ν).val t| ≤ (eventTV μ ν).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    exact le_iSup (fun s : {s : Set X // MeasurableSet s} ↦
      ENNReal.ofReal |(μ : Measure X).real s.val - (ν : Measure X).real s.val|)
      ⟨{x | t ≤ f.val x}, measurableSet_le measurable_const f.property.1⟩
  have hi := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun t ↦ (f.tail μ).val t - (f.tail ν).val t)
    (ae_of_all _ fun t ↦ by simpa only [Real.norm_eq_abs] using pointwise t)
  have hbound : |(∫ x, f.val x ∂μ) - ∫ x, f.val x ∂ν| ≤ (eventTV μ ν).toReal := by
    rw [f.integral_eq_integral_tail μ, f.integral_eq_integral_tail ν,
      ← integral_sub ((f.tail μ).integrable _) ((f.tail ν).integrable _)]
    simpa [Real.norm_eq_abs, measureReal_def] using hi
  exact (ENNReal.ofReal_le_ofReal hbound).trans_eq (ENNReal.ofReal_toReal hfin)

theorem tv_eq_zero_iff (μ ν : ProbabilityMeasure X) : tv μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro s hs
    have he : ENNReal.ofReal |(μ : Measure X).real s - (ν : Measure X).real s| ≤ 0 := by
      calc
        _ ≤ eventTV μ ν := le_iSup _ ⟨s, hs⟩
        _ ≤ tv μ ν := eventTV_le_tv μ ν
        _ = 0 := h
    have hz : (μ : Measure X).real s = (ν : Measure X).real s := by
      exact sub_eq_zero.mp <| abs_eq_zero.mp <| le_antisymm
        (ENNReal.ofReal_eq_zero.mp (le_antisymm he zero_le)) (abs_nonneg _)
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hz
  · rintro rfl
    exact tv_self μ

end MonadFormal.Approximation
