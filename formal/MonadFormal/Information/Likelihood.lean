import MonadFormal.Information

/-!
# Likelihood transport through a deterministic input map

Paper companion: `paper/MonadFormal/Information/Likelihood.tex`.
Joint densities can be pulled back even when a conditional kernel for the
microstate does not exist. The proof compares one measurable output event
at a time; it never assumes a common exceptional set for all output events.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory InformationTheory Set
open Approximation
open scoped ENNReal

variable {X M Y : Type*} [MeasurableSpace X] [MeasurableSpace M] [MeasurableSpace Y]

/-- Pushing the microstate joint law through the coarse-graining gives the macrostate law. -/
theorem map_input_joint (K : Randomization M Y) (μ : ProbabilityMeasure X)
    (q : X → M) (hq : Measurable q) :
    (((μ : Measure X) ⊗ₘ (K.comap q hq).val).map (Prod.map q id)) =
      (μ.map q : Measure M) ⊗ₘ K.val := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (hq.prodMap measurable_id) (hs.prod ht)]
  change ((μ : Measure X) ⊗ₘ (K.comap q hq).val) ((q ⁻¹' s) ×ˢ t) = _
  rw [Measure.compProd_apply_prod (hq hs) ht, Measure.compProd_apply_prod hs ht]
  change (∫⁻ x in q ⁻¹' s, K.val (q x) t ∂(μ : Measure X)) =
    ∫⁻ m in s, K.val m t ∂(μ : Measure X).map q
  rw [setLIntegral_map hs (K.val.measurable_coe ht) hq]

/-- A joint density identity survives pullback of the common input law. -/
theorem withDensity_input_joint (K L : Randomization M Y) (μ : ProbabilityMeasure X)
    (q : X → M) (hq : Measurable q) (f : M × Y → ℝ≥0∞) (hf : Measurable f)
    (h : ((μ.map q : Measure M) ⊗ₘ L.val).withDensity f =
      (μ.map q : Measure M) ⊗ₘ K.val) :
    ((μ : Measure X) ⊗ₘ (L.comap q hq).val).withDensity (f ∘ Prod.map q id) =
      (μ : Measure X) ⊗ₘ (K.comap q hq).val := by
  have hmass : (∫⁻ p, (f ∘ Prod.map q id) p
      ∂((μ : Measure X) ⊗ₘ (L.comap q hq).val)) ≠ ∞ := by
    simp only [Function.comp_apply]
    rw [← lintegral_map hf (hq.prodMap measurable_id), map_input_joint]
    have hn : (((μ.map q : Measure M) ⊗ₘ L.val).withDensity f) univ ≠ ∞ := by
      rw [h]
      exact measure_ne_top _ _
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hn
  let : IsFiniteMeasure
      (((μ : Measure X) ⊗ₘ (L.comap q hq).val).withDensity (f ∘ Prod.map q id)) :=
    isFiniteMeasure_withDensity hmass
  apply Measure.ext_prod
  intro s t hs ht
  have htF : Measurable fun m ↦ ∫⁻ y in t, f (m, y) ∂L.val m := by
    have hi : Measurable fun p : M × Y ↦ t.indicator (fun y ↦ f (p.1, y)) p.2 := by
      convert hf.indicator (measurable_snd ht) using 1
      ext p
      by_cases hp : p.2 ∈ t <;> simp [indicator, hp]
    simpa only [lintegral_indicator ht] using hi.lintegral_kernel_prod_right'
  have he : (fun m ↦ ∫⁻ y in t, f (m, y) ∂L.val m) =ᵐ[(μ.map q : Measure M)]
      fun m ↦ K.val m t := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite htF (K.val.measurable_coe ht)
    intro a ha _
    rw [← Measure.setLIntegral_compProd hf ha ht, ← withDensity_apply _ (ha.prod ht), h,
      Measure.compProd_apply_prod ha ht]
  rw [withDensity_apply _ (hs.prod ht),
    Measure.setLIntegral_compProd (hf.comp (hq.prodMap measurable_id)) hs ht,
    Measure.compProd_apply_prod hs ht]
  exact lintegral_congr_ae (ae_restrict_of_ae (ae_of_ae_map hq.aemeasurable he))

/-- Relative entropy between two channels with a common input law depends only on its image. -/
theorem klDiv_input_joint (K L : Randomization M Y) (μ : ProbabilityMeasure X)
    (q : X → M) (hq : Measurable q) :
    klDiv ((μ : Measure X) ⊗ₘ (K.comap q hq).val)
      ((μ : Measure X) ⊗ₘ (L.comap q hq).val) =
    klDiv ((μ.map q : Measure M) ⊗ₘ K.val) ((μ.map q : Measure M) ⊗ₘ L.val) := by
  apply le_antisymm
  · by_cases hac : (μ.map q : Measure M) ⊗ₘ K.val ≪ (μ.map q : Measure M) ⊗ₘ L.val
    swap
    · rw [klDiv_of_not_ac hac]
      exact le_top
    let f := ((μ.map q : Measure M) ⊗ₘ K.val).rnDeriv ((μ.map q : Measure M) ⊗ₘ L.val)
    have hf : Measurable f := Measure.measurable_rnDeriv _ _
    have hw := withDensity_input_joint K L μ q hq f hf
      (Measure.withDensity_rnDeriv_eq _ _ hac)
    have hac' : (μ : Measure X) ⊗ₘ (K.comap q hq).val ≪
        (μ : Measure X) ⊗ₘ (L.comap q hq).val := by
      rw [← hw]
      exact withDensity_absolutelyContinuous _ _
    have hr : ((μ : Measure X) ⊗ₘ (K.comap q hq).val).rnDeriv
        ((μ : Measure X) ⊗ₘ (L.comap q hq).val) =ᵐ[((μ : Measure X) ⊗ₘ (L.comap q hq).val)]
        f ∘ Prod.map q id := by
      rw [← hw]
      exact Measure.rnDeriv_withDensity _ (hf.comp (hq.prodMap measurable_id))
    rw [klDiv_eq_lintegral_klFun_of_ac hac', klDiv_eq_lintegral_klFun_of_ac hac]
    apply le_of_eq
    calc
      _ = ∫⁻ p, ENNReal.ofReal (klFun (f (Prod.map q id p)).toReal)
          ∂((μ : Measure X) ⊗ₘ (L.comap q hq).val) := by
        apply lintegral_congr_ae
        filter_upwards [hr] with p hp
        rw [hp]
        rfl
      _ = ∫⁻ p, ENNReal.ofReal (klFun (f p).toReal)
          ∂((μ.map q : Measure M) ⊗ₘ L.val) := by
        have hm : (∫⁻ p, ENNReal.ofReal (klFun (f p).toReal)
            ∂(((μ : Measure X) ⊗ₘ (L.comap q hq).val).map (Prod.map q id))) =
            ∫⁻ p, ENNReal.ofReal (klFun (f (Prod.map q id p)).toReal)
              ∂((μ : Measure X) ⊗ₘ (L.comap q hq).val) :=
          lintegral_map (by fun_prop) (hq.prodMap measurable_id)
        rw [map_input_joint] at hm
        exact hm.symm
  · simpa only [map_input_joint] using
      klDiv_map_le ((μ : Measure X) ⊗ₘ (K.comap q hq).val)
        ((μ : Measure X) ⊗ₘ (L.comap q hq).val) (hq.prodMap measurable_id)

end MonadFormal.Information
