import MonadFormal.Information.Testing.Converse
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optimal binary error exponent

Paper companion: `paper/MonadFormal/Information/Testing/Exponent.tex`.
The normalized logarithm is derived from the finite-sample bounds. Positive
fixed priors are essential; no common-support or interior-optimizer assumption
is imposed on the final extended-valued statement.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

/-- Taking logarithms turns the exponential upper bound into a rate lower bound. -/
theorem rate_ge_of_error_le {e z : ℝ} {n : ℕ} (he : 0 < e)
    (hn : 0 < n) (h : e ≤ z ^ n) : -Real.log z ≤ -Real.log e / n := by
  have hl := Real.log_le_log he h
  rw [Real.log_pow] at hl
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply (le_div_iff₀ hn').mpr
  nlinarith

/-- Taking logarithms retains the lower-bound constant and the exponential slack. -/
theorem rate_le_of_error_ge {e z c ε : ℝ} {n : ℕ} (hz : 0 < z) (hc : 0 < c)
    (hn : 0 < n) (h : c * z ^ n * Real.exp (-(n : ℝ) * ε) ≤ e) :
    -Real.log e / n ≤ -Real.log z + ε - Real.log c / n := by
  have hp : 0 < c * z ^ n * Real.exp (-(n : ℝ) * ε) :=
    mul_pos (mul_pos hc (pow_pos hz n)) (Real.exp_pos _)
  have hl := Real.log_le_log hp h
  rw [Real.log_mul (mul_pos hc (pow_pos hz n)).ne' (Real.exp_pos _).ne',
    Real.log_mul hc.ne' (pow_pos hz n).ne', Real.log_pow, Real.log_exp] at hl
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply (div_le_iff₀ hn').mpr
  rw [sub_mul, div_mul_cancel₀ _ hn'.ne']
  nlinarith

/-- Arbitrarily small exponential slack determines the normalized logarithmic limit. -/
theorem tendsto_rate_of_exponential_bounds (e : ℕ → ℝ) {z c : ℝ}
    (hz : 0 < z) (hc : 0 < c)
    (hu : ∀ᶠ n : ℕ in atTop, e n ≤ z ^ n)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      c * z ^ n * Real.exp (-(n : ℝ) * ε) ≤ e n) :
    Tendsto (fun n ↦ -Real.log (e n) / n) atTop (𝓝 (-Real.log z)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hu, hl 1 zero_lt_one, eventually_gt_atTop 0] with n hupper hlower hn
    have he : 0 < e n := (mul_pos (mul_pos hc (pow_pos hz n)) (Real.exp_pos _)).trans_le hlower
    exact ha.trans_le (rate_ge_of_error_le he hn hupper)
  · intro b hb
    let ε := (b + Real.log z) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hlim : Tendsto (fun n : ℕ ↦ -Real.log z + ε - Real.log c / n)
        atTop (𝓝 (-Real.log z + ε)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log c))
    have hbelow : -Real.log z + ε < b := by dsimp [ε]; linarith
    filter_upwards [hl ε hε, hlim.eventually_lt_const hbelow, eventually_gt_atTop 0]
      with n hlower hupper hn
    exact (rate_le_of_error_ge hz hc hn hlower).trans_lt hupper

variable {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]

/-- The explicit variance budget is eventually met for every positive exponential slack. -/
theorem binaryError_iid_eventually_ge (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (h : (commonSupport P Q).Nonempty) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      min ((π : Measure Bool).real {false}) ((π : Measure Bool).real {true}) / 2 *
        supportPartition P Q s ^ n * Real.exp (-(n : ℝ) * ε) ≤
          (binaryError (iidLaw P n) (iidLaw Q n) π).toReal := by
  have hv : ∀ᶠ n : ℕ in atTop,
      2 * variance (logLikelihood P Q) (tiltedLaw P Q h s : Measure X) / ε ^ 2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hv, eventually_gt_atTop 0] with n hvn hn
  exact binaryError_iid_ge_tilted P Q π h hs hmin hn hε
    ((div_le_iff₀ (sq_pos_of_pos hε)).mp hvn)

/-- With common support and positive fixed priors, optimal error is eventually strictly positive. -/
theorem binaryError_iid_eventually_pos (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (h : (commonSupport P Q).Nonempty)
    (ha : 0 < (π : Measure Bool).real {false}) (hb : 0 < (π : Measure Bool).real {true}) :
    ∀ᶠ n : ℕ in atTop, 0 < (binaryError (iidLaw P n) (iidLaw Q n) π).toReal := by
  obtain ⟨s, hs, hmin⟩ := exists_min_supportPartition P Q
  filter_upwards [binaryError_iid_eventually_ge P Q π h hs hmin zero_lt_one] with n hn
  exact (mul_pos (mul_pos (div_pos (lt_min ha hb) (by norm_num))
    (pow_pos (supportPartition_pos P Q h s) n)) (Real.exp_pos _)).trans_le hn

omit [MeasurableSingletonClass X] in
/-- The attained common-support minimum identifies the finite Chernoff information exactly. -/
theorem chernoffInfo_eq_log_supportPartition (P Q : ProbabilityMeasure X)
    (h : (commonSupport P Q).Nonempty) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s) :
    chernoffInfo P Q = ((-Real.log (supportPartition P Q s) : ℝ) : EReal) := by
  rw [chernoffInfo, iInf_chernoffCoeff_eq_of_isMinOn P Q hs hmin,
    ENNReal.log_ofReal_of_pos (supportPartition_pos P Q h s), EReal.coe_neg]

/-- The real-valued rate converges for every nonempty common support, including endpoint optima. -/
theorem tendsto_binaryError_log_rate (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (h : (commonSupport P Q).Nonempty)
    (ha : 0 < (π : Measure Bool).real {false}) (hb : 0 < (π : Measure Bool).real {true})
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s) :
    Tendsto (fun n : ℕ ↦ -Real.log (binaryError (iidLaw P n) (iidLaw Q n) π).toReal / n)
      atTop (𝓝 (-Real.log (supportPartition P Q s))) := by
  apply tendsto_rate_of_exponential_bounds _
    (c := min ((π : Measure Bool).real {false}) ((π : Measure Bool).real {true}) / 2)
    (supportPartition_pos P Q h s)
    (div_pos (lt_min ha hb) (by norm_num))
  · exact Eventually.of_forall fun n ↦ binaryError_iid_le_supportPartition P Q π n hs
  · exact fun _ hε ↦ binaryError_iid_eventually_ge P Q π h hs hmin hε

/-- Normalized negative log error in nats; zero error keeps its infinite rate for positive `n`. -/
noncomputable def binaryErrorRate (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (n : ℕ) : EReal := -ENNReal.log (binaryError (iidLaw P n) (iidLaw Q n) π) / n

omit [Fintype X] [MeasurableSingletonClass X] in
/-- For positive finite error, the extended rate agrees with the ordinary real logarithm. -/
theorem binaryErrorRate_eq_coe (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    {n : ℕ} (he : 0 < (binaryError (iidLaw P n) (iidLaw Q n) π).toReal) :
    binaryErrorRate P Q π n =
      ((-Real.log (binaryError (iidLaw P n) (iidLaw Q n) π).toReal / n : ℝ) : EReal) := by
  rw [binaryErrorRate, ENNReal.log_pos_real' he, EReal.coe_div, EReal.coe_neg,
    EReal.coe_coe_eq_natCast]

/-- Fixed positive priors have Chernoff information as their optimal iid error exponent. -/
theorem tendsto_binaryErrorRate (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (ha : 0 < (π : Measure Bool).real {false}) (hb : 0 < (π : Measure Bool).real {true}) :
    Tendsto (binaryErrorRate P Q π) atTop (𝓝 (chernoffInfo P Q)) := by
  by_cases h : (commonSupport P Q).Nonempty
  · obtain ⟨s, hs, hmin⟩ := exists_min_supportPartition P Q
    rw [chernoffInfo_eq_log_supportPartition P Q h hs hmin]
    apply (EReal.tendsto_coe.mpr (tendsto_binaryError_log_rate P Q π h ha hb hs hmin)).congr'
    filter_upwards [binaryError_iid_eventually_pos P Q π h ha hb] with n hn
    exact (binaryErrorRate_eq_coe P Q π hn).symm
  · have hd : ∀ x, (P : Measure X) {x} = 0 ∨ (Q : Measure X) {x} = 0 := by
      intro x
      have hx : x ∉ commonSupport P Q := fun hx ↦ h ⟨x, hx⟩
      simpa only [commonSupport, mem_ofPred_eq, Measure.real,
        ENNReal.toReal_pos_iff, measure_lt_top, and_true, not_and_or,
        not_lt, nonpos_iff_eq_zero] using hx
    rw [(chernoffInfo_eq_top_iff P Q).mpr hd]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [binaryErrorRate, binaryError_iid_eq_zero_of_disjoint P Q π hd hn]
    simp only [ENNReal.log_zero, EReal.neg_bot]
    exact (EReal.top_div_of_pos_ne_top (by exact_mod_cast hn)
      (by rw [← EReal.coe_coe_eq_natCast n]; exact EReal.coe_ne_top _)).symm

end MonadFormal.Information
