import MonadFormal.Information.Testing.Tilted
import MonadFormal.Information.Testing.Sampling

/-!
# Finite-sample converse by exponential tilting

Paper companion: `paper/MonadFormal/Information/Testing/Converse.tex`.
The lower bound uses an attained common-support minimizer and an actual
typical-set probability. Endpoint minimizers obey directional conditions;
zero mean is not assumed.
-/

namespace MonadFormal.Information

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]

/-- Dropping the prior factor gives an upper bound continuous at either support endpoint. -/
theorem binaryError_iid_le_supportPartition (P Q : ProbabilityMeasure X)
    (π : ProbabilityMeasure Bool) (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (binaryError (iidLaw P n) (iidLaw Q n) π).toReal ≤ supportPartition P Q s ^ n := by
  have hc : IsClosed {t : ℝ | (binaryError (iidLaw P n) (iidLaw Q n) π).toReal ≤
      supportPartition P Q t ^ n} :=
    isClosed_le continuous_const ((continuous_supportPartition P Q).pow n)
  have hi : Ioo (0 : ℝ) 1 ⊆ {t : ℝ |
      (binaryError (iidLaw P n) (iidLaw Q n) π).toReal ≤ supportPartition P Q t ^ n} := by
    intro t ht
    have ha : (π : Measure Bool) {false} ^ t ≤ 1 := by
      simpa using ENNReal.rpow_le_rpow (prob_le_one (μ := (π : Measure Bool))
        (s := {false})) ht.1.le
    have hb : (π : Measure Bool) {true} ^ (1 - t) ≤ 1 := by
      simpa using ENNReal.rpow_le_rpow (prob_le_one (μ := (π : Measure Bool))
        (s := {true})) (sub_nonneg.mpr ht.2.le)
    have hp : (π : Measure Bool) {false} ^ t *
        (π : Measure Bool) {true} ^ (1 - t) ≤ 1 := by
      simpa using mul_le_mul' ha hb
    have he := (binaryError_iid_le P Q π n ht.1.le ht.2.le).trans
      (mul_le_mul' hp (le_refl (chernoffCoeff P Q t ^ n)))
    have hz : 0 ≤ supportPartition P Q t :=
      Finset.sum_nonneg fun x _ ↦ supportWeight_nonneg P Q t x
    rw [one_mul, ← ofReal_supportPartition P Q ht.1 ht.2, ← ENNReal.ofReal_pow hz] at he
    exact ENNReal.toReal_le_of_le_ofReal (pow_nonneg hz n) he
  apply closure_minimal hi hc
  simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hs

omit [Fintype X] [MeasurableSingletonClass X] in
/-- Multiplying a one-observation likelihood bound preserves its exact sample exponent. -/
theorem iid_likelihood_le (R P : ProbabilityMeasure X) (f : X → ℝ) {z c : ℝ}
    (hz : 0 ≤ z) (h : ∀ x, (R : Measure X).real {x} * z * Real.exp (c * f x) ≤
      (P : Measure X).real {x}) (n : ℕ) (x : Fin n → X) :
    (iidLaw R n : Measure (Fin n → X)).real {x} * z ^ n *
      Real.exp (c * sampleSum f n x) ≤ (iidLaw P n : Measure (Fin n → X)).real {x} := by
  have hp := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun i _ ↦ mul_nonneg (mul_nonneg measureReal_nonneg hz) (Real.exp_pos _).le)
    (fun i _ ↦ h (x i))
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, ← Finset.mul_sum, sampleSum, ← iidLaw_real_singleton] using hp

/-- Directional optimality controls both likelihoods on the same typical set. -/
theorem typical_likelihood_exponents {s m L N ε : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hN : 0 ≤ N) (hε : 0 ≤ ε)
    (hm₀ : s * m ≤ 0) (hm₁ : 0 ≤ (1 - s) * m) (hL : |L - N * m| < N * ε) :
    -N * ε ≤ (1 - s) * L ∧ -N * ε ≤ -s * L := by
  have hdev := abs_lt.mp hL
  have ha := mul_nonneg hN hm₁
  have hb := mul_nonpos_of_nonneg_of_nonpos hN hm₀
  have hc := mul_nonneg hs.1 (mul_nonneg hN hε)
  have hd := mul_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hN hε)
  have he := mul_le_mul_of_nonneg_left hdev.1.le (sub_nonneg.mpr hs.2)
  have hf := mul_le_mul_of_nonneg_left hdev.2.le hs.1
  constructor <;> nlinarith

/-- Quantitative converse with an arbitrarily small exponential slack and an explicit sample budget. -/
theorem binaryError_iid_ge_tilted (P Q : ProbabilityMeasure X) (π : ProbabilityMeasure Bool)
    (h : (commonSupport P Q).Nonempty) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmin : IsMinOn (supportPartition P Q) (Icc 0 1) s)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (hv : 2 * variance (logLikelihood P Q) (tiltedLaw P Q h s : Measure X) ≤ n * ε ^ 2) :
    min ((π : Measure Bool).real {false}) ((π : Measure Bool).real {true}) / 2 *
      supportPartition P Q s ^ n * Real.exp (-(n : ℝ) * ε) ≤
        (binaryError (iidLaw P n) (iidLaw Q n) π).toReal := by
  let R := tiltedLaw P Q h s
  let m := ∫ x, logLikelihood P Q x ∂(R : Measure X)
  let A : Set (Fin n → X) := {x | |sampleSum (logLikelihood P Q) n x - n * m| < n * ε}
  let a := (π : Measure Bool).real {false}
  let b := (π : Measure Bool).real {true}
  let z := supportPartition P Q s
  let c := min a b * z ^ n * Real.exp (-(n : ℝ) * ε)
  have hz : 0 < z := supportPartition_pos P Q h s
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg
    (le_min measureReal_nonneg measureReal_nonneg) (pow_nonneg hz.le _)) (Real.exp_pos _).le
  have hm := tilted_mean_endpoint_conditions P Q h hs hmin
  have hpoint : ∀ x ∈ A, c * (iidLaw R n : Measure (Fin n → X)).real {x} ≤
      min (a * (iidLaw P n : Measure (Fin n → X)).real {x})
        (b * (iidLaw Q n : Measure (Fin n → X)).real {x}) := by
    intro x hx
    have hex := typical_likelihood_exponents hs (Nat.cast_nonneg n) hε.le hm.1 hm.2 hx
    have hleft := iid_likelihood_le R P (logLikelihood P Q) hz.le
      (tiltedLaw_likelihood_left_le P Q h s) n x
    have hright := iid_likelihood_le R Q (logLikelihood P Q) hz.le
      (tiltedLaw_likelihood_right_le P Q h s) n x
    have hfactor : 0 ≤ (iidLaw R n : Measure (Fin n → X)).real {x} * z ^ n :=
      mul_nonneg measureReal_nonneg (pow_nonneg hz.le _)
    have hl := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex.1) hfactor).trans hleft
    have hr := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex.2) hfactor).trans hright
    have he : 0 ≤ (iidLaw R n : Measure (Fin n → X)).real {x} * z ^ n *
        Real.exp (-(n : ℝ) * ε) := mul_nonneg hfactor (Real.exp_pos _).le
    change min a b * z ^ n * Real.exp (-(n : ℝ) * ε) * _ ≤ _
    calc
      _ = min a b * ((iidLaw R n : Measure (Fin n → X)).real {x} * z ^ n *
          Real.exp (-(n : ℝ) * ε)) := by ring
      _ ≤ _ := le_min
        (mul_le_mul (min_le_left a b) hl he measureReal_nonneg)
        (mul_le_mul (min_le_right a b) hr he measureReal_nonneg)
  have hb := binaryError_lower_bound (iidLaw P n) (iidLaw Q n) (iidLaw R n) π A c hpoint
  have ht := iid_typical_ge_half R (logLikelihood P Q) hn hε hv
  calc
    _ = c * (1 / 2) := by dsimp [c, a, b, z]; ring
    _ ≤ c * (iidLaw R n : Measure (Fin n → X)).real A := mul_le_mul_of_nonneg_left ht hc
    _ ≤ _ := hb

end MonadFormal.Information
