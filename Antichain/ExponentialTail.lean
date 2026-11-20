import Antichain.BoundedMoment

/-! Genuine Markov/Chernoff bounds from actual integrable exponential moments. -/

namespace Antichain

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem probability_exp_chernoff {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (Y : X → ℝ) {theta a : ℝ} (htheta : 0 < theta)
    (hI : Integrable (fun x => Real.exp (theta * Y x)) mu) :
    mu.real {x | a ≤ Y x} ≤ Real.exp (-theta * a) *
      (∫ x, Real.exp (theta * Y x) ∂mu) := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => Real.exp_nonneg (theta * Y x))) hI
    (Real.exp (theta * a))
  have heq : {x | Real.exp (theta * a) ≤ Real.exp (theta * Y x)} = {x | a ≤ Y x} := by
    ext x
    simp only [Set.mem_setOf_eq, Real.exp_le_exp, mul_le_mul_iff_right₀ htheta]
  rw [heq] at h
  calc
    _ ≤ (∫ x, Real.exp (theta * Y x) ∂mu) / Real.exp (theta * a) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using h)
    _ = _ := by rw [neg_mul, Real.exp_neg, div_eq_mul_inv]; ring

/-- A strict gap in an actual logarithmic moment limit gives an exponential
tail, including events of probability zero and varying sample spaces. -/
theorem exponential_tail_of_log_moment_gap
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (mu : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (mu n)]
    (Y : ∀ n, X n → ℝ) {theta delta L : ℝ} (htheta : 0 < theta)
    (hI : ∀ n, Integrable (fun x => Real.exp (theta * Y n x)) (mu n))
    (hLimit : Tendsto (fun n : ℕ => Real.log
      (∫ x, Real.exp (theta * Y n x) ∂mu n) / (n : ℝ)) atTop (𝓝 L))
    (hgap : L < theta * delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      (mu n).real {x | delta * (n : ℝ) ≤ Y n x} ≤ Real.exp (-alpha * (n : ℝ)) := by
  let alpha : ℝ := (theta * delta - L) / 2
  have ha : 0 < alpha := by dsimp [alpha]; linarith
  refine ⟨alpha, ha, ?_⟩
  have hsmall := hLimit.eventually (Iio_mem_nhds (show L < L + alpha by linarith))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hMpos : 0 < ∫ x, Real.exp (theta * Y n x) ∂mu n := mgf_pos (hI n)
  have hlog : Real.log (∫ x, Real.exp (theta * Y n x) ∂mu n) ≤ (L + alpha) * (n : ℝ) :=
    ((div_lt_iff₀ hnR).mp hn).le
  calc
    _ ≤ Real.exp (-theta * (delta * (n : ℝ))) *
        (∫ x, Real.exp (theta * Y n x) ∂mu n) :=
      probability_exp_chernoff (mu n) (Y n) htheta (hI n)
    _ ≤ Real.exp (-theta * (delta * (n : ℝ))) * Real.exp ((L + alpha) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left ((Real.log_le_iff_le_exp hMpos).mp hlog) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [alpha]; ring

end Antichain
