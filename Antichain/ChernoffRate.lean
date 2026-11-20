import Antichain.SeriesGrowth

/-! Exact coefficient optimization for the global antichain upper bound. -/

namespace Antichain

open Filter
open scoped Topology

/-- From a genuine coefficient bound and an upper rate of its logarithmic
majorant, derive the normalized coefficient upper rate. The choice of saddle
scale and the Stirling remainder are proved here. -/
theorem coefficient_upper_rate_of_log_majorant
    (Z : ℕ → ℝ) (B : ℝ → ℝ) {p K A : ℝ}
    (hZ : ∀ n, 0 < Z n) (hp : 0 < p) (hA : 0 < A)
    (hcoefficient : ∀ n : ℕ, ∀ t : ℝ, 0 < t →
      Z n ≤ (n.factorial : ℝ) / t ^ n * Real.exp (B t))
    (hrate : ∀ e : ℝ, 0 < e → ∀ᶠ t : ℝ in atTop, t ^ (-p) * B t ≤ K + e)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Z n) / (n : ℝ) + (1 / p - 1) * Real.log (n : ℝ) ≤
        Real.log A / p + K / A - 1 + δ := by
  let t : ℕ → ℝ := fun n => ((n : ℝ) / A) ^ (1 / p)
  have htlim : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (one_div_pos.mpr hp)).comp
      (Tendsto.atTop_mul_const (inv_pos.mpr hA) tendsto_natCast_atTop_atTop)
  have hδA : 0 < δ * A / 2 := by positivity
  have hB := htlim.eventually (hrate (δ * A / 2) hδA)
  have hStirling : ∀ᶠ n : ℕ in atTop,
      Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ) + 1 < δ / 2 :=
    tendsto_log_factorial_remainder.eventually_lt_const (half_pos hδ)
  filter_upwards [hB, hStirling, eventually_gt_atTop 0] with n hnB hnS hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htpos : 0 < t n := Real.rpow_pos_of_pos (div_pos hnR hA) _
  have htpow : (t n) ^ p = (n : ℝ) / A := by
    dsimp [t]
    rw [← Real.rpow_mul (div_nonneg hnR.le hA.le), one_div_mul_cancel hp.ne', Real.rpow_one]
  have htlog : Real.log (t n) = (Real.log (n : ℝ) - Real.log A) / p := by
    dsimp [t]
    rw [Real.log_rpow (div_pos hnR hA), Real.log_div hnR.ne' hA.ne']
    ring
  have hB' : B (t n) ≤ (K + δ * A / 2) * ((n : ℝ) / A) := by
    have hm := mul_le_mul_of_nonneg_left hnB (Real.rpow_nonneg htpos.le p)
    have hcancel : (t n) ^ p * ((t n) ^ (-p) * B (t n)) = B (t n) := by
      rw [← mul_assoc, ← Real.rpow_add htpos]
      simp
    rw [hcancel, htpow] at hm
    exact hm.trans_eq (mul_comm _ _)
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hlog := Real.log_le_log (hZ n) (hcoefficient n (t n) htpos)
  rw [Real.log_mul (div_pos hf (pow_pos htpos n)).ne' (Real.exp_ne_zero _),
    Real.log_div hf.ne' (pow_pos htpos n).ne', Real.log_pow, Real.log_exp, htlog] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog hnR.le
  have hBdiv := div_le_div_of_nonneg_right hB' hnR.le
  have hBvalue : ((K + δ * A / 2) * ((n : ℝ) / A)) / (n : ℝ) = K / A + δ / 2 := by
    field_simp
  rw [hBvalue] at hBdiv
  have halgebra : (Real.log (n.factorial : ℝ) -
      (n : ℝ) * ((Real.log (n : ℝ) - Real.log A) / p) + B (t n)) / (n : ℝ) +
        (1 / p - 1) * Real.log (n : ℝ) =
      (Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ) + 1) +
        Real.log A / p + B (t n) / (n : ℝ) - 1 := by
    field_simp
    ring
  have hmain := add_le_add_right hdiv ((1 / p - 1) * Real.log (n : ℝ))
  rw [halgebra] at hmain
  linarith

theorem coefficient_optimized_upper_rate_of_log_majorant
    (Z : ℕ → ℝ) (B : ℝ → ℝ) {p K : ℝ}
    (hZ : ∀ n, 0 < Z n) (hp : 0 < p) (hK : 0 < K)
    (hcoefficient : ∀ n : ℕ, ∀ t : ℝ, 0 < t →
      Z n ≤ (n.factorial : ℝ) / t ^ n * Real.exp (B t))
    (hrate : ∀ e : ℝ, 0 < e → ∀ᶠ t : ℝ in atTop, t ^ (-p) * B t ≤ K + e)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Z n) / (n : ℝ) + (1 / p - 1) * Real.log (n : ℝ) ≤
        Real.log (p * K) / p + 1 / p - 1 + δ := by
  have h := coefficient_upper_rate_of_log_majorant Z B hZ hp (mul_pos hp hK)
    hcoefficient hrate hδ
  have heq : K / (p * K) = 1 / p := by field_simp
  simpa only [heq] using h

/-- Dimension-specific optimization with the paper's exact constants. -/
theorem coefficient_dimension_upper_rate
    (Z : ℕ → ℝ) (B : ℝ → ℝ) {d : ℕ} (hd : 2 ≤ d) {b S : ℝ}
    (hZ : ∀ n, 0 < Z n) (hS : 0 < S)
    (hcoefficient : ∀ n : ℕ, ∀ t : ℝ, 0 < t →
      Z n ≤ (n.factorial : ℝ) / t ^ n * Real.exp (B t))
    (hrate : ∀ e : ℝ, 0 < e → ∀ᶠ t : ℝ in atTop,
      t ^ (-(((d : ℝ) - 1) / (d : ℝ))) * B t ≤
        ((d : ℝ) / ((d : ℝ) - 1) * Real.exp ((((d : ℝ) - 1) / (d : ℝ)) * b -
          1 / (d : ℝ))) * S + e)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Z n) / (n : ℝ) + Real.log (n : ℝ) / ((d : ℝ) - 1) ≤
        b + (d : ℝ) / ((d : ℝ) - 1) * Real.log S + δ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hm0 : (d : ℝ) - 1 ≠ 0 := by linarith
  let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
  let K : ℝ := ((d : ℝ) / ((d : ℝ) - 1) *
    Real.exp (p * b - 1 / (d : ℝ))) * S
  have hp : 0 < p := by dsimp [p]; exact div_pos (by linarith) (by linarith)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (div_pos (by linarith) (by linarith)) (Real.exp_pos _)) hS
  have hev := coefficient_optimized_upper_rate_of_log_majorant Z B hZ hp hK hcoefficient hrate hδ
  have hexponent : 1 / p - 1 = 1 / ((d : ℝ) - 1) := by dsimp [p]; field_simp; ring
  have hscale : p * K = Real.exp (p * b - 1 / (d : ℝ)) * S := by
    dsimp [p, K]
    field_simp
  have hconstant : Real.log (p * K) / p + 1 / p - 1 =
      b + (d : ℝ) / ((d : ℝ) - 1) * Real.log S := by
    rw [hscale, Real.log_mul (Real.exp_ne_zero _) hS.ne', Real.log_exp]
    dsimp [p]
    field_simp
    ring
  filter_upwards [hev] with n hn
  rw [hconstant, hexponent] at hn
  simpa only [one_div_mul_eq_div] using hn

end Antichain
