import Antichain.TileSeries

/-! Linear control of the actual tile series near zero. -/

noncomputable section

namespace Antichain

/-- An exponential series with nonnegative coefficients is linearly controlled
near zero by its value at one. -/
theorem egf_le_one_add_mul_sub_one {v : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n) (hv0 : v 0 = 1)
    (h1 : Summable (fun n : ℕ => v n / (n.factorial : ℝ)))
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hseries : Summable (fun n : ℕ => v n * s ^ n / (n.factorial : ℝ))) :
    exponentialGeneratingFunction v s ≤
      1 + s * (exponentialGeneratingFunction v 1 - 1) := by
  have htail1 : Summable (fun n : ℕ => v (n + 1) / ((n + 1).factorial : ℝ)) :=
    h1.comp_injective Nat.succ_injective
  have htails : Summable (fun n : ℕ =>
      v (n + 1) * s ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
    hseries.comp_injective Nat.succ_injective
  have hp : ∀ n : ℕ, s ^ (n + 1) ≤ s := by
    intro n
    rw [pow_succ]
    exact mul_le_of_le_one_left hs (pow_le_one₀ hs hs1)
  have hle : (∑' n : ℕ, v (n + 1) * s ^ (n + 1) / ((n + 1).factorial : ℝ)) ≤
      s * ∑' n : ℕ, v (n + 1) / ((n + 1).factorial : ℝ) := by
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum _ htails (htail1.mul_left s)
    intro n
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hp n) (hv _))
      (by positivity)).trans_eq (by ring)
  have heq1 : exponentialGeneratingFunction v 1 =
      1 + ∑' n : ℕ, v (n + 1) / ((n + 1).factorial : ℝ) := by
    unfold exponentialGeneratingFunction
    simp only [one_pow, mul_one]
    rw [h1.tsum_eq_zero_add]
    simp [hv0]
  have heqs : exponentialGeneratingFunction v s =
      1 + ∑' n : ℕ, v (n + 1) * s ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    unfold exponentialGeneratingFunction
    rw [hseries.tsum_eq_zero_add]
    simp [hv0]
  rw [heqs, heq1]
  linarith

theorem tileGeneratingFunction_small_argument {d : ℕ} (hd : 2 ≤ d)
    {epsilon c s : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.log (tileGeneratingFunction d epsilon c s) ≤
      s * (tileGeneratingFunction d epsilon c 1 - 1) := by
  have hpos : 0 < tileGeneratingFunction d epsilon c s :=
    lt_of_lt_of_le zero_lt_one (tileGeneratingFunction_one_le hd hepsilon hc hs)
  have hbound := egf_le_one_add_mul_sub_one
    (fun n => (tileCoefficient_pos hd hepsilon hc n).le)
    (tileCoefficient_zero d epsilon c)
    (by simpa using tileSeries_summable hd hepsilon hc (by norm_num : (0 : ℝ) ≤ 1))
    hs hs1 (tileSeries_summable hd hepsilon hc hs)
  exact (Real.log_le_sub_one_of_pos hpos).trans (by
    change exponentialGeneratingFunction (tileCoefficient d epsilon c) s - 1 ≤ _
    unfold tileGeneratingFunction
    linarith)


end Antichain
