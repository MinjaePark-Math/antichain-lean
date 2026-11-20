import Antichain.RankCounting
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! The printed two-dimensional logarithmic remainder, with an explicit
O(1/n) bound obtained from Mathlib's proved Stirling difference estimate. -/

noncomputable section

namespace Antichain

open Filter Asymptotics
open scoped Topology

theorem log_stirlingSeq_error_bound (n : ℕ) :
    0 ≤ Real.log (Stirling.stirlingSeq (n + 1)) - Real.log (Real.sqrt Real.pi) ∧
    Real.log (Stirling.stirlingSeq (n + 1)) - Real.log (Real.sqrt Real.pi) ≤
      1 / (2 * ((n : ℝ) + 1)) := by
  let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (k + 1))
  have hlim : Tendsto f atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))).tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
  have hstep (k : ℕ) : f k - f (k + 1) ≤
      1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) := by
    have h := Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ k
    have hscalar : (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2) ≤
        1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      field_simp
      nlinarith
    have hh : f k - f (k + 1) ≤ (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2) := by
      simpa only [f, Nat.cast_add, Nat.cast_one, Nat.add_assoc] using h
    exact hh.trans hscalar
  have hpartial (k : ℕ) : f n - f (n + k) ≤
      1 / (2 * ((n : ℝ) + 1)) - 1 / (2 * ((n : ℝ) + (k : ℝ) + 1)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hstep (n + k)
      push_cast at hs ⊢
      have heq : n + (k + 1) = (n + k) + 1 := by omega
      rw [heq]
      have hden : (n : ℝ) + ((k : ℝ) + 1) + 1 = (n : ℝ) + (k : ℝ) + 2 := by ring
      rw [hden]
      linarith
  constructor
  · have hs := Stirling.sqrt_pi_le_stirlingSeq (Nat.succ_ne_zero n)
    have hh := Real.log_le_log (Real.sqrt_pos.mpr Real.pi_pos) hs
    exact sub_nonneg.mpr hh
  · apply le_of_tendsto ((tendsto_const_nhds.sub
      (hlim.comp (by simpa only [Nat.add_comm] using (tendsto_add_atTop_nat n)))) :
        Tendsto (fun k : ℕ => f n - f (n + k)) atTop
          (𝓝 (f n - Real.log (Real.sqrt Real.pi))))
    apply Eventually.of_forall
    intro k
    exact (hpartial k).trans (sub_le_self _ (by positivity))

/-- The actual d=2 remainder in the manuscript is bounded in absolute value
by 1/(2n), for every n>0. -/
theorem antichain_dimension_two_refined_remainder_bound (n : ℕ) (hn : 0 < n) :
    |Real.log (antichainProbability n 2) + (n : ℝ) * Real.log (n : ℝ) -
      (n : ℝ) + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (n : ℝ))| ≤
        1 / (2 * (n : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := log_stirlingSeq_error_bound k
  have hf := Stirling.log_stirlingSeq_formula (k + 1)
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hlog : Real.log (Real.sqrt Real.pi) = (1 / 2 : ℝ) * Real.log Real.pi := by
    rw [Real.log_sqrt Real.pi_pos.le]
    ring
  rw [Real.log_div hk.ne' (Real.exp_ne_zero 1), Real.log_exp] at hf
  rw [antichainProbability_dimension_two, one_div, Real.log_inv]
  have hsplit : Real.log (2 * Real.pi * ((k + 1 : ℕ) : ℝ)) =
      Real.log (2 * ((k + 1 : ℕ) : ℝ)) + Real.log Real.pi := by
    rw [← Real.log_mul (by positivity : (2 * ((k + 1 : ℕ) : ℝ)) ≠ 0) Real.pi_ne_zero]
    congr 1
    ring
  rw [hlog] at h
  rw [hsplit]
  have heq : -Real.log ((k + 1).factorial : ℝ) +
      ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) +
      (1 / 2 : ℝ) * (Real.log (2 * ((k + 1 : ℕ) : ℝ)) + Real.log Real.pi) =
      -(Real.log (Stirling.stirlingSeq (k + 1)) - (1 / 2 : ℝ) * Real.log Real.pi) := by
    linarith
  rw [heq, abs_neg, abs_of_nonneg h.1]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using h.2

/-- Literal O(1/n) packaging of the refined source remainder. -/
theorem antichain_dimension_two_refined_remainder_source :
    (fun n : ℕ => Real.log (antichainProbability n 2) +
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
        (1 / 2 : ℝ) * Real.log (2 * Real.pi * (n : ℝ))) =O[atTop]
      (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (1 / 2 : ℝ)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by exact_mod_cast hn : (0 : ℝ) < n))]
  exact (antichain_dimension_two_refined_remainder_bound n hn).trans_eq (by ring)

end Antichain
