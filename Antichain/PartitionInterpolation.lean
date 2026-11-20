import Antichain.OnePointIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Actual normalized weighted rates and passage to arbitrary sample sizes. -/

noncomputable section

namespace Antichain

open Filter
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def normalizedPartitionLog (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) : ℝ :=
  Real.log (weightedPartition n sigma c) / (n : ℝ) + Real.log (n : ℝ) / ((d : ℝ) - 1)

theorem normalizedPartitionLog_deletion (hd : 2 ≤ d) (n N : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    (N : ℝ) / (n : ℝ) * normalizedPartitionLog N sigma c -
      (((N : ℝ) / (n : ℝ) * Real.log (N : ℝ) - Real.log (n : ℝ)) / ((d : ℝ) - 1) +
        ((N - n : ℕ) : ℝ) / (n : ℝ) * Real.log (unrestrictedSinglePointMass sigma c).toReal) ≤
      normalizedPartitionLog n sigma c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hm : 0 < (unrestrictedSinglePointMass sigma c).toReal :=
    ENNReal.toReal_pos (unrestrictedSinglePointMass_pos hd sigma c).ne'
      (unrestrictedSinglePointMass_lt_top sigma c hc).ne
  have hZ := weightedPartition_pos N sigma c hc hd
  have h := Real.log_le_log (mul_pos (inv_pos.mpr (pow_pos hm _)) hZ)
    (weightedPartition_deletion_lower hd n N hnN sigma c hc)
  rw [Real.log_mul (inv_pos.mpr (pow_pos hm _)).ne' hZ.ne',
    Real.log_inv, Real.log_pow] at h
  have hdiv := div_le_div_of_nonneg_right h hnR.le
  have hid : (N : ℝ) / (n : ℝ) * normalizedPartitionLog N sigma c -
      (((N : ℝ) / (n : ℝ) * Real.log (N : ℝ) - Real.log (n : ℝ)) / ((d : ℝ) - 1) +
        ((N - n : ℕ) : ℝ) / (n : ℝ) * Real.log (unrestrictedSinglePointMass sigma c).toReal) =
      (-(N - n : ℕ) * Real.log (unrestrictedSinglePointMass sigma c).toReal +
        Real.log (weightedPartition N sigma c)) / (n : ℝ) +
          Real.log (n : ℝ) / ((d : ℝ) - 1) := by
    unfold normalizedPartitionLog
    field_simp
    ring
  rw [hid]
  simpa only [normalizedPartitionLog, neg_mul] using
    add_le_add_right hdiv (Real.log (n : ℝ) / ((d : ℝ) - 1))

/-- The actual model lower rate passes from slightly larger constructed sizes
to all sizes. The hypotheses concern only the constructed integer sizes and
their lower rates; the deletion inequality is proved from the Gaussian model. -/
theorem normalizedPartitionLog_interpolate_lower (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (N : ℕ → ℕ) (hN : ∀ᶠ n : ℕ in atTop, n ≤ N n)
    (hRatio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 1))
    (hGap : Tendsto (fun n : ℕ => ((N n - n : ℕ) : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0))
    {L : ℝ}
    (hLower : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
      L - e ≤ normalizedPartitionLog (N n) sigma c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, L - δ ≤ normalizedPartitionLog n sigma c := by
  let R : ℕ → ℝ := fun n => (N n : ℝ) / (n : ℝ)
  let k : ℕ → ℝ := fun n => ((N n - n : ℕ) : ℝ) / (n : ℝ)
  have hk : Tendsto k atTop (𝓝 0) := by
    have h := hRatio.sub_const 1
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [hN, eventually_gt_atTop 0] with n hnN hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp [k]
    rw [Nat.cast_sub hnN]
    field_simp
  have hklog : Tendsto (fun n => k n * Real.log (n : ℝ)) atTop (𝓝 0) := by
    convert hGap using 1
    funext n
    dsimp [k]
    ring
  have hlogR : Tendsto (fun n => Real.log (R n)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hRatio
    simpa only [Real.log_one, R] using h
  let G : ℕ → ℝ := fun n =>
    (k n * Real.log (n : ℝ) + R n * Real.log (R n)) / ((d : ℝ) - 1) +
      k n * Real.log (unrestrictedSinglePointMass sigma c).toReal
  have hG : Tendsto G atTop (𝓝 0) := by
    have h := ((hklog.add (hRatio.mul hlogR)).div_const ((d : ℝ) - 1)).add
      (hk.mul_const (Real.log (unrestrictedSinglePointMass sigma c).toReal))
    simpa only [zero_mul, one_mul, zero_add, add_zero, zero_div, G, R, k] using h
  have htest : Tendsto (fun n => R n * (L - δ / 2) - G n) atTop (𝓝 (L - δ / 2)) := by
    have h := (hRatio.mul_const (L - δ / 2)).sub hG
    simpa only [one_mul, sub_zero, R] using h
  have htestLower : ∀ᶠ n : ℕ in atTop, L - δ < R n * (L - δ / 2) - G n :=
    htest.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hN, hLower (δ / 2) (half_pos hδ), htestLower,
    eventually_gt_atTop 0] with n hnN hnLower hnTest hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N n := by exact_mod_cast lt_of_lt_of_le hn hnN
  have hRpos : 0 < R n := div_pos hNR hnR
  have hRk : R n = k n + 1 := by
    dsimp [R, k]
    rw [Nat.cast_sub hnN]
    field_simp
    ring
  have hgapEq :
      ((R n * Real.log (N n : ℝ) - Real.log (n : ℝ)) / ((d : ℝ) - 1) +
        k n * Real.log (unrestrictedSinglePointMass sigma c).toReal) = G n := by
    have hlog : Real.log (R n) = Real.log (N n : ℝ) - Real.log (n : ℝ) :=
      Real.log_div hNR.ne' hnR.ne'
    dsimp only [G]
    rw [hlog]
    congr 2
    rw [hRk]
    ring
  have hcomp := normalizedPartitionLog_deletion hd n (N n) hn hnN sigma c hc
  change R n * normalizedPartitionLog (N n) sigma c -
    ((R n * Real.log (N n : ℝ) - Real.log (n : ℝ)) / ((d : ℝ) - 1) +
      k n * Real.log (unrestrictedSinglePointMass sigma c).toReal) ≤ _ at hcomp
  rw [hgapEq] at hcomp
  have hmul := mul_le_mul_of_nonneg_left hnLower hRpos.le
  linarith

end Antichain
