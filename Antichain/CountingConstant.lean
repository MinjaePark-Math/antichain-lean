import Antichain.WeightedLimit

/-! The explicit Gaussian contribution to the paper's counting constant. -/

noncomputable section

namespace Antichain

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

theorem weightedRateValue_zero_explicit (hd : 2 ≤ d) :
    weightedRateValue d hd (0 : FloorSpace (Fin d) →ᵇ ℝ) =
      localGammaConstant d hd + (d : ℝ) / 2 * Real.log ((d : ℝ) / ((d : ℝ) - 1)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hm0 : (d : ℝ) - 1 ≠ 0 := by linarith
  let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
  have hp : 0 < p := by dsimp [p]; exact div_pos (by linarith) (by linarith)
  have hbase : 0 < 2 * Real.pi := by positivity
  have hk : (Module.finrank ℝ (FloorSpace (Fin d)) : ℝ) = (d : ℝ) - 1 := by
    rw [finrank_floorSpace, Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have hI : (∫ u : FloorSpace (Fin d), standardFloorDensity u ^ p) =
      ((2 * Real.pi) ^ (-((d : ℝ) - 1) / 2)) ^ p *
        (2 * Real.pi / p) ^ (((d : ℝ) - 1) / 2) := by
    simpa only [standardFloorDensity, mul_one, hk] using
      integral_radialGaussianDensity_rpow (V := FloorSpace (Fin d)) (by norm_num : (0 : ℝ) < 1) hp
  unfold weightedRateValue
  simp only [weightedFloorDensity, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
    Real.exp_zero, mul_one]
  change localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log
        (∫ u : FloorSpace (Fin d), standardFloorDensity u ^ p) = _
  rw [hI, Real.log_mul (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hbase _) _).ne'
      (Real.rpow_pos_of_pos (div_pos hbase hp) _).ne',
    Real.log_rpow (Real.rpow_pos_of_pos hbase _), Real.log_rpow hbase,
    Real.log_rpow (div_pos hbase hp), Real.log_div hbase.ne' hp.ne']
  have hq : (d : ℝ) / ((d : ℝ) - 1) = p⁻¹ := by dsimp [p]; field_simp
  conv_rhs => rw [hq, Real.log_inv]
  dsimp [p]
  field_simp
  ring

theorem antichain_normalized_log_limit_explicit (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) :
    Tendsto (fun n : ℕ => Real.log (antichainProbability n d) / (n : ℝ) +
      Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop
      (𝓝 (localGammaConstant d hd + (d : ℝ) / 2 * Real.log ((d : ℝ) / ((d : ℝ) - 1)))) := by
  have h := weightedPartition_rate_limit hd H (0 : FloorSpace (Fin d) →ᵇ ℝ) 0 (by norm_num)
  rw [weightedRateValue_zero_explicit hd] at h
  simpa only [normalizedPartitionLog, weightedPartition_zero] using h

end Antichain
