import Antichain.WeightedLimit
import Antichain.FloorTilt

/-! Actual conditional logarithmic exponential moments under the antichain law. -/

noncomputable section

namespace Antichain

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

theorem weightedRateValue_sub_zero (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) :
    weightedRateValue d hd sigma - weightedRateValue d hd (0 : FloorSpace (Fin d) →ᵇ ℝ) =
      (d : ℝ) / ((d : ℝ) - 1) *
        Real.log (mgf (sigma : FloorSpace (Fin d) → ℝ) (limitingFloorLaw d)
          (((d : ℝ) - 1) / (d : ℝ))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < ((d : ℝ) - 1) / (d : ℝ) := div_pos (by linarith) (by linarith)
  have hI := weightedFloorDensity_rpow_integral_pos sigma hp
  have hI0 : 0 < ∫ u : FloorSpace (Fin d), standardFloorDensity u ^
      (((d : ℝ) - 1) / (d : ℝ)) := by
    simpa [weightedFloorDensity] using
      weightedFloorDensity_rpow_integral_pos (0 : FloorSpace (Fin d) →ᵇ ℝ) hp
  rw [limitingFloorLaw_mgf_identity hd sigma, Real.log_div hI.ne' hI0.ne']
  unfold weightedRateValue
  simp only [weightedFloorDensity, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero, mul_one]
  ring

theorem weightedPartition_ratio_log_limit (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Tendsto (fun n : ℕ => Real.log (weightedPartition n sigma c / antichainProbability n d) /
      (n : ℝ)) atTop (𝓝 ((d : ℝ) / ((d : ℝ) - 1) *
        Real.log (mgf (sigma : FloorSpace (Fin d) → ℝ) (limitingFloorLaw d)
          (((d : ℝ) - 1) / (d : ℝ))))) := by
  have h := (weightedPartition_rate_limit hd H sigma c hc).sub
    (weightedPartition_rate_limit hd H (0 : FloorSpace (Fin d) →ᵇ ℝ) 0 (by norm_num))
  rw [weightedRateValue_sub_zero hd sigma] at h
  apply h.congr
  intro n
  unfold normalizedPartitionLog
  rw [weightedPartition_zero,
    Real.log_div (weightedPartition_pos n sigma c hc hd).ne' (antichainProbability_pos n d hd).ne']
  ring

/-- Equation (2.4), for the genuine conditional Gaussian sample and actual F*. -/
theorem conditional_gaussianWeight_log_limit (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Tendsto (fun n : ℕ => Real.log
      (∫ g, gaussianWeight n sigma c g ∂gaussianAntichainLaw n d) / (n : ℝ)) atTop
      (𝓝 ((d : ℝ) / ((d : ℝ) - 1) *
        Real.log (mgf (sigma : FloorSpace (Fin d) → ℝ) (limitingFloorLaw d)
          (((d : ℝ) - 1) / (d : ℝ))))) := by
  simpa only [conditional_gaussianWeight_integral_eq_ratio] using
    weightedPartition_ratio_log_limit hd H sigma c hc

def totalSquaredHeight (n : ℕ) (g : CubeSample n d) : ℝ :=
  ∑ j, actualHeight (g j) ^ 2

theorem gaussianWeight_zero_eq_height_exp (n : ℕ) (c : ℝ) (g : CubeSample n d) :
    gaussianWeight n (0 : FloorSpace (Fin d) →ᵇ ℝ) c g =
      Real.exp (c * totalSquaredHeight n g) := by
  unfold gaussianWeight gaussianWeightExponent totalSquaredHeight
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, zero_add, Finset.mul_sum]

theorem conditional_height_exp_log_limit (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (c : ℝ) (hc : c < 1 / 2) :
    Tendsto (fun n : ℕ => Real.log
      (∫ g, Real.exp (c * totalSquaredHeight n g) ∂gaussianAntichainLaw n d) / (n : ℝ))
      atTop (𝓝 0) := by
  have h := conditional_gaussianWeight_log_limit hd H (0 : FloorSpace (Fin d) →ᵇ ℝ) c hc
  simpa only [gaussianWeight_zero_eq_height_exp, BoundedContinuousFunction.coe_zero,
    mgf_zero_fun, measureReal_univ_eq_one, Real.log_one, mul_zero] using h

end Antichain
