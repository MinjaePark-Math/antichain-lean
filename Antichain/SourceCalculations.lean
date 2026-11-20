import Antichain.CountingConstant
import Antichain.RankCounting

/-! Literal calculations stated in the introductory remarks. -/

noncomputable section

namespace Antichain

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

/-- The exact simplified Gaussian power integral printed in Remark 1.4. -/
theorem standardFloorDensity_power_integral_explicit (hd : 2 ≤ d) :
    (∫ u : FloorSpace (Fin d), standardFloorDensity u ^
      (((d : ℝ) - 1) / (d : ℝ))) =
      (2 * Real.pi) ^ (((d : ℝ) - 1) / (2 * (d : ℝ))) *
        ((d : ℝ) / ((d : ℝ) - 1)) ^ (((d : ℝ) - 1) / 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hm0 : (d : ℝ) - 1 ≠ 0 := by linarith
  let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  have hbase : 0 < 2 * Real.pi := by positivity
  have hk : (Module.finrank ℝ (FloorSpace (Fin d)) : ℝ) = (d : ℝ) - 1 := by
    rw [finrank_floorSpace, Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  change (∫ u : FloorSpace (Fin d), standardFloorDensity u ^ p) = _
  rw [show (∫ u : FloorSpace (Fin d), standardFloorDensity u ^ p) =
    ((2 * Real.pi) ^ (-((d : ℝ) - 1) / 2)) ^ p *
      (2 * Real.pi / p) ^ (((d : ℝ) - 1) / 2) by
      simpa only [standardFloorDensity, mul_one, hk] using
        integral_radialGaussianDensity_rpow (V := FloorSpace (Fin d))
          (by norm_num : (0 : ℝ) < 1) hp]
  rw [← Real.rpow_mul hbase.le, show 2 * Real.pi / p = 2 * Real.pi * p⁻¹ from div_eq_mul_inv _ _,
    Real.mul_rpow hbase.le (inv_nonneg.mpr hp.le), ← mul_assoc,
    ← Real.rpow_add hbase]
  have hexp : -((d : ℝ) - 1) / 2 * p + ((d : ℝ) - 1) / 2 =
      ((d : ℝ) - 1) / (2 * (d : ℝ)) := by dsimp [p]; field_simp; ring
  have hinv : p⁻¹ = (d : ℝ) / ((d : ℝ) - 1) := by dsimp [p]; field_simp
  rw [hexp, hinv]

/-- Both printed constant calculations, with no geometric premise. -/
theorem counting_constant_calculation_source (hd : 2 ≤ d) :
    (∫ u : FloorSpace (Fin d), standardFloorDensity u ^
      (((d : ℝ) - 1) / (d : ℝ))) =
      (2 * Real.pi) ^ (((d : ℝ) - 1) / (2 * (d : ℝ))) *
        ((d : ℝ) / ((d : ℝ) - 1)) ^ (((d : ℝ) - 1) / 2) ∧
    weightedRateValue d hd (0 : FloorSpace (Fin d) →ᵇ ℝ) =
      localGammaConstant d hd + (d : ℝ) / 2 * Real.log ((d : ℝ) / ((d : ℝ) - 1)) :=
  ⟨standardFloorDensity_power_integral_explicit hd, weightedRateValue_zero_explicit hd⟩

end Antichain
