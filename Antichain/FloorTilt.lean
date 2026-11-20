import Antichain.FloorIntegralApproximation
import Antichain.BoundedMoment

/-! The actual limiting floor probability and its exact exponential-tilt identity. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def limitingFloorLaw (d : ℕ) [NeZero d] : Measure (FloorSpace (Fin d)) :=
  (standardGaussianProduct (Fin d)).map scaledGaussianFloorMap

instance limitingFloorLaw_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (limitingFloorLaw d) :=
  Measure.isProbabilityMeasure_map scaledGaussianFloorMap_continuous.measurable.aemeasurable

theorem limitingFloorLaw_density (hd : 2 ≤ d) :
    limitingFloorLaw d = floorVolume.withDensity
      (fun u : FloorSpace (Fin d) => ENNReal.ofReal (limitingFloorDensity u)) := by
  exact scaledProjectedGaussian_eq_withDensity_limitingFloorDensity (by simpa using hd)

theorem limitingFloorLaw_mgf_identity (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) :
    mgf (sigma : FloorSpace (Fin d) → ℝ) (limitingFloorLaw d)
      (((d : ℝ) - 1) / (d : ℝ)) =
      (∫ u : FloorSpace (Fin d), weightedFloorDensity sigma u ^ (((d : ℝ) - 1) / (d : ℝ))) /
        (∫ u : FloorSpace (Fin d), standardFloorDensity u ^ (((d : ℝ) - 1) / (d : ℝ))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hv : 0 < (d : ℝ) / ((d : ℝ) - 1) := div_pos (by linarith) (by linarith)
  have hpos (u : FloorSpace (Fin d)) : 0 ≤ limitingFloorDensity u := by
    simpa only [limitingFloorDensity, Fintype.card_fin] using (radialGaussianDensity_pos hv u).le
  have hrho (u : FloorSpace (Fin d)) : limitingFloorDensity u =
      standardFloorDensity u ^ (((d : ℝ) - 1) / (d : ℝ)) /
        (∫ v : FloorSpace (Fin d), standardFloorDensity v ^ (((d : ℝ) - 1) / (d : ℝ))) := by
    simpa only [Fintype.card_fin] using
      limitingFloorDensity_eq_normalized_standard_power (by simpa using hd) u
  have hcont : Continuous (limitingFloorDensity (ι := Fin d)) :=
    radialGaussianDensity_continuous _
  unfold mgf
  rw [limitingFloorLaw_density hd,
    integral_withDensity_eq_integral_toReal_smul
      hcont.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun u : FloorSpace (Fin d) =>
      (ENNReal.ofReal (limitingFloorDensity u)).toReal •
        Real.exp ((((d : ℝ) - 1) / (d : ℝ)) * sigma u)) =
      (fun u : FloorSpace (Fin d) =>
        weightedFloorDensity sigma u ^ (((d : ℝ) - 1) / (d : ℝ)) /
          (∫ v : FloorSpace (Fin d), standardFloorDensity v ^ (((d : ℝ) - 1) / (d : ℝ)))) := by
    funext u
    rw [ENNReal.toReal_ofReal (hpos u), smul_eq_mul, hrho]
    unfold weightedFloorDensity
    have hstd : 0 ≤ standardFloorDensity u :=
      (radialGaussianDensity_pos (by norm_num : (0 : ℝ) < 1) u).le
    rw [Real.mul_rpow hstd
      (Real.exp_nonneg _), ← Real.exp_mul]
    rw [mul_comm (sigma u) (((d : ℝ) - 1) / (d : ℝ))]
    ring
  rw [heq, integral_div]
  rfl

end Antichain
