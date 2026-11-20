import Antichain.PartitionDeletion
import Antichain.GaussianFloorHeightLaw
import Antichain.OneTileGaussian

/-! The exact unrestricted mass in the sample-size comparison and Poisson law. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

theorem standardGaussian_quadratic_moment (c : ℝ) :
    (∫ h : ℝ, Real.exp (c * h ^ 2) ∂gaussianReal 0 1) =
      1 / Real.sqrt (1 - 2 * c) := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun h : ℝ => (gaussianPDF 0 1 h).toReal • Real.exp (c * h ^ 2)) =
      (fun h : ℝ => (2 * Real.pi) ^ (-(1 : ℝ) / 2) *
        Real.exp (-((1 / 2 : ℝ) - c) * h ^ 2)) := by
    funext h
    simp only [toReal_gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one,
      sub_zero, smul_eq_mul, mul_assoc, ← Real.exp_add]
    have hn : (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi) ^ (-(1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      congr 1
      norm_num
    rw [hn]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_gaussian]
  have h := gaussian_coefficient_identity 1 (by omega) c
  simpa [commonHeightGaussianCoefficient] using h

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem floorWeight_integrable (sigma : FloorSpace (Fin d) →ᵇ ℝ) :
    Integrable (fun u : FloorSpace (Fin d) => standardFloorDensity u * Real.exp (sigma u)) := by
  have hi := (radialGaussianDensity_integrable (V := FloorSpace (Fin d))
    (by norm_num : (0 : ℝ) < 1)).const_mul (Real.exp ‖sigma‖)
  apply hi.mono'
  · exact ((radialGaussianDensity_continuous 1).mul
      (Real.continuous_exp.comp sigma.continuous)).measurable.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    have hu : sigma u ≤ ‖sigma‖ := le_trans (le_abs_self _) (by
      simpa only [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm sigma u)
    have hdensity := (radialGaussianDensity_pos (V := FloorSpace (Fin d))
      (by norm_num : (0 : ℝ) < 1) u).le
    change ‖radialGaussianDensity (FloorSpace (Fin d)) 1 u * Real.exp (sigma u)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg hdensity (Real.exp_nonneg _))]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) hdensity).trans_eq (mul_comm _ _)

theorem singlePointWeight_integral_eq_mass (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    (∫ g, singlePointWeight sigma c g ∂gaussianPointLaw d) =
      (unrestrictedSinglePointMass sigma c).toReal :=
  integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
    (singlePointWeight_continuous sigma c).measurable.aestronglyMeasurable

theorem singlePointWeight_integrable (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    Integrable (singlePointWeight sigma c) (gaussianPointLaw d) := by
  constructor
  · exact (singlePointWeight_continuous sigma c).measurable.aestronglyMeasurable
  · exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))).mpr
      (unrestrictedSinglePointMass_lt_top sigma c hc)

/-- Equation (4.8)'s actual one-point mass, in ordinary real form. -/
theorem unrestrictedSinglePointMass_exact (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    (unrestrictedSinglePointMass sigma c).toReal =
      (∫ u : FloorSpace (Fin d), standardFloorDensity u * Real.exp (sigma u)) /
        Real.sqrt (1 - 2 * c) := by
  letI : IsProbabilityMeasure (radialGaussianMeasure (FloorSpace (Fin d)) 1) :=
    radialGaussianMeasure_isProbabilityMeasure (by norm_num : (0 : ℝ) < 1)
  let Q : FloorSpace (Fin d) × ℝ → ℝ := fun p => Real.exp (sigma p.1 + c * p.2 ^ 2)
  have hmap : MeasurePreserving (gaussianFloorHeightMap (ι := Fin d))
      (gaussianPointLaw d)
      ((radialGaussianMeasure (FloorSpace (Fin d)) 1).prod (gaussianReal 0 1)) :=
    ⟨gaussianFloorHeightMap_continuous.measurable, gaussianFloorHeightMap_law⟩
  rw [← singlePointWeight_integral_eq_mass]
  have hcomp : (Q ∘ gaussianFloorHeightMap (ι := Fin d)) = singlePointWeight sigma c := by
    funext g
    simp only [Function.comp_apply, Q, singlePointWeight, gaussianFloorHeightMap,
      gaussianHeightMap, actualHeight, Fintype.card_fin, gaussianFloorMap, actualFloor]
  rw [← hcomp]
  change (∫ g, Q (gaussianFloorHeightMap g) ∂gaussianPointLaw d) = _
  rw [← integral_map hmap.measurable.aemeasurable
    (show AEStronglyMeasurable Q ((gaussianPointLaw d).map gaussianFloorHeightMap) from
      (show Continuous Q by dsimp [Q]; fun_prop).measurable.aestronglyMeasurable), hmap.map_eq]
  simp only [Q, Real.exp_add]
  rw [integral_prod_mul (fun u : FloorSpace (Fin d) => Real.exp (sigma u))
    (fun h : ℝ => Real.exp (c * h ^ 2)), standardGaussian_quadratic_moment]
  have hf : (∫ u : FloorSpace (Fin d), Real.exp (sigma u)
      ∂radialGaussianMeasure (FloorSpace (Fin d)) 1) =
      ∫ u : FloorSpace (Fin d), standardFloorDensity u * Real.exp (sigma u) := by
    rw [radialGaussianMeasure,
      integral_withDensity_eq_integral_toReal_smul
        (radialGaussianDensity_continuous 1).measurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by
      dsimp only
      rw [ENNReal.toReal_ofReal (radialGaussianDensity_pos
        (by norm_num : (0 : ℝ) < 1) u).le]
      rfl)
  rw [hf]
  ring

theorem unrestrictedSinglePointMass_eq_ofReal (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    unrestrictedSinglePointMass sigma c = ENNReal.ofReal
      ((∫ u : FloorSpace (Fin d), standardFloorDensity u * Real.exp (sigma u)) /
        Real.sqrt (1 - 2 * c)) := by
  rw [← unrestrictedSinglePointMass_exact]
  exact (ENNReal.ofReal_toReal (unrestrictedSinglePointMass_lt_top sigma c hc).ne).symm

/-- Exact equation (5.11), including its genuine one-point Gaussian mass. -/
theorem weightedPartition_deletion_lower_exact (hd : 2 ≤ d) (n N : ℕ) (hnN : n ≤ N)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    (((∫ u : FloorSpace (Fin d), standardFloorDensity u * Real.exp (sigma u)) /
        Real.sqrt (1 - 2 * c)) ^ (N - n))⁻¹ * weightedPartition N sigma c ≤
      weightedPartition n sigma c := by
  simpa only [unrestrictedSinglePointMass_exact] using
    weightedPartition_deletion_lower hd n N hnN sigma c hc

end Antichain
