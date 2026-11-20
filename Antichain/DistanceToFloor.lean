import Antichain.NormalCDFLipschitz
import Antichain.GaussianFloorLaw
import Antichain.GaussianWeighted

/-! Actual Gaussian samples and their floor images are close when their heights are small. -/

noncomputable section

namespace Antichain

open Set Finset
open scoped Topology NNReal

/-- This statement uses the actual finite-Pi supremum metric. -/
theorem coordinatewiseNormalCDF_pi_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith normalCDFLipschitzConstant (fun x : ι → ℝ ↦ fun i ↦ normalCDF (x i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg normalCDFLipschitzConstant.coe_nonneg dist_nonneg)).mpr
  intro i
  exact (normalCDF_lipschitz.dist_le_mul (x i) (y i)).trans
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) normalCDFLipschitzConstant.coe_nonneg)

theorem gaussianToCubePoint_pi_lipschitz (d : ℕ) :
    LipschitzWith normalCDFLipschitzConstant (gaussianToCubePoint d) :=
  coordinatewiseNormalCDF_pi_lipschitz

variable {d : ℕ} [NeZero d]

theorem gaussian_coordinate_sub_actualFloor (g : CubePoint d) (i : Fin d) :
    g i - (actualFloor g).val i = actualHeight g / Real.sqrt (d : ℝ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  change g i - (g i - (∑ j, g j) / (Fintype.card (Fin d) : ℝ)) = _
  rw [Fintype.card_fin]
  rw [actualHeight, div_div, ← pow_two, Real.sq_sqrt hd.le]
  ring

/-- The exact supremum-metric error, including the source's 1/sqrt(d) factor. -/
theorem gaussianToCubePoint_dist_floor_le (g : CubePoint d) :
    dist (gaussianToCubePoint d g) (normalCDFFloorMap (actualFloor g)) ≤
      (normalCDFLipschitzConstant : ℝ) * |actualHeight g| / Real.sqrt (d : ℝ) := by
  have hd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
  apply (dist_pi_le_iff (div_nonneg (mul_nonneg normalCDFLipschitzConstant.coe_nonneg
    (abs_nonneg _)) hd.le)).mpr
  intro i
  have h := normalCDF_lipschitz.dist_le_mul (g i) ((actualFloor g).val i)
  change dist (normalCDF (g i)) (normalCDF ((actualFloor g).val i)) ≤ _
  simp only [Real.dist_eq] at h ⊢
  rw [gaussian_coordinate_sub_actualFloor g i, abs_div, abs_of_pos hd] at h
  simpa only [mul_div_assoc] using h

theorem gaussianToCubePoint_dist_floor_le_height (g : CubePoint d) :
    dist (gaussianToCubePoint d g) (normalCDFFloorMap (actualFloor g)) ≤
      (normalCDFLipschitzConstant : ℝ) * |actualHeight g| := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hs : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := (Real.one_le_sqrt).mpr hd
  exact (gaussianToCubePoint_dist_floor_le g).trans
    (div_le_self (mul_nonneg normalCDFLipschitzConstant.coe_nonneg (abs_nonneg _)) hs)

theorem euclidean_dist_actualFloor_eq_height (g : CubePoint d) :
    dist (WithLp.toLp 2 g) (actualFloor g).val = |actualHeight g| := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have heq : ‖WithLp.toLp 2 g - (actualFloor g).val‖ ^ 2 = |actualHeight g| ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    simp_rw [gaussian_coordinate_sub_actualFloor g]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      div_pow, Real.sq_sqrt hd.le]
    field_simp
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (WithLp.toLp 2 g - (actualFloor g).val), abs_nonneg (actualHeight g)]

/-- The same comparison in the native Euclidean L2 metric. -/
theorem euclideanNormalCDF_dist_floor_le (g : CubePoint d) :
    dist (euclideanNormalCDF (WithLp.toLp 2 g)) (euclideanNormalCDFFloorMap (actualFloor g)) ≤
      (normalCDFLipschitzConstant : ℝ) * |actualHeight g| := by
  have h := euclideanNormalCDF_lipschitz.dist_le_mul (WithLp.toLp 2 g) (actualFloor g).val
  rwa [euclidean_dist_actualFloor_eq_height] at h

/- A deterministic squared-height bound for the fraction of large-height labels. -/
omit [NeZero d] in
theorem largeHeight_count_mul_sq_le {n : ℕ} (g : CubeSample n d) {η : ℝ} (hη : 0 < η) :
    ((Finset.univ.filter (fun j ↦ η ≤ |actualHeight (g j)|)).card : ℝ) * η ^ 2 ≤
      ∑ j, actualHeight (g j) ^ 2 := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j ↦ η ≤ |actualHeight (g j)|), η ^ 2 := by simp
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ η ≤ |actualHeight (g j)|), actualHeight (g j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := (Finset.mem_filter.mp hj).2
      exact (sq_le_sq₀ hη.le (abs_nonneg _)).mpr hh |>.trans_eq (sq_abs _)
    _ ≤ ∑ j, actualHeight (g j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ ↦ sq_nonneg _)

end Antichain
