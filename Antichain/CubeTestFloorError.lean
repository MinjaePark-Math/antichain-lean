import Antichain.DistanceToFloor
import Antichain.FloorTilt

/-! Deterministic empirical-test comparison between actual cube points and their floor images. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def cubeTestOnFloor (g : CubePoint d →ᵇ ℝ) : FloorSpace (Fin d) →ᵇ ℝ :=
  g.compContinuous ⟨normalCDFFloorMap, normalCDFFloorMap_continuous⟩

omit [NeZero d] in
@[simp] theorem cubeTestOnFloor_apply (g : CubePoint d →ᵇ ℝ) (u : FloorSpace (Fin d)) :
    cubeTestOnFloor g u = g (normalCDFFloorMap u) := rfl

theorem limitingFloorLaw_normalCDFFloorMap :
    (limitingFloorLaw d).map normalCDFFloorMap = limitingAntichainMeasure (Fin d) := by
  rw [limitingFloorLaw, Measure.map_map normalCDFFloorMap_continuous.measurable
    scaledGaussianFloorMap_continuous.measurable]
  rfl

theorem cubeTestOnFloor_integral (g : CubePoint d →ᵇ ℝ) :
    (∫ u, cubeTestOnFloor g u ∂limitingFloorLaw d) =
      ∫ x, g x ∂limitingAntichainMeasure (Fin d) := by
  rw [← limitingFloorLaw_normalCDFFloorMap,
    integral_map normalCDFFloorMap_continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  rfl

omit [NeZero d] in
theorem isCompact_cubePointSet : IsCompact (cubePointSet d) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

omit [NeZero d] in
theorem gaussianToCubePoint_mem_cube (g : CubePoint d) : gaussianToCubePoint d g ∈ cubePointSet d := by
  intro i _
  exact ⟨(normalCDF_mem_Ioo _).1.le, (normalCDF_mem_Ioo _).2.le⟩

omit [NeZero d] in
theorem normalCDFFloorMap_mem_cube (u : FloorSpace (Fin d)) : normalCDFFloorMap u ∈ cubePointSet d := by
  intro i _
  exact ⟨(normalCDF_mem_Ioo _).1.le, (normalCDF_mem_Ioo _).2.le⟩

/-- Uniform continuity on the actual compact cube gives a quadratic-height error,
uniformly over every input Gaussian vector. -/
theorem cubeTest_point_floor_error (g : CubePoint d →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : CubePoint d,
      |g (gaussianToCubePoint d G) - cubeTestOnFloor g (actualFloor G)| ≤
        ε + C * actualHeight G ^ 2 := by
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_cubePointSet.uniformContinuousOn_of_continuous g.continuous.continuousOn) ε hε
  let η := δ / ((normalCDFLipschitzConstant : ℝ) + 1)
  have hη : 0 < η := div_pos hδ (by positivity)
  let C := 2 * ‖g‖ / η ^ 2
  have hC : 0 ≤ C := div_nonneg (by positivity) (sq_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro G
  by_cases hsmall : |actualHeight G| < η
  · have hdist : dist (gaussianToCubePoint d G) (normalCDFFloorMap (actualFloor G)) < δ := by
      have hηeq : ((normalCDFLipschitzConstant : ℝ) + 1) * η = δ := by
        dsimp [η]
        field_simp
      have hh := mul_lt_mul_of_pos_left hsmall
        (show (0 : ℝ) < (normalCDFLipschitzConstant : ℝ) + 1 by positivity)
      have hd := gaussianToCubePoint_dist_floor_le_height G
      nlinarith [abs_nonneg (actualHeight G)]
    have hh := huc (gaussianToCubePoint d G) (gaussianToCubePoint_mem_cube G)
      (normalCDFFloorMap (actualFloor G)) (normalCDFFloorMap_mem_cube _) hdist
    rw [Real.dist_eq] at hh
    exact hh.le.trans (le_add_of_nonneg_right (mul_nonneg hC (sq_nonneg _)))
  · have hheight : η ^ 2 ≤ actualHeight G ^ 2 :=
      ((sq_le_sq₀ hη.le (abs_nonneg _)).mpr (le_of_not_gt hsmall)).trans_eq (sq_abs _)
    have hlarge : 2 * ‖g‖ ≤ C * actualHeight G ^ 2 := by
      calc
        _ = C * η ^ 2 := by dsimp [C]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hheight hC
    have hh := g.dist_le_two_norm (gaussianToCubePoint d G) (normalCDFFloorMap (actualFloor G))
    rw [Real.dist_eq] at hh
    exact hh.trans (hlarge.trans (le_add_of_nonneg_left hε.le))

/-- The exact empirical-test error needed to pass from floor convergence to cube convergence. -/
theorem cubeTest_empirical_floor_error (g : CubePoint d →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ G : CubeSample n d,
      |(∑ j, g (gaussianToCubePoint d (G j))) / n -
        (∑ j, cubeTestOnFloor g (actualFloor (G j))) / n| ≤
          ε + C * ((∑ j, actualHeight (G j) ^ 2) / n) := by
  obtain ⟨C, hC, hpoint⟩ := cubeTest_point_floor_error g hε
  refine ⟨C, hC, ?_⟩
  intro n hn G
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = |∑ j, (g (gaussianToCubePoint d (G j)) - cubeTestOnFloor g (actualFloor (G j)))| / n := by
      rw [Finset.sum_sub_distrib, ← sub_div, abs_div, abs_of_pos hnR]
    _ ≤ (∑ j, |g (gaussianToCubePoint d (G j)) - cubeTestOnFloor g (actualFloor (G j))|) / n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ (∑ j, (ε + C * actualHeight (G j) ^ 2)) / n :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ ↦ hpoint (G j))) hnR.le
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]
      field_simp

theorem cubeTest_empirical_error_from_floor (g : CubePoint d →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ G : CubeSample n d,
      |(∑ j, g (gaussianToCubePoint d (G j))) / n -
        (∫ x, g x ∂limitingAntichainMeasure (Fin d))| ≤
          ε + C * ((∑ j, actualHeight (G j) ^ 2) / n) +
            |(∑ j, cubeTestOnFloor g (actualFloor (G j))) / n -
              (∫ u, cubeTestOnFloor g u ∂limitingFloorLaw d)| := by
  obtain ⟨C, hC, herr⟩ := cubeTest_empirical_floor_error g hε
  refine ⟨C, hC, ?_⟩
  intro n hn G
  rw [cubeTestOnFloor_integral]
  exact (abs_sub_le _ ((∑ j, cubeTestOnFloor g (actualFloor (G j))) / n) _).trans
    (add_le_add_right (herr n hn G) _)

end Antichain
