import Antichain.GaussianFloorLaw

/-! Exact standard Gaussian and uniform marginals of the actual limiting law. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Any actual unit linear form of the independent standard normal vector is standard normal. -/
omit [Nonempty ι] in
theorem standardGaussianProduct_map_unitLinearForm
    (c : EuclideanSpace ℝ ι) (hc : ‖c‖ = 1) :
    (standardGaussianProduct ι).map (fun y : ι → ℝ ↦ ∑ j, c j * y j) = gaussianReal 0 1 := by
  have hmeas : Measurable (fun y : ι → ℝ ↦ ∑ j, c j * y j) := by fun_prop
  letI : IsProbabilityMeasure ((standardGaussianProduct ι).map
      (fun y : ι → ℝ ↦ ∑ j, c j * y j)) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  have heq : charFun ((standardGaussianProduct ι).map (fun y : ι → ℝ ↦ ∑ j, c j * y j)) t =
      charFun ((standardGaussianProduct ι).map (WithLp.toLp 2)) (t • c) := by
    simp only [charFun_apply]
    rw [integral_map hmeas.aemeasurable (by fun_prop),
      integral_map (by fun_prop : AEMeasurable (WithLp.toLp 2) (standardGaussianProduct ι)) (by fun_prop)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    have hi : inner ℝ (∑ j, c j * y j) t = inner ℝ (WithLp.toLp 2 y) (t • c) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.smul_apply,
        smul_eq_mul, PiLp.toLp_apply]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    dsimp only
    rw [hi]
  rw [heq, charFun_standardGaussianProduct, charFun_gaussianReal]
  rw [norm_smul, hc, mul_one, Real.norm_eq_abs]
  push_cast
  rw [← Complex.ofReal_pow, sq_abs]
  push_cast
  simp only [mul_zero, zero_mul, one_mul, zero_sub]
  congr 1
  ring

def scaledCoordinateCoefficient (i : ι) : EuclideanSpace ℝ ι := by
  classical
  exact WithLp.toLp 2 (fun j ↦ floorGaussianScale ι * ((if j = i then 1 else 0) -
    1 / (Fintype.card ι : ℝ)))

omit [Nonempty ι] in
theorem scaledCoordinateCoefficient_norm (hd : 2 ≤ Fintype.card ι) (i : ι) :
    ‖scaledCoordinateCoefficient i‖ = 1 := by
  classical
  let D : ℝ := Fintype.card ι
  have hD : (2 : ℝ) ≤ D := by dsimp [D]; exact_mod_cast hd
  have hDn : D ≠ 0 := by linarith
  have hD1n : D - 1 ≠ 0 := by linarith
  have hs : floorGaussianScale ι ^ 2 = D / (D - 1) :=
    Real.sq_sqrt (div_pos (by linarith : 0 < D) (by linarith : 0 < D - 1)).le
  have hsum : (∑ j : ι, ((if j = i then (1 : ℝ) else 0) - 1 / D) ^ 2) = (D - 1) / D := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [ite_pow, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change 1 - 2 * 1 * (1 / D) + D * (1 / D) ^ 2 = (D - 1) / D
    field_simp
    ring
  have hnorm := EuclideanSpace.norm_sq_eq (scaledCoordinateCoefficient i)
  simp only [Real.norm_eq_abs, sq_abs] at hnorm
  change ‖scaledCoordinateCoefficient i‖ ^ 2 =
    ∑ j : ι, (floorGaussianScale ι * ((if j = i then 1 else 0) - 1 / D)) ^ 2 at hnorm
  simp_rw [mul_pow] at hnorm
  rw [← Finset.mul_sum, hsum, hs] at hnorm
  have hnormsq : ‖scaledCoordinateCoefficient i‖ ^ 2 = 1 := by
    rw [hnorm]
    field_simp
  nlinarith [norm_nonneg (scaledCoordinateCoefficient i)]

omit [Nonempty ι] in
theorem scaledCenteredCoordinates_eq_linearForm (y : ι → ℝ) (i : ι) :
    scaledCenteredCoordinates y i = ∑ j, scaledCoordinateCoefficient i j * y j := by
  classical
  change floorGaussianScale ι * (y i - (∑ j, y j) / (Fintype.card ι : ℝ)) =
    ∑ j, floorGaussianScale ι * ((if j = i then 1 else 0) - 1 / (Fintype.card ι : ℝ)) * y j
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ← Finset.mul_sum]
  ring

/- Each coordinate of exactly the source's projected/rescaled F* is standard normal. -/
omit [Nonempty ι] in
theorem scaledCenteredCoordinate_map_standardGaussian (hd : 2 ≤ Fintype.card ι) (i : ι) :
    (standardGaussianProduct ι).map (fun y ↦ scaledCenteredCoordinates y i) = gaussianReal 0 1 := by
  simp_rw [scaledCenteredCoordinates_eq_linearForm]
  exact standardGaussianProduct_map_unitLinearForm _ (scaledCoordinateCoefficient_norm hd i)

theorem scaledGaussianFloor_coordinate_map (hd : 2 ≤ Fintype.card ι) (i : ι) :
    (standardGaussianProduct ι).map (fun y ↦ (scaledGaussianFloorMap y).val i) = gaussianReal 0 1 :=
  scaledCenteredCoordinate_map_standardGaussian hd i

/- Each actual cube marginal of μ* is exactly restricted uniform Lebesgue measure. -/
omit [Nonempty ι] in
theorem limitingAntichainMeasure_coordinate_map (hd : 2 ≤ Fintype.card ι) (i : ι) :
    (limitingAntichainMeasure ι).map (fun x ↦ x i) = cubeCoordinateLaw := by
  rw [limitingAntichainMeasure, Measure.map_map (by fun_prop) limitingCubeMap_continuous.measurable]
  have heq : (fun x : ι → ℝ ↦ x i) ∘ limitingCubeMap =
      normalCDF ∘ (fun y : ι → ℝ ↦ scaledCenteredCoordinates y i) := rfl
  rw [heq, ← Measure.map_map normalCDF_continuous.measurable (by unfold scaledCenteredCoordinates; fun_prop),
    scaledCenteredCoordinate_map_standardGaussian hd i, normalCDF_map_gaussianReal]

omit [Nonempty ι] in
theorem measurableSet_limiting_closed_cube :
    MeasurableSet {x : ι → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_Icc.preimage (measurable_pi_apply i))

omit [Nonempty ι] in
theorem limitingAntichainMeasure_mem_closed_cube :
    ∀ᵐ x ∂limitingAntichainMeasure ι, ∀ i, x i ∈ Icc (0 : ℝ) 1 := by
  unfold limitingAntichainMeasure
  apply (ae_map_iff limitingCubeMap_continuous.measurable.aemeasurable
    measurableSet_limiting_closed_cube).mpr
  exact Filter.Eventually.of_forall (fun y i ↦ ⟨(normalCDF_mem_Ioo _).1.le, (normalCDF_mem_Ioo _).2.le⟩)

omit [Nonempty ι] in
theorem limitingAntichainMeasure_closed_cube_mass :
    limitingAntichainMeasure ι {x | ∀ i, x i ∈ Icc (0 : ℝ) 1} = 1 := by
  exact (mem_ae_iff_prob_eq_one measurableSet_limiting_closed_cube).mp limitingAntichainMeasure_mem_closed_cube

omit [Nonempty ι] in
theorem limitingAntichainMeasure_support_subset_closed_cube :
    (limitingAntichainMeasure ι).support ⊆ {x | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
  apply Measure.support_subset_of_isClosed
  · simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i ↦ isClosed_Icc.preimage (continuous_apply i))
  · exact limitingAntichainMeasure_mem_closed_cube

/- The genuine probability, closed-cube support, and exact uniform marginal properties. -/
omit [Nonempty ι] in
theorem limitingAntichainMeasure_permuton_properties (hd : 2 ≤ Fintype.card ι) :
    IsProbabilityMeasure (limitingAntichainMeasure ι) ∧
    limitingAntichainMeasure ι {x | ∀ i, x i ∈ Icc (0 : ℝ) 1} = 1 ∧
    ∀ i : ι, (limitingAntichainMeasure ι).map (fun x ↦ x i) = cubeCoordinateLaw :=
  ⟨inferInstance, limitingAntichainMeasure_closed_cube_mass, limitingAntichainMeasure_coordinate_map hd⟩

end Antichain
