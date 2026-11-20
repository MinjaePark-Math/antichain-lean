import Antichain.LimitMarginals
import Antichain.NormalCDFLipschitz
import Antichain.WeakVanishingTest
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Topology.Order.MonotoneContinuity

/-! The actual limiting Gaussian interval law and its zero-error quantile predictor. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x := by
  let μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)
  letI : NoAtoms μ := noAtoms_gaussianReal one_ne_zero
  have hneg : μ.map (fun y : ℝ ↦ -y) = μ := by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hpre : (fun y : ℝ ↦ -y) ⁻¹' Iic (-x) = Ici x := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le_neg_iff]
  have hm : μ (Iic (-x)) = μ (Ioi x) := by
    calc
      _ = μ.map (fun y : ℝ ↦ -y) (Iic (-x)) := by rw [hneg]
      _ = μ (Ici x) := by rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]
      _ = μ (Ioi x) := measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := x)).symm
  change ProbabilityTheory.cdf μ (-x) = 1 - ProbabilityTheory.cdf μ x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, hm]
  change μ.real (Ioi x) = 1 - μ.real (Iic x)
  rw [← compl_Iic, measureReal_compl measurableSet_Iic]
  simp

theorem normalQuantile_image_open_interval : normalQuantile '' Ioo (0 : ℝ) 1 = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  exact ⟨normalCDF x, normalCDF_mem_Ioo x, normalQuantile_normalCDF x⟩

theorem normalQuantile_continuousAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt normalQuantile x := by
  apply normalQuantile_strictMonoOn.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds hx)
  rw [normalQuantile_image_open_interval]
  exact univ_mem

theorem normalQuantile_continuousOn : ContinuousOn normalQuantile (Ioo (0 : ℝ) 1) :=
  fun _ hx ↦ (normalQuantile_continuousAt hx).continuousWithinAt

def intervalCubeMap (x : CubePoint 3) : CubePoint 3 := ![x 0, 1 - x 2, x 1]

theorem intervalCubeMap_continuous : Continuous intervalCubeMap := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_const.sub (continuous_apply 2)
  · exact continuous_apply 1

def intervalGaussianPair (y : Fin 3 → ℝ) : ℝ × ℝ :=
  (scaledCenteredCoordinates y 0, scaledCenteredCoordinates y 1)

theorem intervalGaussianPair_continuous : Continuous intervalGaussianPair := by
  unfold intervalGaussianPair scaledCenteredCoordinates
  fun_prop

def tripleGaussianAssembly : (ℝ × (ℝ × ℝ)) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ),
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]

theorem tripleGaussianAssembly_law :
    ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))).map tripleGaussianAssembly =
      standardGaussianProduct (Fin 3) := by
  symm
  unfold standardGaussianProduct
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply tripleGaussianAssembly.continuous.measurable (MeasurableSet.univ_pi hs)]
  have heq : tripleGaussianAssembly ⁻¹' univ.pi s = (s 0) ×ˢ ((s 1) ×ˢ (s 2)) := by
    ext z
    constructor
    · intro h
      exact ⟨h 0 (mem_univ _), h 1 (mem_univ _), h 2 (mem_univ _)⟩
    · rintro ⟨h0, h1, h2⟩ i _
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
  rw [heq, Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_three]
  ring

instance standardGaussianProduct_three_isGaussian : IsGaussian (standardGaussianProduct (Fin 3)) := by
  rw [← tripleGaussianAssembly_law]
  infer_instance

def scaledCoordinateLinearMap (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 3, scaledCoordinateCoefficient i j • ContinuousLinearMap.proj j

@[simp] theorem scaledCoordinateLinearMap_apply (i : Fin 3) (y : Fin 3 → ℝ) :
    scaledCoordinateLinearMap i y = scaledCenteredCoordinates y i := by
  simp only [scaledCoordinateLinearMap, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact (scaledCenteredCoordinates_eq_linearForm y i).symm

def intervalGaussianPairLinearMap : (Fin 3 → ℝ) →L[ℝ] (ℝ × ℝ) :=
  (scaledCoordinateLinearMap 0).prod (scaledCoordinateLinearMap 1)

theorem intervalGaussianPairLinearMap_eq :
    (intervalGaussianPairLinearMap : (Fin 3 → ℝ) → ℝ × ℝ) = intervalGaussianPair := by
  funext y
  exact Prod.ext (scaledCoordinateLinearMap_apply 0 y) (scaledCoordinateLinearMap_apply 1 y)

def intervalGaussianPairLaw : Measure (ℝ × ℝ) :=
  (standardGaussianProduct (Fin 3)).map intervalGaussianPair

instance intervalGaussianPairLaw_isProbabilityMeasure : IsProbabilityMeasure intervalGaussianPairLaw :=
  Measure.isProbabilityMeasure_map intervalGaussianPair_continuous.measurable.aemeasurable

instance intervalGaussianPairLaw_isGaussian : IsGaussian intervalGaussianPairLaw := by
  unfold intervalGaussianPairLaw
  rw [← intervalGaussianPairLinearMap_eq]
  infer_instance

theorem intervalGaussianPairLaw_map_fst : intervalGaussianPairLaw.map Prod.fst = gaussianReal 0 1 := by
  rw [intervalGaussianPairLaw, Measure.map_map measurable_fst intervalGaussianPair_continuous.measurable]
  exact scaledCenteredCoordinate_map_standardGaussian (by decide : 2 ≤ Fintype.card (Fin 3)) 0

theorem intervalGaussianPairLaw_map_snd : intervalGaussianPairLaw.map Prod.snd = gaussianReal 0 1 := by
  rw [intervalGaussianPairLaw, Measure.map_map measurable_snd intervalGaussianPair_continuous.measurable]
  exact scaledCenteredCoordinate_map_standardGaussian (by decide : 2 ≤ Fintype.card (Fin 3)) 1

def intervalGaussianCubeMap (z : ℝ × ℝ) : CubePoint 3 :=
  ![normalCDF z.1, normalCDF (z.1 + z.2), normalCDF z.2]

theorem intervalGaussianCubeMap_continuous : Continuous intervalGaussianCubeMap := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact normalCDF_continuous.comp continuous_fst
  · exact normalCDF_continuous.comp (continuous_fst.add continuous_snd)
  · exact normalCDF_continuous.comp continuous_snd

theorem scaledCenteredCoordinates_three_sum (y : Fin 3 → ℝ) :
    scaledCenteredCoordinates y 0 + scaledCenteredCoordinates y 1 + scaledCenteredCoordinates y 2 = 0 := by
  simpa only [Fin.sum_univ_three, add_assoc] using scaledCenteredCoordinates_sum_zero y

theorem intervalGaussianPairLaw_map_sum :
    intervalGaussianPairLaw.map (fun z ↦ z.1 + z.2) = gaussianReal 0 1 := by
  rw [intervalGaussianPairLaw, Measure.map_map (by fun_prop) intervalGaussianPair_continuous.measurable]
  have heq : (fun z : ℝ × ℝ ↦ z.1 + z.2) ∘ intervalGaussianPair =
      (fun t : ℝ ↦ -t) ∘ (fun y : Fin 3 → ℝ ↦ scaledCenteredCoordinates y 2) := by
    funext y
    change scaledCenteredCoordinates y 0 + scaledCenteredCoordinates y 1 = -scaledCenteredCoordinates y 2
    linarith [scaledCenteredCoordinates_three_sum y]
  rw [heq, ← Measure.map_map (by fun_prop) (by unfold scaledCenteredCoordinates; fun_prop),
    scaledCenteredCoordinate_map_standardGaussian (by decide : 2 ≤ Fintype.card (Fin 3)) 2,
    gaussianReal_map_neg, neg_zero]

theorem intervalGaussianPairLaw_mean_fst : (∫ z, z.1 ∂intervalGaussianPairLaw) = 0 := by
  calc
    _ = ∫ t : ℝ, t ∂intervalGaussianPairLaw.map Prod.fst :=
      (integral_map (by fun_prop) (by fun_prop)).symm
    _ = 0 := by rw [intervalGaussianPairLaw_map_fst, integral_id_gaussianReal]

theorem intervalGaussianPairLaw_mean_snd : (∫ z, z.2 ∂intervalGaussianPairLaw) = 0 := by
  calc
    _ = ∫ t : ℝ, t ∂intervalGaussianPairLaw.map Prod.snd :=
      (integral_map (by fun_prop) (by fun_prop)).symm
    _ = 0 := by rw [intervalGaussianPairLaw_map_snd, integral_id_gaussianReal]

theorem intervalGaussianPairLaw_variance_fst : Var[Prod.fst; intervalGaussianPairLaw] = 1 := by
  rw [← variance_id_map (by fun_prop), intervalGaussianPairLaw_map_fst, variance_id_gaussianReal]
  rfl

theorem intervalGaussianPairLaw_variance_snd : Var[Prod.snd; intervalGaussianPairLaw] = 1 := by
  rw [← variance_id_map (by fun_prop), intervalGaussianPairLaw_map_snd, variance_id_gaussianReal]
  rfl

theorem intervalGaussianPairLaw_variance_sum : Var[(fun z : ℝ × ℝ ↦ z.1 + z.2); intervalGaussianPairLaw] = 1 := by
  rw [← variance_id_map (by fun_prop), intervalGaussianPairLaw_map_sum, variance_id_gaussianReal]
  rfl

theorem intervalGaussianPairLaw_covariance : cov[Prod.fst, Prod.snd; intervalGaussianPairLaw] = -(1 : ℝ) / 2 := by
  have h0 : MemLp Prod.fst 2 intervalGaussianPairLaw :=
    IsGaussian.memLp_dual intervalGaussianPairLaw (ContinuousLinearMap.fst ℝ ℝ ℝ) 2 (by decide)
  have h1 : MemLp Prod.snd 2 intervalGaussianPairLaw :=
    IsGaussian.memLp_dual intervalGaussianPairLaw (ContinuousLinearMap.snd ℝ ℝ ℝ) 2 (by decide)
  have h := variance_fun_add h0 h1
  rw [intervalGaussianPairLaw_variance_sum, intervalGaussianPairLaw_variance_fst,
    intervalGaussianPairLaw_variance_snd] at h
  linarith

theorem bivariateGaussian_dual_moments (ν : Measure (ℝ × ℝ)) [IsGaussian ν]
    (h0 : (∫ z, z.1 ∂ν) = 0) (h1 : (∫ z, z.2 ∂ν) = 0)
    (hv0 : Var[Prod.fst; ν] = 1) (hv1 : Var[Prod.snd; ν] = 1)
    (hcov : cov[Prod.fst, Prod.snd; ν] = -(1 : ℝ) / 2)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    (∫ z, L z ∂ν) = 0 ∧ Var[L; ν] = L (1, 0) ^ 2 - L (1, 0) * L (0, 1) + L (0, 1) ^ 2 := by
  have hx : MemLp Prod.fst 2 ν := IsGaussian.memLp_dual ν (ContinuousLinearMap.fst ℝ ℝ ℝ) 2 (by decide)
  have hy : MemLp Prod.snd 2 ν := IsGaussian.memLp_dual ν (ContinuousLinearMap.snd ℝ ℝ ℝ) 2 (by decide)
  have hL : (L : (ℝ × ℝ) → ℝ) = fun z ↦ L (1, 0) * z.1 + L (0, 1) * z.2 := by
    funext z
    calc
      L z = L (z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ)) := by congr 1; ext <;> simp
      _ = _ := by rw [map_add, map_smul, map_smul]; simp only [smul_eq_mul]; ring
  constructor
  · rw [hL, integral_add ((hx.const_mul _).integrable (by simp)) ((hy.const_mul _).integrable (by simp)),
      integral_const_mul, integral_const_mul, h0, h1, mul_zero, mul_zero, add_zero]
  · rw [hL, variance_fun_add (hx.const_mul _) (hy.const_mul _), variance_mul, variance_mul,
      covariance_mul_left, covariance_mul_right, hv0, hv1, hcov]
    ring

/-- A centered bivariate Gaussian with the source's variances and covariance
has exactly the actual F* pair law; its distribution is not an extra premise. -/
theorem intervalGaussianPairLaw_unique (ν : Measure (ℝ × ℝ)) [IsGaussian ν]
    (h0 : (∫ z, z.1 ∂ν) = 0) (h1 : (∫ z, z.2 ∂ν) = 0)
    (hv0 : Var[Prod.fst; ν] = 1) (hv1 : Var[Prod.snd; ν] = 1)
    (hcov : cov[Prod.fst, Prod.snd; ν] = -(1 : ℝ) / 2) : ν = intervalGaussianPairLaw := by
  apply Measure.ext_of_charFunDual
  funext L
  obtain ⟨hνm, hνv⟩ := bivariateGaussian_dual_moments ν h0 h1 hv0 hv1 hcov L
  obtain ⟨hμm, hμv⟩ := bivariateGaussian_dual_moments intervalGaussianPairLaw
    intervalGaussianPairLaw_mean_fst intervalGaussianPairLaw_mean_snd
    intervalGaussianPairLaw_variance_fst intervalGaussianPairLaw_variance_snd intervalGaussianPairLaw_covariance L
  rw [IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq]
  simp_rw [integral_complex_ofReal]
  rw [hνm, hνv, hμm, hμv]

theorem intervalCubeMap_limitingCubeMap (y : Fin 3 → ℝ) :
    intervalCubeMap (limitingCubeMap y) = intervalGaussianCubeMap (intervalGaussianPair y) := by
  funext i
  fin_cases i
  · rfl
  · change 1 - normalCDF (scaledCenteredCoordinates y 2) =
      normalCDF (scaledCenteredCoordinates y 0 + scaledCenteredCoordinates y 1)
    have hsum := scaledCenteredCoordinates_three_sum y
    rw [show scaledCenteredCoordinates y 2 =
      -(scaledCenteredCoordinates y 0 + scaledCenteredCoordinates y 1) by linarith, normalCDF_neg]
    ring
  · rfl

def intervalLimitMeasure : Measure (CubePoint 3) := (limitingAntichainMeasure (Fin 3)).map intervalCubeMap

instance intervalLimitMeasure_isProbabilityMeasure : IsProbabilityMeasure intervalLimitMeasure :=
  Measure.isProbabilityMeasure_map intervalCubeMap_continuous.measurable.aemeasurable

theorem intervalLimitMeasure_eq_gaussian_pair_pushforward :
    intervalLimitMeasure = intervalGaussianPairLaw.map intervalGaussianCubeMap := by
  rw [intervalLimitMeasure, limitingAntichainMeasure, intervalGaussianPairLaw,
    Measure.map_map intervalCubeMap_continuous.measurable limitingCubeMap_continuous.measurable,
    Measure.map_map intervalGaussianCubeMap_continuous.measurable intervalGaussianPair_continuous.measurable]
  congr 1
  funext y
  exact intervalCubeMap_limitingCubeMap y

theorem intervalLimitMeasure_eq_centered_bivariate_gaussian (ν : Measure (ℝ × ℝ)) [IsGaussian ν]
    (h0 : (∫ z, z.1 ∂ν) = 0) (h1 : (∫ z, z.2 ∂ν) = 0)
    (hv0 : Var[Prod.fst; ν] = 1) (hv1 : Var[Prod.snd; ν] = 1)
    (hcov : cov[Prod.fst, Prod.snd; ν] = -(1 : ℝ) / 2) :
    intervalLimitMeasure = ν.map intervalGaussianCubeMap := by
  rw [intervalGaussianPairLaw_unique ν h0 h1 hv0 hv1 hcov]
  exact intervalLimitMeasure_eq_gaussian_pair_pushforward

def openCubeThree : Set (CubePoint 3) := univ.pi (fun _ ↦ Ioo (0 : ℝ) 1)

theorem isOpen_openCubeThree : IsOpen openCubeThree :=
  isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)

theorem measurableSet_openCubeThree : MeasurableSet openCubeThree := isOpen_openCubeThree.measurableSet

def intervalPredictorError (x : CubePoint 3) : ℝ := by
  classical
  exact if x ∈ openCubeThree then (x 1 - normalCDF (normalQuantile (x 0) + normalQuantile (x 2))) ^ 2 else 0

theorem intervalPredictorError_measurable : Measurable intervalPredictorError := by
  have hf : Measurable (fun x : CubePoint 3 ↦
      (x 1 - normalCDF (normalQuantile (x 0) + normalQuantile (x 2))) ^ 2) :=
    ((measurable_pi_apply 1).sub (normalCDF_continuous.measurable.comp
      ((normalQuantile_measurable.comp (measurable_pi_apply 0)).add
        (normalQuantile_measurable.comp (measurable_pi_apply 2))))).pow_const 2
  exact hf.ite measurableSet_openCubeThree measurable_const

theorem intervalPredictorError_bounds (x : CubePoint 3) : 0 ≤ intervalPredictorError x ∧ intervalPredictorError x ≤ 1 := by
  unfold intervalPredictorError
  split_ifs with hx
  · have hx1 := hx 1 (mem_univ _)
    have hΦ := normalCDF_mem_Ioo (normalQuantile (x 0) + normalQuantile (x 2))
    constructor
    · positivity
    · have h1 : 0 ≤ 1 - (x 1 - normalCDF (normalQuantile (x 0) + normalQuantile (x 2))) := by linarith [hx1.2, hΦ.1]
      have h2 : 0 ≤ 1 + (x 1 - normalCDF (normalQuantile (x 0) + normalQuantile (x 2))) := by linarith [hx1.1, hΦ.2]
      nlinarith [mul_nonneg h1 h2]
  · exact ⟨le_rfl, zero_le_one⟩

theorem intervalPredictorError_continuousAt {x : CubePoint 3} (hx : x ∈ openCubeThree) :
    ContinuousAt intervalPredictorError x := by
  have hQ0 : ContinuousAt (fun y : CubePoint 3 ↦ normalQuantile (y 0)) x :=
    (normalQuantile_continuousAt (hx 0 (mem_univ _))).comp'
      (f := fun y : CubePoint 3 ↦ y 0) (continuous_apply 0).continuousAt
  have hQ2 : ContinuousAt (fun y : CubePoint 3 ↦ normalQuantile (y 2)) x :=
    (normalQuantile_continuousAt (hx 2 (mem_univ _))).comp'
      (f := fun y : CubePoint 3 ↦ y 2) (continuous_apply 2).continuousAt
  have hf : ContinuousAt (fun y : CubePoint 3 ↦
      (y 1 - normalCDF (normalQuantile (y 0) + normalQuantile (y 2))) ^ 2) x :=
    ((continuous_apply 1).continuousAt.sub
      (normalCDF_continuous.continuousAt.comp' (hQ0.add hQ2))).pow 2
  apply hf.congr_of_eventuallyEq
  filter_upwards [isOpen_openCubeThree.mem_nhds hx] with y hy
  simp only [intervalPredictorError, if_pos hy]

theorem intervalGaussianCubeMap_mem_openCube (z : ℝ × ℝ) : intervalGaussianCubeMap z ∈ openCubeThree := by
  intro i _
  fin_cases i <;> exact normalCDF_mem_Ioo _

theorem intervalPredictorError_gaussian_zero (z : ℝ × ℝ) :
    intervalPredictorError (intervalGaussianCubeMap z) = 0 := by
  rw [intervalPredictorError, if_pos (intervalGaussianCubeMap_mem_openCube z)]
  change (normalCDF (z.1 + z.2) -
    normalCDF (normalQuantile (normalCDF z.1) + normalQuantile (normalCDF z.2))) ^ 2 = 0
  rw [normalQuantile_normalCDF, normalQuantile_normalCDF, sub_self, zero_pow (by decide : 2 ≠ 0)]

theorem intervalLimitMeasure_openCube_mass : intervalLimitMeasure openCubeThree = 1 := by
  rw [intervalLimitMeasure_eq_gaussian_pair_pushforward,
    Measure.map_apply intervalGaussianCubeMap_continuous.measurable measurableSet_openCubeThree,
    show intervalGaussianCubeMap ⁻¹' openCubeThree = univ from
      Set.eq_univ_iff_forall.mpr intervalGaussianCubeMap_mem_openCube, measure_univ]

theorem intervalPredictorError_ae_continuous :
    ∀ᵐ x ∂intervalLimitMeasure, ContinuousAt intervalPredictorError x := by
  have hopen : ∀ᵐ x ∂intervalLimitMeasure, x ∈ openCubeThree :=
    (mem_ae_iff_prob_eq_one measurableSet_openCubeThree).mpr intervalLimitMeasure_openCube_mass
  exact hopen.mono (fun _ hx ↦ intervalPredictorError_continuousAt hx)

theorem intervalPredictorError_ae_zero : ∀ᵐ x ∂intervalLimitMeasure, intervalPredictorError x = 0 := by
  rw [intervalLimitMeasure_eq_gaussian_pair_pushforward]
  apply (ae_map_iff intervalGaussianCubeMap_continuous.measurable.aemeasurable
    (measurableSet_eq_fun intervalPredictorError_measurable measurable_const)).mpr
  exact Filter.Eventually.of_forall intervalPredictorError_gaussian_zero

theorem intervalPredictorError_integral_zero : ∫ x, intervalPredictorError x ∂intervalLimitMeasure = 0 :=
  integral_eq_zero_of_ae intervalPredictorError_ae_zero

def intervalLimitProbability : ProbabilityMeasure (CubePoint 3) := ⟨intervalLimitMeasure, inferInstance⟩

/-- A genuine fixed weak neighborhood forces the printed predictor error to be small. -/
theorem intervalPredictorError_weak_neighborhood {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set (ProbabilityMeasure (CubePoint 3)), U ∈ 𝓝 intervalLimitProbability ∧
      ∀ ν ∈ U, (∫ x, intervalPredictorError x ∂(ν : Measure (CubePoint 3))) < δ := by
  apply weak_neighborhood_for_vanishing_test intervalLimitProbability isOpen_openCubeThree.isClosed_compl
  · change intervalLimitMeasure openCubeThreeᶜ = 0
    rw [measure_compl measurableSet_openCubeThree (measure_ne_top _ _), intervalLimitMeasure_openCube_mass, measure_univ]
    exact tsub_self (1 : ℝ≥0∞)
  · exact intervalPredictorError_measurable
  · exact fun x ↦ (intervalPredictorError_bounds x).1
  · exact fun x ↦ (intervalPredictorError_bounds x).2
  · simp only [compl_compl]
    exact fun _ hx ↦ (intervalPredictorError_continuousAt hx).continuousWithinAt
  · exact intervalPredictorError_ae_zero
  · exact hδ

end Antichain
