import Antichain.LimitMarginals
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

/-! The actual limiting Gaussian's general-dimensional covariance matrix. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Finset Set
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

theorem standardGaussianProduct_map_linearForm (c : EuclideanSpace ℝ ι) :
    (standardGaussianProduct ι).map (fun y : ι → ℝ ↦ ∑ j, c j * y j) =
      gaussianReal 0 (Real.toNNReal (‖c‖ ^ 2)) := by
  have hmeas : Measurable (fun y : ι → ℝ ↦ ∑ j, c j * y j) := by fun_prop
  letI : IsProbabilityMeasure ((standardGaussianProduct ι).map
      (fun y : ι → ℝ ↦ ∑ j, c j * y j)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  have heq : charFun ((standardGaussianProduct ι).map (fun y : ι → ℝ ↦ ∑ j, c j * y j)) t =
      charFun ((standardGaussianProduct ι).map (WithLp.toLp 2)) (t • c) := by
    simp only [charFun_apply]
    rw [integral_map hmeas.aemeasurable (by fun_prop),
      integral_map (by fun_prop : AEMeasurable (WithLp.toLp 2) (standardGaussianProduct ι))
        (by fun_prop)]
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
  rw [heq, charFun_standardGaussianProduct, charFun_gaussianReal,
    Real.coe_toNNReal _ (sq_nonneg _), norm_smul, Real.norm_eq_abs]
  push_cast
  have ht : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by exact_mod_cast sq_abs t
  rw [mul_pow, ht]
  simp only [mul_zero, zero_mul, zero_sub]
  congr 1
  ring

theorem standardGaussianProduct_linearForm_mean (c : EuclideanSpace ℝ ι) :
    (∫ y : ι → ℝ, (∑ j, c j * y j) ∂standardGaussianProduct ι) = 0 := by
  have hm : Measurable (fun y : ι → ℝ ↦ ∑ j, c j * y j) := by fun_prop
  calc
    _ = ∫ t : ℝ, t ∂(standardGaussianProduct ι).map (fun y : ι → ℝ ↦ ∑ j, c j * y j) :=
      (integral_map hm.aemeasurable (by fun_prop)).symm
    _ = 0 := by rw [standardGaussianProduct_map_linearForm, integral_id_gaussianReal]

theorem standardGaussianProduct_linearForm_variance (c : EuclideanSpace ℝ ι) :
    Var[(fun y : ι → ℝ ↦ ∑ j, c j * y j); standardGaussianProduct ι] = ‖c‖ ^ 2 := by
  have hm : Measurable (fun y : ι → ℝ ↦ ∑ j, c j * y j) := by fun_prop
  rw [← variance_id_map hm.aemeasurable, standardGaussianProduct_map_linearForm,
    variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]

theorem standardGaussianProduct_gaussian : IsGaussian (standardGaussianProduct ι) := by
  classical
  constructor
  intro L
  let c : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i ↦ L (Pi.single i (1 : ℝ)))
  have hL : (L : (ι → ℝ) → ℝ) = (fun y ↦ ∑ i, c i * y i) := by
    funext y
    have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      funext i
      simp [Pi.single_apply, mul_ite]
    conv_lhs => rw [hy]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
  rw [hL, standardGaussianProduct_map_linearForm,
    standardGaussianProduct_linearForm_mean, standardGaussianProduct_linearForm_variance]

def scaledCenteredLinearMap : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦
    ∑ j : ι, scaledCoordinateCoefficient i j • ContinuousLinearMap.proj j)

@[simp] theorem scaledCenteredLinearMap_apply (y : ι → ℝ) :
    scaledCenteredLinearMap y = scaledCenteredCoordinates y := by
  funext i
  simp only [scaledCenteredLinearMap, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact (scaledCenteredCoordinates_eq_linearForm y i).symm

def scaledCenteredGaussianLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  (standardGaussianProduct ι).map scaledCenteredCoordinates

theorem scaledCenteredGaussianLaw_gaussian : IsGaussian (scaledCenteredGaussianLaw ι) := by
  letI := standardGaussianProduct_gaussian (ι := ι)
  change IsGaussian ((standardGaussianProduct ι).map scaledCenteredCoordinates)
  rw [← show (scaledCenteredLinearMap : (ι → ℝ) → (ι → ℝ)) =
    scaledCenteredCoordinates from funext scaledCenteredLinearMap_apply]
  infer_instance

theorem scaledCenteredCoordinate_mean (i : ι) :
    (∫ y : ι → ℝ, scaledCenteredCoordinates y i ∂standardGaussianProduct ι) = 0 := by
  simp_rw [scaledCenteredCoordinates_eq_linearForm]
  exact standardGaussianProduct_linearForm_mean _

theorem scaledCenteredCoordinate_variance (hd : 2 ≤ Fintype.card ι) (i : ι) :
    Var[(fun y : ι → ℝ ↦ scaledCenteredCoordinates y i); standardGaussianProduct ι] = 1 := by
  simp_rw [scaledCenteredCoordinates_eq_linearForm]
  rw [standardGaussianProduct_linearForm_variance, scaledCoordinateCoefficient_norm hd, one_pow]

theorem scaledCenteredCoordinate_memLp (i : ι) :
    MemLp (fun y : ι → ℝ ↦ scaledCenteredCoordinates y i) 2 (standardGaussianProduct ι) := by
  letI := standardGaussianProduct_gaussian (ι := ι)
  have h := IsGaussian.memLp_dual (standardGaussianProduct ι)
    ((ContinuousLinearMap.proj i).comp scaledCenteredLinearMap) 2 (by decide)
  change MemLp (fun y : ι → ℝ ↦ scaledCenteredLinearMap y i) 2 (standardGaussianProduct ι) at h
  simpa only [scaledCenteredLinearMap_apply] using h

theorem scaledCoordinateCoefficient_sub_norm_sq (hd : 2 ≤ Fintype.card ι)
    {i j : ι} (hij : i ≠ j) :
    ‖scaledCoordinateCoefficient i - scaledCoordinateCoefficient j‖ ^ 2 =
      2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) := by
  classical
  let D : ℝ := Fintype.card ι
  have hD : (2 : ℝ) ≤ D := by dsimp [D]; exact_mod_cast hd
  have hs : floorGaussianScale ι ^ 2 = D / (D - 1) :=
    Real.sq_sqrt (div_nonneg (by linarith) (by linarith))
  have hcoord (k : ι) :
      (scaledCoordinateCoefficient i - scaledCoordinateCoefficient j) k =
        floorGaussianScale ι * ((if k = i then 1 else 0) - (if k = j then 1 else 0)) := by
    change floorGaussianScale ι * ((if k = i then 1 else 0) - 1 / D) -
      floorGaussianScale ι * ((if k = j then 1 else 0) - 1 / D) = _
    ring
  have hsum : (∑ k : ι, ((if k = i then (1 : ℝ) else 0) -
      (if k = j then 1 else 0)) ^ 2) = 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [ite_pow, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      hij.symm, if_false, mul_zero, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    norm_num
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  simp_rw [hcoord, mul_pow]
  rw [← Finset.mul_sum, hsum, hs]
  dsimp [D]
  ring

theorem scaledCenteredCoordinate_difference_variance (hd : 2 ≤ Fintype.card ι)
    {i j : ι} (hij : i ≠ j) :
    Var[(fun y : ι → ℝ ↦ scaledCenteredCoordinates y i - scaledCenteredCoordinates y j);
      standardGaussianProduct ι] =
        2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) := by
  have heq : (fun y : ι → ℝ ↦ scaledCenteredCoordinates y i - scaledCenteredCoordinates y j) =
      (fun y ↦ ∑ k, (scaledCoordinateCoefficient i - scaledCoordinateCoefficient j) k * y k) := by
    funext y
    simp_rw [scaledCenteredCoordinates_eq_linearForm]
    simp only [PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [heq, standardGaussianProduct_linearForm_variance, scaledCoordinateCoefficient_sub_norm_sq hd hij]

/-- The source's off-diagonal covariance, for every actual coordinate pair and dimension. -/
theorem scaledCenteredCoordinate_covariance (hd : 2 ≤ Fintype.card ι)
    {i j : ι} (hij : i ≠ j) :
    cov[(fun y : ι → ℝ ↦ scaledCenteredCoordinates y i),
      (fun y : ι → ℝ ↦ scaledCenteredCoordinates y j); standardGaussianProduct ι] =
        -(1 : ℝ) / ((Fintype.card ι : ℝ) - 1) := by
  have hv := variance_fun_sub (scaledCenteredCoordinate_memLp i) (scaledCenteredCoordinate_memLp j)
  rw [scaledCenteredCoordinate_difference_variance hd hij,
    scaledCenteredCoordinate_variance hd i, scaledCenteredCoordinate_variance hd j] at hv
  have hD : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hm : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  apply (eq_div_iff hm).mpr
  field_simp at hv
  nlinarith

/-- All printed distributional facts about `F*`, using its actual Gaussian source law. -/
theorem scaledCenteredGaussian_source (hd : 2 ≤ Fintype.card ι) :
    IsGaussian (scaledCenteredGaussianLaw ι) ∧
      (∀ i, (∫ y, y i ∂scaledCenteredGaussianLaw ι) = 0 ∧
        Var[(fun y : ι → ℝ ↦ y i); scaledCenteredGaussianLaw ι] = 1) ∧
      (∀ i j, i ≠ j → cov[(fun y : ι → ℝ ↦ y i), (fun y : ι → ℝ ↦ y j);
        scaledCenteredGaussianLaw ι] = -(1 : ℝ) / ((Fintype.card ι : ℝ) - 1)) ∧
      (∀ᵐ y ∂scaledCenteredGaussianLaw ι, ∑ i, y i = 0) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hm : Measurable (scaledCenteredCoordinates (ι := ι)) := by
    unfold scaledCenteredCoordinates
    fun_prop
  refine ⟨scaledCenteredGaussianLaw_gaussian, ?_, ?_, ?_⟩
  · intro i
    constructor
    · rw [scaledCenteredGaussianLaw, integral_map hm.aemeasurable
        (measurable_pi_apply i).aestronglyMeasurable]
      exact scaledCenteredCoordinate_mean i
    · rw [scaledCenteredGaussianLaw, variance_map (measurable_pi_apply i).aemeasurable hm.aemeasurable]
      exact scaledCenteredCoordinate_variance hd i
  · intro i j hij
    rw [scaledCenteredGaussianLaw, covariance_map_fun
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
      hm.aemeasurable]
    exact scaledCenteredCoordinate_covariance hd hij
  · have hclosed : IsClosed {y : ι → ℝ | ∑ i, y i = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    apply (ae_map_iff hm.aemeasurable hclosed.measurableSet).mpr
    exact Filter.Eventually.of_forall scaledCenteredCoordinates_sum_zero

end Antichain
