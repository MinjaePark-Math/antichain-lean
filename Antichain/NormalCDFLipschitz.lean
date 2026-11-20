import Antichain.GaussianCDF
import Antichain.FloorSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! The actual normal CDF derivative and Lipschitz estimates in native Euclidean metrics. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

def standardNormalPDF (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)

def normalCDFLipschitzConstant : ℝ≥0 := ⟨(Real.sqrt (2 * Real.pi))⁻¹, by positivity⟩

theorem standardNormalPDF_eq_gaussianPDFReal : standardNormalPDF = gaussianPDFReal 0 1 := by
  funext x
  simp only [standardNormalPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]

theorem standardNormalPDF_continuous : Continuous standardNormalPDF := by
  unfold standardNormalPDF
  fun_prop

theorem standardNormalPDF_integrable : Integrable standardNormalPDF := by
  rw [standardNormalPDF_eq_gaussianPDFReal]
  exact integrable_gaussianPDFReal 0 1

theorem normalCDF_sub_eq_intervalIntegral (a b : ℝ) :
    normalCDF b - normalCDF a = ∫ x in a..b, standardNormalPDF x := by
  rw [normalCDF_eq_integral, normalCDF_eq_integral]
  exact intervalIntegral.integral_Iic_sub_Iic standardNormalPDF_integrable.integrableOn
    standardNormalPDF_integrable.integrableOn

/-- The derivative is proved for the actual probability-law CDF. -/
theorem normalCDF_hasDerivAt (x : ℝ) : HasDerivAt normalCDF (standardNormalPDF x) x := by
  have heq : normalCDF = fun t : ℝ ↦ normalCDF 0 + ∫ u in (0 : ℝ)..t, standardNormalPDF u := by
    funext t
    have h := normalCDF_sub_eq_intervalIntegral 0 t
    linarith
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (standardNormalPDF_continuous.intervalIntegrable 0 x)
    standardNormalPDF_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    standardNormalPDF_continuous.continuousAt).const_add _

theorem standardNormalPDF_nonneg (x : ℝ) : 0 ≤ standardNormalPDF x := by
  unfold standardNormalPDF
  positivity

theorem standardNormalPDF_le_lipschitzConstant (x : ℝ) :
    standardNormalPDF x ≤ (normalCDFLipschitzConstant : ℝ) := by
  have hexp : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  exact mul_le_of_le_one_right (by positivity : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹) hexp

theorem normalCDF_lipschitz : LipschitzWith normalCDFLipschitzConstant normalCDF := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (normalCDF_hasDerivAt x).differentiableAt)
  intro x
  change ‖deriv normalCDF x‖ ≤ (normalCDFLipschitzConstant : ℝ)
  rw [(normalCDF_hasDerivAt x).deriv, Real.norm_eq_abs, abs_of_nonneg (standardNormalPDF_nonneg x)]
  exact standardNormalPDF_le_lipschitzConstant x

def euclideanCoordinateMap {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ f (x i))

/-- A scalar Lipschitz constant lifts unchanged to the Euclidean L2 norm. -/
theorem euclideanCoordinateMap_lipschitz {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (euclideanCoordinateMap (ι := ι) f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg C.coe_nonneg (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hb := hf.dist_le_mul (x i) (y i)
  simp only [Real.dist_eq] at hb
  have hs := (sq_le_sq₀ (abs_nonneg (f (x i) - f (y i)))
    (mul_nonneg C.coe_nonneg (abs_nonneg (x i - y i)))).mpr hb
  simpa only [euclideanCoordinateMap, PiLp.sub_apply, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs, mul_pow] using hs

def euclideanNormalCDF {ι : Type*} [Fintype ι] : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
  euclideanCoordinateMap normalCDF

theorem euclideanNormalCDF_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith normalCDFLipschitzConstant (euclideanNormalCDF (ι := ι)) :=
  euclideanCoordinateMap_lipschitz normalCDF_lipschitz

def euclideanNormalCDFFloorMap {ι : Type*} [Fintype ι] (u : FloorSpace ι) : EuclideanSpace ℝ ι :=
  euclideanNormalCDF u.val

theorem euclideanNormalCDFFloorMap_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith normalCDFLipschitzConstant (euclideanNormalCDFFloorMap (ι := ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  exact euclideanNormalCDF_lipschitz.dist_le_mul u.val v.val

@[simp] theorem euclideanNormalCDFFloorMap_apply {ι : Type*} [Fintype ι]
    (u : FloorSpace ι) (i : ι) : euclideanNormalCDFFloorMap u i = normalCDF (u.val i) := rfl

end Antichain
