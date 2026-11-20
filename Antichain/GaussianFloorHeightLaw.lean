import Antichain.GaussianFloorLaw
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The full actual Gaussian floor/height decomposition, including independence. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Finset
open scoped Topology NNReal RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def gaussianHeightMap (y : ι → ℝ) : ℝ :=
  (∑ i, y i) / Real.sqrt (Fintype.card ι : ℝ)

def gaussianFloorHeightMap (y : ι → ℝ) : FloorSpace ι × ℝ :=
  (gaussianFloorMap y, gaussianHeightMap y)

omit [Nonempty ι] in
theorem gaussianHeightMap_continuous : Continuous (gaussianHeightMap (ι := ι)) := by
  unfold gaussianHeightMap
  fun_prop

theorem gaussianFloorHeightMap_continuous : Continuous (gaussianFloorHeightMap (ι := ι)) :=
  gaussianFloorMap_continuous.prodMk gaussianHeightMap_continuous

/-- A floor test vector plus its unit-normal height component. -/
def floorHeightLift (u : FloorSpace ι) (a : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => u.val i + a / Real.sqrt (Fintype.card ι : ℝ))

theorem floorHeightLift_inner (y : ι → ℝ) (u : FloorSpace ι) (a : ℝ) :
    inner ℝ (gaussianFloorMap y) u + gaussianHeightMap y * a =
      inner ℝ (WithLp.toLp 2 y) (floorHeightLift u a) := by
  rw [gaussianFloorMap_inner]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i, u.val i * y i) +
      ((∑ i, y i) / Real.sqrt (Fintype.card ι : ℝ)) * a =
    ∑ i, (u.val i + a / Real.sqrt (Fintype.card ι : ℝ)) * y i
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Pythagoras with exactly the manuscript's unit normal `e = 1/sqrt(d)`. -/
theorem floorHeightLift_norm_sq (u : FloorSpace ι) (a : ℝ) :
    ‖floorHeightLift u a‖ ^ 2 = ‖u‖ ^ 2 + a ^ 2 := by
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card ι : ℝ) ^ 2 = (Fintype.card ι : ℝ) :=
    Real.sq_sqrt hm.le
  have hsn : Real.sqrt (Fintype.card ι : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have hu : ∑ i, u.val i = 0 := u.property
  have hn := EuclideanSpace.norm_sq_eq u.val
  simp only [Real.norm_eq_abs, sq_abs] at hn
  have hsum := sum_sq_add_of_sum_zero (fun i => u.val i)
    (a / Real.sqrt (Fintype.card ι : ℝ)) hu
  have hshift : (∑ i, (u.val i + a / Real.sqrt (Fintype.card ι : ℝ)) ^ 2) =
      (Fintype.card ι : ℝ) * (a / Real.sqrt (Fintype.card ι : ℝ)) ^ 2 + ∑ i, u.val i ^ 2 := by
    simpa only [add_comm] using hsum
  rw [EuclideanSpace.norm_sq_eq]
  simp only [floorHeightLift, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  rw [hshift, ← hn]
  change (Fintype.card ι : ℝ) * (a / Real.sqrt (Fintype.card ι : ℝ)) ^ 2 + ‖u‖ ^ 2 = _
  have hterm : (Fintype.card ι : ℝ) * (a / Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = a ^ 2 := by
    rw [div_pow]
    field_simp [hsn]
    rw [hs]
    ring
  rw [hterm]
  ring

theorem gaussianFloorHeightMap_inner (y : ι → ℝ) (u : FloorSpace ι) (a : ℝ) :
    inner ℝ (WithLp.toLp 2 (gaussianFloorHeightMap y)) (WithLp.toLp 2 (u, a)) =
      inner ℝ (WithLp.toLp 2 y) (floorHeightLift u a) := by
  rw [WithLp.prod_inner_apply]
  change inner ℝ (gaussianFloorMap y) u + a * gaussianHeightMap y = _
  rw [mul_comm a, floorHeightLift_inner]

/-- Joint characteristic function, computed directly from the independent ambient
coordinates. The factorization is proved from orthogonality. -/
theorem charFun_gaussianFloorHeight (u : FloorSpace ι) (a : ℝ) :
    charFun (((standardGaussianProduct ι).map gaussianFloorHeightMap).map (WithLp.toLp 2))
      (WithLp.toLp 2 (u, a)) =
      charFun (radialGaussianMeasure (FloorSpace ι) 1) u * charFun (gaussianReal 0 1) a := by
  have hcmp : charFun (((standardGaussianProduct ι).map gaussianFloorHeightMap).map
      (WithLp.toLp 2)) (WithLp.toLp 2 (u, a)) =
      charFun ((standardGaussianProduct ι).map (WithLp.toLp 2)) (floorHeightLift u a) := by
    simp only [charFun_apply]
    rw [integral_map (by fun_prop : AEMeasurable (WithLp.toLp 2)
        ((standardGaussianProduct ι).map gaussianFloorHeightMap)) (by fun_prop),
      integral_map gaussianFloorHeightMap_continuous.measurable.aemeasurable (by fun_prop),
      integral_map (by fun_prop : AEMeasurable (WithLp.toLp 2) (standardGaussianProduct ι))
        (by fun_prop)]
    simp_rw [gaussianFloorHeightMap_inner]
  rw [hcmp, charFun_standardGaussianProduct,
    charFun_radialGaussianMeasure (by norm_num : (0 : ℝ) < 1), charFun_gaussianReal]
  simp only [Complex.ofReal_zero, NNReal.coe_one, Complex.ofReal_one, mul_zero,
    zero_mul, one_mul, zero_sub]
  rw [← Complex.exp_add, ← Complex.ofReal_pow, floorHeightLift_norm_sq]
  congr 1
  push_cast
  ring

/-- Exact independent product law of the actual orthogonal floor and signed height. -/
theorem gaussianFloorHeightMap_law :
    (standardGaussianProduct ι).map gaussianFloorHeightMap =
      (radialGaussianMeasure (FloorSpace ι) 1).prod (gaussianReal 0 1) := by
  letI : IsProbabilityMeasure ((standardGaussianProduct ι).map gaussianFloorHeightMap) :=
    Measure.isProbabilityMeasure_map gaussianFloorHeightMap_continuous.measurable.aemeasurable
  letI : IsProbabilityMeasure (radialGaussianMeasure (FloorSpace ι) 1) :=
    radialGaussianMeasure_isProbabilityMeasure (by norm_num : (0 : ℝ) < 1)
  apply charFun_eq_prod_iff.mp
  intro t
  exact charFun_gaussianFloorHeight (WithLp.ofLp t).1 (WithLp.ofLp t).2

/-- The same joint law in the paper's named standard-floor density. -/
theorem gaussianFloorHeightMap_law_withDensity :
    (standardGaussianProduct ι).map gaussianFloorHeightMap =
      (floorVolume.withDensity (fun u => ENNReal.ofReal (standardFloorDensity u))).prod
        (gaussianReal 0 1) := gaussianFloorHeightMap_law

end Antichain
