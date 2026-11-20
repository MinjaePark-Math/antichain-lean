import Antichain.LimitMeasure
import Antichain.FloorSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Positivity

/-! Normalized Gaussian densities and their powers on the actual Euclidean floor. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Module GaussianFourier
open scoped Topology ENNReal NNReal RealInnerProductSpace

section FiniteHilbertGaussian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The normalized isotropic Gaussian density of variance `v` in the canonical
Euclidean volume of a finite dimensional real inner product space. -/
def radialGaussianDensity (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (v : ℝ) (x : V) : ℝ :=
  (2 * Real.pi * v) ^ (-(finrank ℝ V : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * v))

omit [MeasurableSpace V] [BorelSpace V] in
theorem radialGaussianDensity_pos {v : ℝ} (hv : 0 < v) (x : V) :
    0 < radialGaussianDensity V v x := by
  unfold radialGaussianDensity
  positivity

omit [MeasurableSpace V] [BorelSpace V] in
theorem radialGaussianDensity_continuous (v : ℝ) : Continuous (radialGaussianDensity V v) := by
  unfold radialGaussianDensity
  fun_prop

theorem integrable_exp_neg_mul_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V => Real.exp (-b * ‖x‖ ^ 2)) := by
  have hi := (integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) (show 0 < (b : ℂ).re from hb) 0 (0 : V)).norm
  simpa [Complex.norm_exp, pow_two, Complex.mul_re] using hi

theorem radialGaussianDensity_integrable {v : ℝ} (hv : 0 < v) :
    Integrable (radialGaussianDensity V v) := by
  have hb : 0 < 1 / (2 * v) := by positivity
  have hi := (integrable_exp_neg_mul_norm_sq (V := V) hb).const_mul
    ((2 * Real.pi * v) ^ (-(finrank ℝ V : ℝ) / 2))
  apply hi.congr
  exact Filter.Eventually.of_forall (fun x => by
    dsimp [radialGaussianDensity]
    congr 2
    ring)

/-- Exact normalization; the measure is the canonical Euclidean volume. -/
theorem integral_radialGaussianDensity {v : ℝ} (hv : 0 < v) :
    ∫ x : V, radialGaussianDensity V v x = 1 := by
  have hb : 0 < 1 / (2 * v) := by positivity
  have hbase : 0 < 2 * Real.pi * v := by positivity
  have hratio : Real.pi / (1 / (2 * v)) = 2 * Real.pi * v := by
    field_simp
  have hexp : (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * v))) =
      (fun x : V => Real.exp (-(1 / (2 * v)) * ‖x‖ ^ 2)) := by
    funext x
    congr 1
    ring
  unfold radialGaussianDensity
  rw [integral_const_mul, hexp, integral_rexp_neg_mul_sq_norm hb, hratio]
  rw [show -(finrank ℝ V : ℝ) / 2 = -((finrank ℝ V : ℝ) / 2) by ring,
    Real.rpow_neg hbase.le]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hbase _))

/-- A normalized actual Gaussian density, rather than a named but unproved law. -/
def radialGaussianMeasure (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (v : ℝ) : Measure V :=
  volume.withDensity (fun x => ENNReal.ofReal (radialGaussianDensity V v x))

theorem radialGaussianMeasure_isProbabilityMeasure {v : ℝ} (hv : 0 < v) :
    IsProbabilityMeasure (radialGaussianMeasure V v) := by
  constructor
  rw [radialGaussianMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal
      (radialGaussianDensity_integrable hv)
      (Filter.Eventually.of_forall (fun x => (radialGaussianDensity_pos hv x).le)),
    integral_radialGaussianDensity hv, ENNReal.ofReal_one]

/-- Exact Gaussian power integral, with all constants and Euclidean dimension retained. -/
theorem integral_radialGaussianDensity_rpow {v p : ℝ} (hv : 0 < v) (hp : 0 < p) :
    ∫ x : V, (radialGaussianDensity V v x) ^ p =
      ((2 * Real.pi * v) ^ (-(finrank ℝ V : ℝ) / 2)) ^ p *
        (2 * Real.pi * v / p) ^ ((finrank ℝ V : ℝ) / 2) := by
  have hb : 0 < p / (2 * v) := div_pos hp (by positivity)
  have hbase : 0 ≤ (2 * Real.pi * v) ^ (-(finrank ℝ V : ℝ) / 2) := by positivity
  have heq : (fun x : V => (radialGaussianDensity V v x) ^ p) =
      (fun x : V => ((2 * Real.pi * v) ^ (-(finrank ℝ V : ℝ) / 2)) ^ p *
        Real.exp (-(p / (2 * v)) * ‖x‖ ^ 2)) := by
    funext x
    rw [radialGaussianDensity, Real.mul_rpow hbase (Real.exp_nonneg _), ← Real.exp_mul]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_rexp_neg_mul_sq_norm hb]
  congr 2
  field_simp

/-- The characteristic function of the normalized radial density, proved by
the finite-dimensional Gaussian integral rather than assumed as a law identity. -/
theorem charFun_radialGaussianMeasure {v : ℝ} (hv : 0 < v) (t : V) :
    charFun (radialGaussianMeasure V v) t =
      Complex.exp (-((v : ℂ) * (‖t‖ : ℂ) ^ 2) / 2) := by
  let C : ℝ := (2 * Real.pi * v) ^ (-(finrank ℝ V : ℝ) / 2)
  let b : ℝ := 1 / (2 * v)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbase : 0 < 2 * Real.pi * v := by positivity
  have hdens : Measurable (fun x : V => ENNReal.ofReal (radialGaussianDensity V v x)) :=
    (radialGaussianDensity_continuous v).measurable.ennreal_ofReal
  rw [charFun_apply, radialGaussianMeasure,
    integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (radialGaussianDensity_pos hv _).le, Complex.real_smul]
  have heq : (fun x : V => (radialGaussianDensity V v x : ℂ) *
      Complex.exp (((inner ℝ x t) : ℂ) * Complex.I)) =
      (fun x : V => (C : ℂ) * Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
        Complex.I * ((inner ℝ t x) : ℂ))) := by
    funext x
    dsimp [radialGaussianDensity, C, b]
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add,
      real_inner_comm x t]
    congr 2
    push_cast
    ring
  rw [heq, integral_const_mul,
    integral_cexp_neg_mul_sq_norm_add (show 0 < (b : ℂ).re from hb)]
  have hdim : (finrank ℝ V / 2 : ℂ) = (((finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hp : ((Real.pi : ℂ) / (b : ℂ)) ^ (finrank ℝ V / 2 : ℂ) =
      (((Real.pi / b) ^ ((finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hdim, ← Complex.ofReal_div, ← Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hb.le)]
  have hratio : Real.pi / b = 2 * Real.pi * v := by dsimp [b]; field_simp
  have hnorm : C * (Real.pi / b) ^ ((finrank ℝ V : ℝ) / 2) = 1 := by
    rw [hratio]
    dsimp [C]
    rw [show -(finrank ℝ V : ℝ) / 2 = -((finrank ℝ V : ℝ) / 2) by ring,
      Real.rpow_neg hbase.le]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hbase _))
  rw [hp, ← mul_assoc, ← Complex.ofReal_mul, hnorm, Complex.ofReal_one, one_mul]
  congr 1
  dsimp [b]
  have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Complex.I_sq]
  push_cast
  field_simp
  ring

/-- Raising a standard Gaussian density to a positive power and renormalizing
gives the actual Gaussian density with inverse variance. -/
theorem radialGaussianDensity_inverseVariance_eq_normalized_power
    {p : ℝ} (hp : 0 < p) (x : V) :
    radialGaussianDensity V (1 / p) x =
      (radialGaussianDensity V 1 x) ^ p /
        (∫ y : V, (radialGaussianDensity V 1 y) ^ p) := by
  let C : ℝ := (2 * Real.pi) ^ (-(finrank ℝ V : ℝ) / 2)
  let D : ℝ := 2 * Real.pi / p
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hI : (∫ y : V, (radialGaussianDensity V 1 y) ^ p) =
      C ^ p * D ^ ((finrank ℝ V : ℝ) / 2) := by
    simpa only [C, D, mul_one] using
      (integral_radialGaussianDensity_rpow (V := V) (by norm_num : (0 : ℝ) < 1) hp)
  have hpw : (radialGaussianDensity V 1 x) ^ p =
      C ^ p * Real.exp (-(p / 2) * ‖x‖ ^ 2) := by
    simp only [radialGaussianDensity, mul_one]
    rw [Real.mul_rpow hC.le (Real.exp_nonneg _), ← Real.exp_mul]
    congr 2
    ring
  have hrho : radialGaussianDensity V (1 / p) x =
      D ^ (-((finrank ℝ V : ℝ) / 2)) * Real.exp (-(p / 2) * ‖x‖ ^ 2) := by
    unfold radialGaussianDensity
    dsimp [D]
    apply congrArg₂ (fun a b : ℝ => a * b)
    · apply congrArg₂ (fun a b : ℝ => a ^ b)
      · field_simp
      · ring
    · congr 1
      field_simp [hp.ne']
  rw [hI, hpw, hrho, Real.rpow_neg hD.le]
  have hCn : C ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hC _)
  have hDn : D ^ ((finrank ℝ V : ℝ) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hD _)
  field_simp

end FiniteHilbertGaussian

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The actual orthogonal projection of an independent Gaussian coordinate vector. -/
def gaussianFloorMap (y : ι → ℝ) : FloorSpace ι := centeredFloor (WithLp.toLp 2 y)

theorem gaussianFloorMap_continuous : Continuous (gaussianFloorMap (ι := ι)) := by
  have hc : Continuous (centeredFloor (ι := ι)) := by
    apply Continuous.subtype_mk
    have heq : (fun x : EuclideanSpace ℝ ι => (centeredFloor x).val) =
        (FloorSpace ι).starProjection := funext centeredFloor_eq_starProjection
    change Continuous (fun x : EuclideanSpace ℝ ι => (centeredFloor x).val)
    rw [heq]
    exact (FloorSpace ι).starProjection.continuous
  exact hc.comp (by fun_prop)

theorem gaussianFloorMap_inner (y : ι → ℝ) (u : FloorSpace ι) :
    inner ℝ (gaussianFloorMap y) u = inner ℝ (WithLp.toLp 2 y) u.val := by
  simp only [Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i, u.val i * (y i - (∑ j, y j) / (Fintype.card ι : ℝ))) =
    ∑ i, u.val i * y i
  simp_rw [mul_sub]
  have hu : ∑ i, u.val i = 0 := u.property
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hu, zero_mul, sub_zero]

omit [Nonempty ι] in
theorem charFun_standardGaussianProduct (u : EuclideanSpace ℝ ι) :
    charFun ((standardGaussianProduct ι).map (WithLp.toLp 2)) u =
      Complex.exp (-(‖u‖ : ℂ) ^ 2 / 2) := by
  rw [standardGaussianProduct, charFun_pi]
  simp_rw [charFun_gaussianReal]
  simp only [Complex.ofReal_zero, NNReal.coe_one, Complex.ofReal_one,
    mul_zero, zero_mul, one_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp_rw [neg_div]
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
  congr 2
  have hn := EuclideanSpace.norm_sq_eq u
  simp only [Real.norm_eq_abs, sq_abs] at hn
  have hc := congrArg Complex.ofReal hn
  push_cast at hc
  exact hc.symm

theorem charFun_projectedGaussian (u : FloorSpace ι) :
    charFun ((standardGaussianProduct ι).map gaussianFloorMap) u =
      Complex.exp (-(‖u‖ : ℂ) ^ 2 / 2) := by
  have hmap : charFun ((standardGaussianProduct ι).map gaussianFloorMap) u =
      charFun ((standardGaussianProduct ι).map (WithLp.toLp 2)) u.val := by
    simp only [charFun_apply]
    rw [integral_map gaussianFloorMap_continuous.measurable.aemeasurable (by fun_prop),
      integral_map (by fun_prop : AEMeasurable (WithLp.toLp 2) (standardGaussianProduct ι))
        (by fun_prop)]
    simp_rw [gaussianFloorMap_inner]
  rw [hmap, charFun_standardGaussianProduct]
  rfl

/-- The orthogonally projected independent Gaussian law has exactly `ψ_E`
as its density with respect to induced Euclidean floor volume. -/
theorem projectedGaussian_eq_radialGaussian :
    (standardGaussianProduct ι).map gaussianFloorMap = radialGaussianMeasure (FloorSpace ι) 1 := by
  letI : IsProbabilityMeasure ((standardGaussianProduct ι).map gaussianFloorMap) :=
    Measure.isProbabilityMeasure_map gaussianFloorMap_continuous.measurable.aemeasurable
  letI : IsProbabilityMeasure (radialGaussianMeasure (FloorSpace ι) 1) :=
    radialGaussianMeasure_isProbabilityMeasure (by norm_num : (0 : ℝ) < 1)
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_projectedGaussian, charFun_radialGaussianMeasure (by norm_num : (0 : ℝ) < 1)]
  simp

/-- The actual rescaled orthogonal projection used in the definition of `F*`. -/
def scaledGaussianFloorMap (y : ι → ℝ) : FloorSpace ι :=
  floorGaussianScale ι • gaussianFloorMap y

theorem scaledGaussianFloorMap_continuous : Continuous (scaledGaussianFloorMap (ι := ι)) :=
  gaussianFloorMap_continuous.const_smul _

@[simp] theorem scaledGaussianFloorMap_coordinates (y : ι → ℝ) (i : ι) :
    (scaledGaussianFloorMap y).val i = scaledCenteredCoordinates y i := rfl

/-- The exact limiting floor law, with the source's variance and Euclidean measure. -/
theorem scaledProjectedGaussian_eq_radialGaussian (hd : 2 ≤ Fintype.card ι) :
    (standardGaussianProduct ι).map scaledGaussianFloorMap =
      radialGaussianMeasure (FloorSpace ι)
        ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) := by
  have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hv : 0 < (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) :=
    div_pos (by linarith) (by linarith)
  have hscale : floorGaussianScale ι ^ 2 =
      (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) := Real.sq_sqrt hv.le
  letI : IsProbabilityMeasure ((standardGaussianProduct ι).map scaledGaussianFloorMap) :=
    Measure.isProbabilityMeasure_map scaledGaussianFloorMap_continuous.measurable.aemeasurable
  letI : IsProbabilityMeasure (radialGaussianMeasure (FloorSpace ι)
      ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1))) :=
    radialGaussianMeasure_isProbabilityMeasure hv
  apply Measure.ext_of_charFun
  funext u
  have hmap : (standardGaussianProduct ι).map scaledGaussianFloorMap =
      ((standardGaussianProduct ι).map gaussianFloorMap).map
        (fun z : FloorSpace ι => floorGaussianScale ι • z) := by
    rw [Measure.map_map (by fun_prop) gaussianFloorMap_continuous.measurable]
    rfl
  rw [hmap, charFun_map_smul, charFun_projectedGaussian, charFun_radialGaussianMeasure hv]
  congr 1
  rw [norm_smul, Real.norm_eq_abs]
  push_cast
  rw [mul_pow, ← Complex.ofReal_pow, sq_abs, hscale]
  push_cast
  rfl

/-- The paper's standard-floor density `ψ_E`, on actual induced Euclidean volume. -/
def standardFloorDensity (u : FloorSpace ι) : ℝ := radialGaussianDensity (FloorSpace ι) 1 u

/-- The paper's limiting-floor density `ρ*`, before identifying it with the projected law. -/
def limitingFloorDensity (u : FloorSpace ι) : ℝ :=
  radialGaussianDensity (FloorSpace ι)
    ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) u

theorem standardFloorDensity_formula (u : FloorSpace ι) :
    standardFloorDensity u =
      (2 * Real.pi) ^ (-((Fintype.card ι : ℝ) - 1) / 2) * Real.exp (-‖u‖ ^ 2 / 2) := by
  have hc : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  simp only [standardFloorDensity, radialGaussianDensity, finrank_floorSpace, hc,
    mul_one]

omit [Nonempty ι] in
theorem standardFloorDensity_integral : ∫ u : FloorSpace ι, standardFloorDensity u = 1 :=
  integral_radialGaussianDensity (by norm_num : (0 : ℝ) < 1)

omit [Nonempty ι] in
theorem limitingFloorDensity_integral (hd : 2 ≤ Fintype.card ι) :
    ∫ u : FloorSpace ι, limitingFloorDensity u = 1 := by
  have hc : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  exact integral_radialGaussianDensity (div_pos (by linarith) (by linarith))

theorem limitingFloorDensity_formula (hd : 2 ≤ Fintype.card ι) (u : FloorSpace ι) :
    limitingFloorDensity u =
      (((Fintype.card ι : ℝ) - 1) / (2 * Real.pi * (Fintype.card ι : ℝ))) ^
        (((Fintype.card ι : ℝ) - 1) / 2) *
      Real.exp (-((Fintype.card ι : ℝ) - 1) / (2 * (Fintype.card ι : ℝ)) * ‖u‖ ^ 2) := by
  have hc : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hc0 : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hc1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hb : 0 < 2 * Real.pi * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (div_pos (by linarith) (by linarith))
  unfold limitingFloorDensity radialGaussianDensity
  rw [finrank_floorSpace, hcast,
    show -((Fintype.card ι : ℝ) - 1) / 2 = -(((Fintype.card ι : ℝ) - 1) / 2) by ring,
    Real.rpow_neg hb.le, ← Real.inv_rpow hb.le]
  congr 2
  · field_simp
  · field_simp

/-- The source's `ψ_E` really is the density of the actual orthogonal projection. -/
theorem projectedGaussian_eq_withDensity_standardFloorDensity :
    (standardGaussianProduct ι).map gaussianFloorMap =
      floorVolume.withDensity (fun u => ENNReal.ofReal (standardFloorDensity u)) :=
  projectedGaussian_eq_radialGaussian

/-- The source's `ρ*` really is the density of the actual scaled projection. -/
theorem scaledProjectedGaussian_eq_withDensity_limitingFloorDensity
    (hd : 2 ≤ Fintype.card ι) :
    (standardGaussianProduct ι).map scaledGaussianFloorMap =
      floorVolume.withDensity (fun u => ENNReal.ofReal (limitingFloorDensity u)) :=
  scaledProjectedGaussian_eq_radialGaussian hd

def normalCDFFloorMap (u : FloorSpace ι) : ι → ℝ := fun i => normalCDF (u.val i)

omit [Nonempty ι] in
theorem normalCDFFloorMap_continuous : Continuous (normalCDFFloorMap (ι := ι)) := by
  apply continuous_pi
  intro i
  exact normalCDF_continuous.comp
    ((PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp continuous_subtype_val)

/-- The limiting cube law, represented using the proved exact native floor density. -/
theorem limitingAntichainMeasure_eq_density_pushforward (hd : 2 ≤ Fintype.card ι) :
    limitingAntichainMeasure ι =
      (floorVolume.withDensity (fun u => ENNReal.ofReal (limitingFloorDensity u))).map
        normalCDFFloorMap := by
  rw [← scaledProjectedGaussian_eq_withDensity_limitingFloorDensity hd,
    Measure.map_map normalCDFFloorMap_continuous.measurable
      scaledGaussianFloorMap_continuous.measurable]
  rfl

/-- The normalized-power formula for `ρ*` used by the empirical concentration proof. -/
theorem limitingFloorDensity_eq_normalized_standard_power (hd : 2 ≤ Fintype.card ι)
    (u : FloorSpace ι) :
    limitingFloorDensity u =
      (standardFloorDensity u) ^ (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) /
        (∫ v : FloorSpace ι,
          (standardFloorDensity v) ^ (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ))) := by
  have hc : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hp : 0 < ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) :=
    div_pos (by linarith) (by linarith)
  have hinv : 1 / (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) =
      (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) := by field_simp
  have h := radialGaussianDensity_inverseVariance_eq_normalized_power
    (V := FloorSpace ι) hp u
  rw [hinv] at h
  exact h

end Antichain
