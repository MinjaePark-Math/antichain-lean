import Antichain.GaussianSample
import Antichain.NormalCDFLipschitz
import Antichain.GaussianCharacterization
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The actual general coordinate change in the introductory proof strategy:
inverse derivatives, volume Jacobian, Boltzmann density, and normalization to
the literal standard normal quantile. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 800000

/-- A real extension of the source's increasing interval bijection Q and its
actual inverse R. All regularity and Jacobian conclusions about R are derived.
Positive actual derivative is weaker than the source's smoothness premise. -/
structure IntervalCoordinateChange where
  forward : ℝ → ℝ
  inverse : ℝ → ℝ
  inverse_mem : ∀ s, inverse s ∈ Ioo (0 : ℝ) 1
  left_inverse : ∀ x ∈ Ioo (0 : ℝ) 1, inverse (forward x) = x
  right_inverse : ∀ s, forward (inverse s) = s
  forward_deriv_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < deriv forward x

namespace IntervalCoordinateChange

variable (C : IntervalCoordinateChange)

theorem forward_strictMonoOn : StrictMonoOn C.forward (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro x hx
    exact (differentiableAt_of_deriv_ne_zero (C.forward_deriv_pos x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    exact C.forward_deriv_pos x (by simpa only [interior_Ioo] using hx)

theorem inverse_strictMono : StrictMono C.inverse := by
  intro s t hst
  by_contra hnot
  have hQ := C.forward_strictMonoOn.monotoneOn (C.inverse_mem t) (C.inverse_mem s) (le_of_not_gt hnot)
  rw [C.right_inverse, C.right_inverse] at hQ
  exact (not_le_of_gt hst) hQ

theorem inverse_range : range C.inverse = Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    exact C.inverse_mem s
  · intro x hx
    exact ⟨C.forward x, C.left_inverse x hx⟩

theorem inverse_continuous : Continuous C.inverse := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply (C.inverse_strictMono.strictMonoOn univ).continuousAt_of_image_mem_nhds (by simp)
  rw [Set.image_univ, C.inverse_range]
  exact isOpen_Ioo.mem_nhds (C.inverse_mem s)

theorem inverse_hasDerivAt (s : ℝ) :
    HasDerivAt C.inverse (deriv C.forward (C.inverse s))⁻¹ s := by
  exact HasDerivAt.of_local_left_inverse C.inverse_continuous.continuousAt
    (differentiableAt_of_deriv_ne_zero (C.forward_deriv_pos _ (C.inverse_mem s)).ne').hasDerivAt
    (C.forward_deriv_pos _ (C.inverse_mem s)).ne' (Filter.Eventually.of_forall C.right_inverse)

/-- The source's scalar q=(Q⁻¹)′, an actual derivative. -/
def density (s : ℝ) : ℝ := deriv C.inverse s

theorem density_eq_inverse_forward_deriv (s : ℝ) :
    C.density s = (deriv C.forward (C.inverse s))⁻¹ := (C.inverse_hasDerivAt s).deriv

theorem density_pos (s : ℝ) : 0 < C.density s := by
  rw [C.density_eq_inverse_forward_deriv]
  exact inv_pos.mpr (C.forward_deriv_pos _ (C.inverse_mem s))

theorem inverse_hasDerivAt_density (s : ℝ) : HasDerivAt C.inverse (C.density s) s := by
  rw [C.density_eq_inverse_forward_deriv]
  exact C.inverse_hasDerivAt s

def inverseCoordinates (d : ℕ) (s : CubePoint d) : CubePoint d := fun i => C.inverse (s i)

def forwardCoordinates (d : ℕ) (x : CubePoint d) : CubePoint d := fun i => C.forward (x i)

def openCube (d : ℕ) : Set (CubePoint d) := univ.pi (fun _ => Ioo (0 : ℝ) 1)

theorem inverseCoordinates_injective (d : ℕ) : Function.Injective (C.inverseCoordinates d) := by
  intro s t h
  funext i
  exact C.inverse_strictMono.injective (congrFun h i)

theorem inverseCoordinates_range (d : ℕ) : range (C.inverseCoordinates d) = openCube d := by
  apply Set.Subset.antisymm
  · rintro _ ⟨s, rfl⟩ i _
    exact C.inverse_mem (s i)
  · intro x hx
    refine ⟨C.forwardCoordinates d x, ?_⟩
    funext i
    exact C.left_inverse (x i) (hx i (mem_univ i))

theorem forwardCoordinates_antichain_iff (n d : ℕ) (x : CubeSample n d)
    (hx : ∀ j i, x j i ∈ Ioo (0 : ℝ) 1) :
    IsAntichain (fun j => C.forwardCoordinates d (x j)) ↔ IsAntichain x :=
  isAntichain_coordinatewise_iff_on C.forward_strictMonoOn x hx

def inverseCoordinatesDerivative (d : ℕ) (s : CubePoint d) : CubePoint d →L[ℝ] CubePoint d :=
  ContinuousLinearMap.pi (fun i =>
    (((1 : ℝ →L[ℝ] ℝ).smulRight (C.density (s i))).comp (ContinuousLinearMap.proj i)))

theorem inverseCoordinates_hasFDerivAt (d : ℕ) (s : CubePoint d) :
    HasFDerivAt (C.inverseCoordinates d) (C.inverseCoordinatesDerivative d s) s := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (C.inverse_hasDerivAt_density (s i)).hasFDerivAt.comp s (hasFDerivAt_apply i s)

theorem inverseCoordinatesDerivative_det (d : ℕ) (s : CubePoint d) :
    (C.inverseCoordinatesDerivative d s).toLinearMap.det = ∏ i : Fin d, C.density (s i) := by
  have hs (a : ℝ) : (1 : ℝ →L[ℝ] ℝ).smulRight a = a • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [smul_eq_mul, mul_comm]
  simp_rw [inverseCoordinatesDerivative, hs]
  change (LinearMap.pi (fun i : Fin d =>
    ((C.density (s i)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj i))).det = _
  rw [LinearMap.det_pi]
  simp

theorem inverseCoordinates_jacobian_pos (d : ℕ) (s : CubePoint d) :
    0 < ∏ i : Fin d, C.density (s i) := Finset.prod_pos (fun i _ => C.density_pos (s i))

/-- The actual Lebesgue change of variables, not only a formal determinant:
dx = (product_i q(s_i)) ds for every nonnegative measurable-integral test. -/
theorem lintegral_coordinate_change (d : ℕ) (g : CubePoint d → ℝ≥0∞) :
    ∫⁻ x in openCube d, g x =
      ∫⁻ s, ENNReal.ofReal (∏ i : Fin d, C.density (s i)) * g (C.inverseCoordinates d s) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (CubePoint d))
    MeasurableSet.univ (fun s _ => (C.inverseCoordinates_hasFDerivAt d s).hasFDerivWithinAt)
    (C.inverseCoordinates_injective d).injOn g
  simpa only [Set.image_univ, C.inverseCoordinates_range, Measure.restrict_univ,
    C.inverseCoordinatesDerivative_det, abs_of_pos (C.inverseCoordinates_jacobian_pos d _)] using h

theorem integral_coordinate_change (d : ℕ) (g : CubePoint d → ℝ) :
    ∫ x in openCube d, g x =
      ∫ s, (∏ i : Fin d, C.density (s i)) * g (C.inverseCoordinates d s) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (CubePoint d))
    MeasurableSet.univ (fun s _ => (C.inverseCoordinates_hasFDerivAt d s).hasFDerivWithinAt)
    (C.inverseCoordinates_injective d).injOn g
  simpa only [Set.image_univ, C.inverseCoordinates_range, Measure.restrict_univ,
    C.inverseCoordinatesDerivative_det, abs_of_pos (C.inverseCoordinates_jacobian_pos d _), smul_eq_mul] using h

/-- Equality of actual measures behind the change-of-variables notation. -/
theorem inverseCoordinates_map_withDensity (d : ℕ) :
    (volume.withDensity (fun s : CubePoint d => ENNReal.ofReal (∏ i : Fin d, C.density (s i)))).map
      (C.inverseCoordinates d) = (volume : Measure (CubePoint d)).restrict (openCube d) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (CubePoint d))
    MeasurableSet.univ.nullMeasurableSet
    (fun s _ => (C.inverseCoordinates_hasFDerivAt d s).hasFDerivWithinAt)
    (C.inverseCoordinates_injective d).injOn
  simpa only [Measure.restrict_univ, Set.image_univ, C.inverseCoordinates_range,
    C.inverseCoordinatesDerivative_det, abs_of_pos (C.inverseCoordinates_jacobian_pos d _)] using h

def inverseEuclideanCoordinates (d : ℕ) (s : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (C.inverseCoordinates d (WithLp.ofLp s))

/-- The same formula for the literal native Euclidean volume, using the
proved volume-preserving Pi-to-Euclidean coordinate equivalence. -/
theorem euclidean_lintegral_coordinate_change (d : ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ x in ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) '' openCube d), g x =
      ∫⁻ s : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (∏ i : Fin d, C.density (s i)) * g (C.inverseEuclideanCoordinates d s) := by
  have hp : MeasurePreserving (WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) volume volume :=
    PiLp.volume_preserving_toLp (Fin d)
  have he : MeasurableEmbedding (WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) :=
    (EuclideanSpace.measurableEquiv (Fin d)).symm.measurableEmbedding
  rw [← hp.setLIntegral_comp_emb he g (openCube d), ← hp.lintegral_comp_emb he]
  exact C.lintegral_coordinate_change d (fun x => g (WithLp.toLp 2 x))

def potential (s : ℝ) : ℝ := -Real.log (C.density s)

theorem product_density_eq_boltzmann (d : ℕ) (s : CubePoint d) :
    (∏ i : Fin d, C.density (s i)) = Real.exp (-(∑ i : Fin d, C.potential (s i))) := by
  simp only [potential, Finset.sum_neg_distrib, neg_neg, Real.exp_sum,
    Real.exp_log (C.density_pos _)]

/-- Identifying the integration constant uses the actual interval range,
not an assumed equality of cumulative distribution functions. -/
theorem inverse_eq_of_same_derivative {F : ℝ → ℝ}
    (hF : ∀ s, HasDerivAt F (C.density s) s)
    (hFbot : Tendsto F atBot (𝓝 0)) (hFtop : Tendsto F atTop (𝓝 1)) :
    C.inverse = F := by
  have hd : Differentiable ℝ (fun s => C.inverse s - F s) := fun s =>
    ((C.inverse_hasDerivAt_density s).sub (hF s)).differentiableAt
  have hz (s : ℝ) : deriv (fun t => C.inverse t - F t) s = 0 := by
    simpa only [sub_self] using ((C.inverse_hasDerivAt_density s).sub (hF s)).deriv
  let K := C.inverse 0 - F 0
  have heq (s : ℝ) : C.inverse s = F s + K := by
    have hc := is_const_of_deriv_eq_zero hd hz s 0
    dsimp [K]
    linarith
  have hbot : Tendsto C.inverse atBot (𝓝 K) := by
    rw [show C.inverse = (fun s => F s + K) from funext heq]
    simpa only [zero_add] using hFbot.add_const K
  have htop : Tendsto C.inverse atTop (𝓝 (1 + K)) := by
    rw [show C.inverse = (fun s => F s + K) from funext heq]
    exact hFtop.add_const K
  have hK0 : 0 ≤ K := ge_of_tendsto hbot (Filter.Eventually.of_forall (fun s => (C.inverse_mem s).1.le))
  have hK1 : 1 + K ≤ 1 := le_of_tendsto htop (Filter.Eventually.of_forall (fun s => (C.inverse_mem s).2.le))
  have hK : K = 0 := by linarith
  funext s
  rw [heq, hK, add_zero]

theorem inverse_eq_normalCDF (hdensity : ∀ s, C.density s = standardNormalPDF s) :
    C.inverse = normalCDF := by
  apply C.inverse_eq_of_same_derivative
  · intro s
    rw [hdensity]
    exact normalCDF_hasDerivAt s
  · exact normalCDF_tendsto_atBot
  · exact normalCDF_tendsto_atTop

/-- Once origin and scale make the Gaussian density standard, the actual
coordinate map is the literal inverse standard normal CDF on its domain. -/
theorem forward_eq_normalQuantile (hdensity : ∀ s, C.density s = standardNormalPDF s)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : C.forward x = normalQuantile x := by
  have hi := C.left_inverse x hx
  rw [C.inverse_eq_normalCDF hdensity] at hi
  exact normalCDF_strictMono.injective (hi.trans (normalCDF_normalQuantile x hx).symm)

theorem inverse_eq_gaussianCDF_location_scale (m sigma : ℝ) (hsigma : 0 < sigma)
    (hdensity : ∀ s, C.density s = sigma⁻¹ * standardNormalPDF ((s - m) / sigma)) :
    C.inverse = fun s => normalCDF ((s - m) / sigma) := by
  apply C.inverse_eq_of_same_derivative
  · intro s
    have ha : HasDerivAt (fun t : ℝ => (t - m) / sigma) sigma⁻¹ s := by
      simpa only [one_div] using ((hasDerivAt_id s).sub_const m).div_const sigma
    convert (normalCDF_hasDerivAt ((s - m) / sigma)).comp s ha using 1
    rw [hdensity]
    ring
  · apply normalCDF_tendsto_atBot.comp
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [eventually_le_atBot (m + b * sigma)] with s hs
    exact (div_le_iff₀ hsigma).mpr (by linarith)
  · apply normalCDF_tendsto_atTop.comp
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (m + b * sigma)] with s hs
    exact (le_div_iff₀ hsigma).mpr (by linarith)

theorem forward_eq_gaussianQuantile_location_scale (m sigma : ℝ) (hsigma : 0 < sigma)
    (hdensity : ∀ s, C.density s = sigma⁻¹ * standardNormalPDF ((s - m) / sigma))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : C.forward x = m + sigma * normalQuantile x := by
  have hi := C.left_inverse x hx
  rw [C.inverse_eq_gaussianCDF_location_scale m sigma hsigma hdensity] at hi
  have heq := normalCDF_strictMono.injective (hi.trans (normalCDF_normalQuantile x hx).symm)
  have hh := (div_eq_iff hsigma.ne').mp heq
  linarith

theorem gaussian_density_eq_scaled_standardPDF {a : ℝ} (ha : 0 < a) (m s : ℝ) :
    (Real.sqrt (Real.pi / a))⁻¹ * Real.exp (-a * (s - m) ^ 2) =
      Real.sqrt (2 * a) * standardNormalPDF (Real.sqrt (2 * a) * (s - m)) := by
  have hr : Real.sqrt (Real.pi / a) * Real.sqrt (2 * a) = Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / a)]
    congr 1
    field_simp
  have hp : (Real.sqrt (Real.pi / a))⁻¹ = Real.sqrt (2 * a) * (Real.sqrt (2 * Real.pi))⁻¹ := by
    have h1 : Real.sqrt (Real.pi / a) ≠ 0 := by positivity
    have h2 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp
    simpa only [mul_comm] using hr.symm
  have he : -(Real.sqrt (2 * a) * (s - m)) ^ 2 / 2 = -a * (s - m) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * a)]
    ring
  rw [standardNormalPDF, he, hp]
  ring

/-- The exact affine bridge from the Gaussian density form proved by the
location/arrangement characterization to the actual inverse normal CDF. -/
theorem gaussian_family_coordinate_source {a : ℝ} (ha : 0 < a) (m : ℝ)
    (hdensity : ∀ s, C.density s =
      (Real.sqrt (Real.pi / a))⁻¹ * Real.exp (-a * (s - m) ^ 2)) :
    (∀ s, C.inverse s = normalCDF (Real.sqrt (2 * a) * (s - m))) ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, C.forward x = m + normalQuantile x / Real.sqrt (2 * a) := by
  have hs : 0 < (Real.sqrt (2 * a))⁻¹ := by positivity
  have hstandard (s : ℝ) : C.density s =
      ((Real.sqrt (2 * a))⁻¹)⁻¹ * standardNormalPDF ((s - m) / (Real.sqrt (2 * a))⁻¹) := by
    rw [hdensity, gaussian_density_eq_scaled_standardPDF ha m s]
    simp only [inv_inv, div_inv_eq_mul, mul_comm (s - m)]
  constructor
  · intro s
    have h := congrFun (C.inverse_eq_gaussianCDF_location_scale m _ hs hstandard) s
    simpa only [div_inv_eq_mul, mul_comm (s - m)] using h
  · intro x hx
    have h := C.forward_eq_gaussianQuantile_location_scale m _ hs hstandard hx
    simpa only [div_eq_mul_inv, mul_comm (Real.sqrt (2 * a))⁻¹] using h

theorem scalarInverseDerivative_det (s : ℝ) :
    (((1 : ℝ →L[ℝ] ℝ).smulRight (C.density s)).toLinearMap).det = C.density s := by
  have heq : (1 : ℝ →L[ℝ] ℝ).smulRight (C.density s) =
      C.density s • ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [smul_eq_mul, mul_comm]
  rw [heq]
  change ((C.density s) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).det = _
  simp

theorem inverse_map_withDensity :
    (volume.withDensity (fun s : ℝ => ENNReal.ofReal (C.density s))).map C.inverse =
      (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℝ)
    MeasurableSet.univ.nullMeasurableSet
    (fun s _ => (C.inverse_hasDerivAt_density s).hasFDerivAt.hasFDerivWithinAt)
    C.inverse_strictMono.injective.injOn
  simpa only [Measure.restrict_univ, Set.image_univ, C.inverse_range,
    C.scalarInverseDerivative_det, abs_of_pos (C.density_pos _)] using h

theorem density_lintegral_one : ∫⁻ s : ℝ, ENNReal.ofReal (C.density s) = 1 := by
  have h := congrArg (fun mu : Measure ℝ => mu univ) C.inverse_map_withDensity
  dsimp only at h
  rw [Measure.map_apply C.inverse_continuous.measurable MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_apply MeasurableSet.univ] at h
  simpa only [Measure.restrict_univ, Set.univ_inter, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one] using h

theorem density_integrable : Integrable C.density := by
  refine ⟨(measurable_deriv C.inverse).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun s => (C.density_pos s).le))).mpr
  rw [C.density_lintegral_one]
  exact ENNReal.one_lt_top

theorem density_integral_one : ∫ s : ℝ, C.density s = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun s => (C.density_pos s).le)) C.density_integrable.aestronglyMeasurable,
    C.density_lintegral_one, ENNReal.toReal_one]

/-- The complete source implication: separation of the actual transformed
uniform density forces an affine standard-normal quantile coordinate. Its
probability normalization is proved from the actual change of variables. -/
theorem separated_coordinate_is_affine_normalQuantile
    (hsmooth : ContDiff ℝ 2 C.density)
    (hsep : LocationArrangementSeparation (fun s => -Real.log (C.density s))) :
    ∃ a : ℝ, 0 < a ∧ ∃ m : ℝ,
      (∀ s, C.inverse s = normalCDF (Real.sqrt (2 * a) * (s - m))) ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, C.forward x = m + normalQuantile x / Real.sqrt (2 * a) := by
  obtain ⟨a, ha, m, hfamily⟩ := gaussian_location_arrangement_characterization_source C.density
    C.density_pos hsmooth C.density_integrable C.density_integral_one hsep
  exact ⟨a, ha, m, C.gaussian_family_coordinate_source ha m hfamily⟩

end IntervalCoordinateChange

end Antichain
