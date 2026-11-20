import Antichain.CubeModel
import Antichain.GaussianCDF
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
The actual independent standard-Gaussian sample and its coordinatewise
normal-CDF map to the actual independent uniform cube sample.

The scalar probability integral transform is proved from interval masses;
it is not assumed. Strict coordinate order is preserved exactly, so the
antichain probability is unchanged in every finite dimension and sample size.
-/

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- Exact interval masses of the actual uniform coordinate law. -/
theorem cubeCoordinateLaw_Iic (y : ℝ) :
    cubeCoordinateLaw (Iic y) = ENNReal.ofReal (min y 1) := by
  have hset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 (min y 1) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨hy, h0, h1⟩
      exact ⟨h0, hy, h1⟩
    · rintro ⟨h0, hy, h1⟩
      exact ⟨hy, h0, h1⟩
  rw [cubeCoordinateLaw, Measure.restrict_apply measurableSet_Iic, hset,
    Real.volume_Icc, sub_zero]

/-- The scalar probability integral transform for the actual standard
Gaussian and actual uniform restricted-Lebesgue coordinate measure. -/
theorem normalCDF_map_gaussianReal :
    (gaussianReal 0 1).map normalCDF = cubeCoordinateLaw := by
  letI : IsProbabilityMeasure ((gaussianReal 0 1).map normalCDF) :=
    Measure.isProbabilityMeasure_map normalCDF_continuous.measurable.aemeasurable
  apply Measure.ext_of_Iic
  intro y
  by_cases hy0 : y ≤ 0
  · have hpre : normalCDF ⁻¹' Iic y = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.notMem_empty, iff_false]
      have hx := (normalCDF_mem_Ioo x).1
      linarith
    rw [Measure.map_apply normalCDF_continuous.measurable measurableSet_Iic,
      hpre, measure_empty, cubeCoordinateLaw_Iic,
      ENNReal.ofReal_eq_zero.mpr ((min_le_left y 1).trans hy0)]
  · by_cases hy1 : 1 ≤ y
    · have hpre : normalCDF ⁻¹' Iic y = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        exact (normalCDF_mem_Ioo x).2.le.trans hy1
      rw [Measure.map_apply normalCDF_continuous.measurable measurableSet_Iic,
        hpre, measure_univ, cubeCoordinateLaw_Iic, min_eq_right hy1,
        ENNReal.ofReal_one]
    · obtain ⟨x, hx⟩ := normalCDF_onto_Ioo y ⟨lt_of_not_ge hy0, lt_of_not_ge hy1⟩
      have hpre : normalCDF ⁻¹' Iic y = Iic x := by
        ext t
        change normalCDF t ≤ y ↔ t ≤ x
        rw [← hx]
        exact normalCDF_strictMono.le_iff_le
      rw [Measure.map_apply normalCDF_continuous.measurable measurableSet_Iic,
        hpre, ← ofReal_cdf (gaussianReal 0 1) x, cubeCoordinateLaw_Iic]
      change ENNReal.ofReal (normalCDF x) = ENNReal.ofReal (min y 1)
      rw [hx, min_eq_left (le_of_not_ge hy1)]

theorem measurePreserving_normalCDF :
    MeasurePreserving normalCDF (gaussianReal 0 1) cubeCoordinateLaw :=
  ⟨normalCDF_continuous.measurable, normalCDF_map_gaussianReal⟩

theorem normalCDF_measurableEmbedding : MeasurableEmbedding normalCDF := by
  apply (normalCDF_strictMono.isEmbedding_of_ordConnected ?_).measurableEmbedding
  · rw [normalCDF_range]
    exact measurableSet_Ioo
  · rw [normalCDF_range]
    exact Set.ordConnected_Ioo

/-- The actual inverse normal CDF on `(0,1)`, extended measurably outside
that interval. Its values outside the range have no probabilistic role. -/
noncomputable def normalQuantile : ℝ → ℝ := normalCDF_measurableEmbedding.invFun

theorem normalQuantile_measurable : Measurable normalQuantile :=
  normalCDF_measurableEmbedding.measurable_invFun

theorem normalQuantile_normalCDF (x : ℝ) : normalQuantile (normalCDF x) = x :=
  normalCDF_measurableEmbedding.leftInverse_invFun x

theorem normalCDF_normalQuantile (y : ℝ) (hy : y ∈ Ioo 0 1) :
    normalCDF (normalQuantile y) = y := by
  obtain ⟨x, hx⟩ := normalCDF_onto_Ioo y hy
  rw [← hx, normalQuantile_normalCDF]

theorem normalQuantile_strictMonoOn : StrictMonoOn normalQuantile (Ioo 0 1) := by
  intro x hx y hy hxy
  apply normalCDF_strictMono.lt_iff_lt.mp
  rw [normalCDF_normalQuantile x hx, normalCDF_normalQuantile y hy]
  exact hxy

/-- Mapping the actual uniform coordinate back by the actual quantile gives
the actual standard Gaussian law, including the null cube endpoints. -/
theorem normalQuantile_map_cubeCoordinateLaw :
    cubeCoordinateLaw.map normalQuantile = gaussianReal 0 1 := by
  rw [← normalCDF_map_gaussianReal,
    Measure.map_map normalQuantile_measurable normalCDF_continuous.measurable]
  have hcomp : normalQuantile ∘ normalCDF = id := funext normalQuantile_normalCDF
  rw [hcomp, Measure.map_id]

theorem measurePreserving_normalQuantile :
    MeasurePreserving normalQuantile cubeCoordinateLaw (gaussianReal 0 1) :=
  ⟨normalQuantile_measurable, normalQuantile_map_cubeCoordinateLaw⟩

/-- A standard Gaussian vector with independent real coordinates. -/
noncomputable def gaussianPointLaw (d : ℕ) : Measure (CubePoint d) :=
  Measure.pi (fun _ : Fin d => gaussianReal 0 1)

instance gaussianPointLaw_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (gaussianPointLaw d) := by
  unfold gaussianPointLaw
  infer_instance

/-- Independent labelled standard Gaussian vectors. -/
noncomputable def gaussianSampleLaw (n d : ℕ) : Measure (CubeSample n d) :=
  Measure.pi (fun _ : Fin n => gaussianPointLaw d)

instance gaussianSampleLaw_isProbabilityMeasure (n d : ℕ) :
    IsProbabilityMeasure (gaussianSampleLaw n d) := by
  unfold gaussianSampleLaw
  infer_instance

noncomputable def gaussianToCubePoint (d : ℕ) (g : CubePoint d) : CubePoint d :=
  fun i => normalCDF (g i)

noncomputable def gaussianToCubeSample (n d : ℕ) (g : CubeSample n d) : CubeSample n d :=
  fun j => gaussianToCubePoint d (g j)

theorem continuous_gaussianToCubePoint (d : ℕ) : Continuous (gaussianToCubePoint d) :=
  continuous_pi (fun i => normalCDF_continuous.comp (continuous_apply i))

theorem continuous_gaussianToCubeSample (n d : ℕ) :
    Continuous (gaussianToCubeSample n d) :=
  continuous_pi (fun j => (continuous_gaussianToCubePoint d).comp (continuous_apply j))

/-- The actual Gaussian vector is mapped to independent uniform coordinates. -/
theorem measurePreserving_gaussianToCubePoint (d : ℕ) :
    MeasurePreserving (gaussianToCubePoint d) (gaussianPointLaw d) (cubePointLaw d) :=
  measurePreserving_pi (fun _ : Fin d => gaussianReal 0 1)
    (fun _ : Fin d => cubeCoordinateLaw) (fun _ => measurePreserving_normalCDF)

/-- The actual independent Gaussian sample is mapped to the actual uniform sample. -/
theorem measurePreserving_gaussianToCubeSample (n d : ℕ) :
    MeasurePreserving (gaussianToCubeSample n d)
      (gaussianSampleLaw n d) (cubeSampleLaw n d) :=
  measurePreserving_pi (fun _ : Fin n => gaussianPointLaw d)
    (fun _ : Fin n => cubePointLaw d) (fun _ => measurePreserving_gaussianToCubePoint d)

theorem gaussianToCubeSample_map_eq (n d : ℕ) :
    (gaussianSampleLaw n d).map (gaussianToCubeSample n d) = cubeSampleLaw n d :=
  (measurePreserving_gaussianToCubeSample n d).map_eq

noncomputable def cubeToGaussianPoint (d : ℕ) (x : CubePoint d) : CubePoint d :=
  fun i => normalQuantile (x i)

noncomputable def cubeToGaussianSample (n d : ℕ) (x : CubeSample n d) : CubeSample n d :=
  fun j => cubeToGaussianPoint d (x j)

theorem measurePreserving_cubeToGaussianPoint (d : ℕ) :
    MeasurePreserving (cubeToGaussianPoint d) (cubePointLaw d) (gaussianPointLaw d) :=
  measurePreserving_pi (fun _ : Fin d => cubeCoordinateLaw)
    (fun _ : Fin d => gaussianReal 0 1) (fun _ => measurePreserving_normalQuantile)

/-- Equation (1.2)'s inverse-coordinate transform of the actual uniform sample. -/
theorem measurePreserving_cubeToGaussianSample (n d : ℕ) :
    MeasurePreserving (cubeToGaussianSample n d)
      (cubeSampleLaw n d) (gaussianSampleLaw n d) :=
  measurePreserving_pi (fun _ : Fin n => cubePointLaw d)
    (fun _ : Fin n => gaussianPointLaw d) (fun _ => measurePreserving_cubeToGaussianPoint d)

theorem cubeToGaussianSample_map_eq (n d : ℕ) :
    (cubeSampleLaw n d).map (cubeToGaussianSample n d) = gaussianSampleLaw n d :=
  (measurePreserving_cubeToGaussianSample n d).map_eq

theorem cubeToGaussian_gaussianToCubeSample (n d : ℕ) (g : CubeSample n d) :
    cubeToGaussianSample n d (gaussianToCubeSample n d g) = g := by
  funext j i
  exact normalQuantile_normalCDF (g j i)

/-- All actual uniform sample coordinates lie in the quantile domain almost surely. -/
theorem ae_cubeSample_mem_openCube (n d : ℕ) :
    ∀ᵐ x ∂cubeSampleLaw n d, ∀ j i, x j i ∈ Ioo 0 1 := by
  rw [← gaussianToCubeSample_map_eq n d]
  apply (ae_map_iff (continuous_gaussianToCubeSample n d).measurable.aemeasurable ?_).mpr
  · exact Filter.Eventually.of_forall (fun g j i => normalCDF_mem_Ioo (g j i))
  · simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun i =>
      measurableSet_Ioo.preimage ((measurable_pi_apply i).comp (measurable_pi_apply j))))

theorem cubeToGaussianSample_antichain_iff_of_mem (n d : ℕ) (x : CubeSample n d)
    (hx : ∀ j i, x j i ∈ Ioo 0 1) :
    IsAntichain (cubeToGaussianSample n d x) ↔ IsAntichain x :=
  isAntichain_coordinatewise_iff_on normalQuantile_strictMonoOn x hx

theorem ae_cubeToGaussianSample_antichain_iff (n d : ℕ) :
    ∀ᵐ x ∂cubeSampleLaw n d,
      IsAntichain (cubeToGaussianSample n d x) ↔ IsAntichain x :=
  (ae_cubeSample_mem_openCube n d).mono
    (fun x hx => cubeToGaussianSample_antichain_iff_of_mem n d x hx)

theorem ae_gaussianToCube_cubeToGaussianSample (n d : ℕ) :
    ∀ᵐ x ∂cubeSampleLaw n d,
      gaussianToCubeSample n d (cubeToGaussianSample n d x) = x := by
  apply (ae_cubeSample_mem_openCube n d).mono
  intro x hx
  funext j i
  exact normalCDF_normalQuantile (x j i) (hx j i)

/-- The normal-CDF map preserves and reflects every actual strict antichain. -/
theorem gaussianToCubeSample_antichain_iff (n d : ℕ) (g : CubeSample n d) :
    IsAntichain (gaussianToCubeSample n d g) ↔ IsAntichain g :=
  isAntichain_coordinatewise_iff normalCDF_strictMono g

theorem gaussianToCubeSample_preimage_antichainEvent (n d : ℕ) :
    gaussianToCubeSample n d ⁻¹' strictAntichainEvent n d = strictAntichainEvent n d := by
  ext g
  exact gaussianToCubeSample_antichain_iff n d g

/-- The same probability transform holds after restricting to the actual
antichain event, before normalizing by its positive mass. -/
theorem gaussianToCubeSample_restrict_map_eq (n d : ℕ) :
    ((gaussianSampleLaw n d).restrict (strictAntichainEvent n d)).map
        (gaussianToCubeSample n d) =
      (cubeSampleLaw n d).restrict (strictAntichainEvent n d) := by
  have h := Measure.restrict_map (μ := gaussianSampleLaw n d)
    (continuous_gaussianToCubeSample n d).measurable
    (measurableSet_strictAntichainEvent n d)
  rw [gaussianToCubeSample_map_eq, gaussianToCubeSample_preimage_antichainEvent] at h
  exact h.symm

theorem measurePreserving_gaussianToCubeSample_restrict (n d : ℕ) :
    MeasurePreserving (gaussianToCubeSample n d)
      ((gaussianSampleLaw n d).restrict (strictAntichainEvent n d))
      ((cubeSampleLaw n d).restrict (strictAntichainEvent n d)) :=
  ⟨(continuous_gaussianToCubeSample n d).measurable,
    gaussianToCubeSample_restrict_map_eq n d⟩

/-- The actual inverse-coordinate law bridge, restricted to antichains. -/
theorem cubeToGaussianSample_restrict_map_eq (n d : ℕ) :
    ((cubeSampleLaw n d).restrict (strictAntichainEvent n d)).map
        (cubeToGaussianSample n d) =
      (gaussianSampleLaw n d).restrict (strictAntichainEvent n d) := by
  rw [← gaussianToCubeSample_restrict_map_eq n d,
    Measure.map_map (measurePreserving_cubeToGaussianSample n d).measurable
      (continuous_gaussianToCubeSample n d).measurable]
  have hcomp : cubeToGaussianSample n d ∘ gaussianToCubeSample n d = id :=
    funext (cubeToGaussian_gaussianToCubeSample n d)
  rw [hcomp, Measure.map_id]

theorem measurePreserving_cubeToGaussianSample_restrict (n d : ℕ) :
    MeasurePreserving (cubeToGaussianSample n d)
      ((cubeSampleLaw n d).restrict (strictAntichainEvent n d))
      ((gaussianSampleLaw n d).restrict (strictAntichainEvent n d)) :=
  ⟨(measurePreserving_cubeToGaussianSample n d).measurable,
    cubeToGaussianSample_restrict_map_eq n d⟩

/-- Any measurable nonnegative weight of the paper's inverse-normal
coordinates has exactly the corresponding Gaussian antichain integral. -/
theorem cube_antichain_lintegral_eq_gaussian (n d : ℕ)
    (F : CubeSample n d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in strictAntichainEvent n d,
      F (cubeToGaussianSample n d x) ∂cubeSampleLaw n d) =
      ∫⁻ g in strictAntichainEvent n d, F g ∂gaussianSampleLaw n d :=
  (measurePreserving_cubeToGaussianSample_restrict n d).lintegral_comp hF

/-- Transfer of every measurable nonnegative test over actual antichains. -/
theorem gaussian_antichain_lintegral_eq_cube (n d : ℕ)
    (F : CubeSample n d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g in strictAntichainEvent n d,
      F (gaussianToCubeSample n d g) ∂gaussianSampleLaw n d) =
      ∫⁻ x in strictAntichainEvent n d, F x ∂cubeSampleLaw n d :=
  (measurePreserving_gaussianToCubeSample_restrict n d).lintegral_comp hF

/-- Exact equality of Gaussian and uniform antichain masses; this is the
unweighted probability bridge used in the Gaussian-coordinate model. -/
theorem gaussianSampleLaw_antichainEvent_eq_mass (n d : ℕ) :
    gaussianSampleLaw n d (strictAntichainEvent n d) = antichainMass n d := by
  have h := (measurePreserving_gaussianToCubeSample n d).measure_preimage
    (measurableSet_strictAntichainEvent n d).nullMeasurableSet
  rw [gaussianToCubeSample_preimage_antichainEvent] at h
  exact h

theorem gaussianSampleLaw_antichainEvent_toReal (n d : ℕ) :
    (gaussianSampleLaw n d (strictAntichainEvent n d)).toReal =
      antichainProbability n d := by
  rw [gaussianSampleLaw_antichainEvent_eq_mass]
  rfl

theorem gaussianSampleLaw_antichainEvent_pos (n d : ℕ) (hd : 2 ≤ d) :
    0 < gaussianSampleLaw n d (strictAntichainEvent n d) := by
  rw [gaussianSampleLaw_antichainEvent_eq_mass]
  exact antichainMass_pos n d hd

end Antichain
