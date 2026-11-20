import Antichain.EmpiricalConcentration
import Antichain.LimitMarginals

/-! The manuscript's probability space of the actual closed-cube subtype.
The coordinate clamp is a continuous retraction, which gives an explicit
weak embedding and transfers the empirical theorem from ambient coordinates. -/

noncomputable section

set_option maxHeartbeats 800000

namespace Antichain

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

abbrev ClosedCubePoint (d : ℕ) := {x : CubePoint d // x ∈ cubePointSet d}
abbrev ClosedCubeSample (n d : ℕ) := Fin n → ClosedCubePoint d

def cubeClamp (d : ℕ) (x : CubePoint d) : ClosedCubePoint d :=
  ⟨fun i => max 0 (min 1 (x i)), fun i _ =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩

theorem cubeClamp_continuous (d : ℕ) : Continuous (cubeClamp d) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_const.min (continuous_apply i))

@[simp] theorem cubeClamp_subtype (d : ℕ) (x : ClosedCubePoint d) : cubeClamp d x.val = x := by
  apply Subtype.ext
  funext i
  have hx := x.property i (mem_univ i)
  simp only [cubeClamp, min_eq_right hx.2, max_eq_right hx.1]

@[simp] theorem cubeClamp_idempotent (d : ℕ) (x : CubePoint d) :
    cubeClamp d (cubeClamp d x).val = cubeClamp d x := cubeClamp_subtype d _

def includeClosedCubeProbability (d : ℕ) (mu : ProbabilityMeasure (ClosedCubePoint d)) :
    ProbabilityMeasure (CubePoint d) := mu.map measurable_subtype_coe.aemeasurable

def projectClosedCubeProbability (d : ℕ) (mu : ProbabilityMeasure (CubePoint d)) :
    ProbabilityMeasure (ClosedCubePoint d) :=
  mu.map (cubeClamp_continuous d).measurable.aemeasurable

theorem includeClosedCubeProbability_continuous (d : ℕ) : Continuous (includeClosedCubeProbability d) :=
  ProbabilityMeasure.continuous_map continuous_subtype_val

theorem projectClosedCubeProbability_continuous (d : ℕ) : Continuous (projectClosedCubeProbability d) :=
  ProbabilityMeasure.continuous_map (cubeClamp_continuous d)

@[simp] theorem project_includeClosedCubeProbability (d : ℕ)
    (mu : ProbabilityMeasure (ClosedCubePoint d)) :
    projectClosedCubeProbability d (includeClosedCubeProbability d mu) = mu := by
  apply Subtype.ext
  change ((mu : Measure (ClosedCubePoint d)).map Subtype.val).map (cubeClamp d) = _
  rw [Measure.map_map (cubeClamp_continuous d).measurable measurable_subtype_coe]
  have heq : cubeClamp d ∘ Subtype.val = id := funext (cubeClamp_subtype d)
  rw [heq, Measure.map_id]
  rfl

/-- Actual weak probability measures on the closed cube embed into ambient
weak probability measures. This is proved by the explicit continuous inverse
on the image, so the ambient/subspace weak agreement is not assumed. -/
theorem includeClosedCubeProbability_isEmbedding (d : ℕ) :
    Topology.IsEmbedding (includeClosedCubeProbability d) := by
  have hInv : Function.LeftInverse (projectClosedCubeProbability d) (includeClosedCubeProbability d) :=
    project_includeClosedCubeProbability d
  exact hInv.isEmbedding (projectClosedCubeProbability_continuous d)
    (includeClosedCubeProbability_continuous d)

theorem closedCubeProbability_tendsto_iff {I : Type*} {F : Filter I} (d : ℕ)
    (mu : ProbabilityMeasure (ClosedCubePoint d)) (nu : I → ProbabilityMeasure (ClosedCubePoint d)) :
    Tendsto nu F (𝓝 mu) ↔
      Tendsto (fun i => includeClosedCubeProbability d (nu i)) F
        (𝓝 (includeClosedCubeProbability d mu)) :=
  (includeClosedCubeProbability_isEmbedding d).isInducing.tendsto_nhds_iff

def closedCubeLimitingProbability (d : ℕ) : ProbabilityMeasure (ClosedCubePoint d) :=
  projectClosedCubeProbability d (limitingCubeProbability d)

def closedCubeEmpiricalProbability (n d : ℕ) (x : CubeSample n d) :
    ProbabilityMeasure (ClosedCubePoint d) :=
  projectClosedCubeProbability d (empiricalCubeProbability n d x)

theorem closedCubeEmpiricalProbability_continuous (n d : ℕ) :
    Continuous (closedCubeEmpiricalProbability n d) :=
  (projectClosedCubeProbability_continuous d).comp (empiricalCubeProbability_continuous n d)

theorem closedCubeEmpiricalProbability_integral (n d : ℕ) (hn : 0 < n)
    (x : CubeSample n d) (g : ClosedCubePoint d →ᵇ ℝ) :
    ∫ u, g u ∂(closedCubeEmpiricalProbability n d x : Measure (ClosedCubePoint d)) =
      (∑ j, g (cubeClamp d (x j))) / (n : ℝ) := by
  change ∫ u, g u ∂((empiricalCubeProbability n d x : Measure (CubePoint d)).map (cubeClamp d)) = _
  rw [integral_map (cubeClamp_continuous d).measurable.aemeasurable g.continuous.measurable.aestronglyMeasurable]
  exact empiricalCubeProbability_integral n d hn x
    (g.compContinuous ⟨cubeClamp d, cubeClamp_continuous d⟩)

/-- The empirical measure is literally the equal-weight law of the original
closed-cube sample, since the clamp fixes every cube point. -/
theorem closedCubeEmpiricalProbability_integral_of_cube (n d : ℕ) (hn : 0 < n)
    (x : CubeSample n d) (hx : ∀ j, x j ∈ cubePointSet d) (g : ClosedCubePoint d →ᵇ ℝ) :
    ∫ u, g u ∂(closedCubeEmpiricalProbability n d x : Measure (ClosedCubePoint d)) =
      (∑ j, g ⟨x j, hx j⟩) / (n : ℝ) := by
  rw [closedCubeEmpiricalProbability_integral n d hn]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg g (cubeClamp_subtype d ⟨x j, hx j⟩)

/-- Theorem 2.1 in the actual closed-cube probability-measure space.
The finite-dimensional coordinate representation is merely the sample carrier. -/
theorem empirical_closed_cube_weak_concentration {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))}
    (hU : U ∈ 𝓝 (closedCubeLimitingProbability d)) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedCubeEmpiricalProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  change U ∈ 𝓝 (projectClosedCubeProbability d (limitingCubeProbability d)) at hU
  have hV : projectClosedCubeProbability d ⁻¹' U ∈ 𝓝 (limitingCubeProbability d) :=
    ((projectClosedCubeProbability_continuous d).tendsto (limitingCubeProbability d)).eventually hU
  obtain ⟨α, hα, htail⟩ := empirical_cube_weak_concentration hd H hV
  refine ⟨α, hα, htail.mono (fun n hn => ?_)⟩
  change cubeAntichainLaw n d {x | projectClosedCubeProbability d (empiricalCubeProbability n d x) ∉ U} ≤ _ at hn
  exact hn

theorem include_projectClosedCubeProbability_of_ae (d : ℕ)
    (mu : ProbabilityMeasure (CubePoint d)) (hmu : ∀ᵐ x ∂(mu : Measure (CubePoint d)), x ∈ cubePointSet d) :
    includeClosedCubeProbability d (projectClosedCubeProbability d mu) = mu := by
  apply Subtype.ext
  change ((mu : Measure (CubePoint d)).map (cubeClamp d)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe (cubeClamp_continuous d).measurable]
  have heq : (Subtype.val ∘ cubeClamp d) =ᵐ[(mu : Measure (CubePoint d))] id := by
    filter_upwards [hmu] with x hx
    exact congrArg Subtype.val (cubeClamp_subtype d ⟨x, hx⟩)
  rw [Measure.map_congr heq, Measure.map_id]
  rfl

theorem include_closedCubeLimitingProbability (d : ℕ) :
    includeClosedCubeProbability d (closedCubeLimitingProbability d) = limitingCubeProbability d := by
  apply include_projectClosedCubeProbability_of_ae
  filter_upwards [limitingAntichainMeasure_mem_closed_cube (ι := Fin d)] with x hx
  exact fun i _ => hx i

def liftCubeSample (n d : ℕ) (x : CubeSample n d) : ClosedCubeSample n d :=
  fun j => cubeClamp d (x j)

def includeClosedCubeSample (n d : ℕ) (x : ClosedCubeSample n d) : CubeSample n d :=
  fun j => (x j).val

theorem liftCubeSample_continuous (n d : ℕ) : Continuous (liftCubeSample n d) :=
  continuous_pi (fun j => (cubeClamp_continuous d).comp (continuous_apply j))

theorem includeClosedCubeSample_continuous (n d : ℕ) : Continuous (includeClosedCubeSample n d) :=
  continuous_pi (fun j => continuous_subtype_val.comp (continuous_apply j))

def closedCubeAntichainLaw (n d : ℕ) : Measure (ClosedCubeSample n d) :=
  (cubeAntichainLaw n d).map (liftCubeSample n d)

theorem closedCubeAntichainLaw_isProbabilityMeasure (n d : ℕ) (hd : 2 ≤ d) :
    IsProbabilityMeasure (closedCubeAntichainLaw n d) := by
  letI := cubeAntichainLaw_isProbabilityMeasure n d hd
  exact Measure.isProbabilityMeasure_map (liftCubeSample_continuous n d).measurable.aemeasurable

theorem cubeAntichainLaw_ae_closed_cube (n d : ℕ) :
    ∀ᵐ x ∂cubeAntichainLaw n d, x ∈ cubeSampleSet n d := by
  unfold cubeAntichainLaw
  exact Measure.ae_smul_measure (ae_restrict_of_ae (ae_cubeSample_mem_cube n d)) _

theorem closedCubeAntichainLaw_include_map_eq (n d : ℕ) :
    (closedCubeAntichainLaw n d).map (includeClosedCubeSample n d) = cubeAntichainLaw n d := by
  rw [closedCubeAntichainLaw,
    Measure.map_map (includeClosedCubeSample_continuous n d).measurable (liftCubeSample_continuous n d).measurable]
  have heq : (includeClosedCubeSample n d ∘ liftCubeSample n d) =ᵐ[cubeAntichainLaw n d] id := by
    filter_upwards [cubeAntichainLaw_ae_closed_cube n d] with x hx
    funext j
    exact congrArg Subtype.val (cubeClamp_subtype d ⟨x j, hx j (mem_univ j)⟩)
  rw [Measure.map_congr heq, Measure.map_id]

def empiricalClosedCubeProbability (n d : ℕ) (x : ClosedCubeSample n d) :
    ProbabilityMeasure (ClosedCubePoint d) :=
  closedCubeEmpiricalProbability n d (includeClosedCubeSample n d x)

theorem empiricalClosedCubeProbability_continuous (n d : ℕ) :
    Continuous (empiricalClosedCubeProbability n d) :=
  (closedCubeEmpiricalProbability_continuous n d).comp (includeClosedCubeSample_continuous n d)

theorem empiricalClosedCubeProbability_integral (n d : ℕ) (hn : 0 < n)
    (x : ClosedCubeSample n d) (g : ClosedCubePoint d →ᵇ ℝ) :
    ∫ u, g u ∂(empiricalClosedCubeProbability n d x : Measure (ClosedCubePoint d)) =
      (∑ j, g (x j)) / (n : ℝ) := by
  rw [empiricalClosedCubeProbability, closedCubeEmpiricalProbability_integral n d hn]
  simp only [includeClosedCubeSample, cubeClamp_subtype]

theorem empiricalClosedCubeProbability_lift (n d : ℕ) (hn : 0 < n) (x : CubeSample n d) :
    empiricalClosedCubeProbability n d (liftCubeSample n d x) = closedCubeEmpiricalProbability n d x := by
  letI : IsProbabilityMeasure (closedCubeEmpiricalProbability n d x : Measure (ClosedCubePoint d)) :=
    (closedCubeEmpiricalProbability n d x).prop
  letI : IsProbabilityMeasure (empiricalClosedCubeProbability n d (liftCubeSample n d x) :
      Measure (ClosedCubePoint d)) := (empiricalClosedCubeProbability n d (liftCubeSample n d x)).prop
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [empiricalClosedCubeProbability_integral n d hn, closedCubeEmpiricalProbability_integral n d hn]
  rfl

/-- The same theorem on the literal closed-cube sample space, under the
actual lifted conditional law, with the genuine equal-weight empirical law. -/
theorem closed_cube_empirical_source {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U)
    (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      closedCubeAntichainLaw n d {x | empiricalClosedCubeProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨α, hα, htail⟩ := empirical_closed_cube_weak_concentration hd H (hUopen.mem_nhds hUmem)
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hmeas : MeasurableSet {x : ClosedCubeSample n d | empiricalClosedCubeProbability n d x ∉ U} := by
    change MeasurableSet ((empiricalClosedCubeProbability n d) ⁻¹' U)ᶜ
    exact (hUopen.preimage (empiricalClosedCubeProbability_continuous n d)).measurableSet.compl
  rw [closedCubeAntichainLaw, Measure.map_apply (liftCubeSample_continuous n d).measurable
    hmeas]
  have hset : liftCubeSample n d ⁻¹' {x | empiricalClosedCubeProbability n d x ∉ U} =
      {x | closedCubeEmpiricalProbability n d x ∉ U} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, empiricalClosedCubeProbability_lift n d hnpos]
  rw [hset]
  exact hn

theorem closed_cube_empirical_neighborhood_concentration {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))}
    (hU : U ∈ 𝓝 (closedCubeLimitingProbability d)) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      closedCubeAntichainLaw n d {x | empiricalClosedCubeProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨V, hVU, hVopen, hVmem⟩ := mem_nhds_iff.mp hU
  obtain ⟨α, hα, htail⟩ := closed_cube_empirical_source hd H hVopen hVmem
  refine ⟨α, hα, htail.mono (fun n hn => (measure_mono ?_).trans hn)⟩
  intro x hx
  change empiricalClosedCubeProbability n d x ∉ U at hx
  change empiricalClosedCubeProbability n d x ∉ V
  exact fun hmem => hx (hVU hmem)

def empiricalClosedSetFrequency (n d : ℕ) (B : Set (ClosedCubePoint d)) (x : ClosedCubeSample n d) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => x j ∈ B)).card : ℝ) / (n : ℝ)

theorem empiricalClosedCubeProbability_set_eq_frequency (n d : ℕ) (hn : 0 < n)
    {B : Set (ClosedCubePoint d)} (hB : MeasurableSet B) (x : ClosedCubeSample n d) :
    ((empiricalClosedCubeProbability n d x : Measure (ClosedCubePoint d)) B).toReal =
      empiricalClosedSetFrequency n d B x := by
  classical
  change (((empiricalCubeProbability n d (includeClosedCubeSample n d x) : Measure (CubePoint d)).map
    (cubeClamp d)) B).toReal = _
  rw [Measure.map_apply (cubeClamp_continuous d).measurable hB,
    empiricalCubeProbability_set_eq_frequency n d hn]
  simp only [empiricalSetFrequency, empiricalClosedSetFrequency, includeClosedCubeSample,
    Set.mem_preimage, cubeClamp_subtype]

/-- The source continuity-set assertion on the literal closed-cube space,
with its relative frontier and the literal fraction of sampled labels. -/
theorem closed_cube_continuity_set_concentration {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) {B : Set (ClosedCubePoint d)}
    (hB : MeasurableSet B)
    (hfrontier : (closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) (frontier B) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      closedCubeAntichainLaw n d {x | ε ≤ |empiricalClosedSetFrequency n d B x -
        ((closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) B).toReal|} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨α, hα, htail⟩ := continuity_set_concentration_of_weak
    (fun n => closedCubeAntichainLaw n d) (fun n x => empiricalClosedCubeProbability n d x)
    (closedCubeLimitingProbability d)
    (fun _ hU => closed_cube_empirical_neighborhood_concentration hd H hU) hfrontier hε
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have heq : {x : ClosedCubeSample n d | ε ≤
      |((empiricalClosedCubeProbability n d x : Measure (ClosedCubePoint d)) B).toReal -
        ((closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) B).toReal|} =
      {x | ε ≤ |empiricalClosedSetFrequency n d B x -
        ((closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) B).toReal|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [empiricalClosedCubeProbability_set_eq_frequency n d hnpos hB]
  rwa [heq] at hn

end Antichain
