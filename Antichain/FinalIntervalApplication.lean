import Antichain.WeakBruhatIntervals
import Antichain.IntervalGaussianPredictor
import Antichain.RankBoxes
import Antichain.RankPermuton
import Antichain.ProbabilityConsequences

/-! Literal midpoint interval clouds and uniform-law transport for Proposition 6.4. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

theorem rankMidpoint_mem_Ioo {n : ℕ} (r : Fin n) : rankMidpoint n r ∈ Ioo (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  have hr : (r.val : ℝ) + 1 ≤ n := by exact_mod_cast r.isLt
  constructor
  · exact div_pos (by positivity) hn
  · exact (div_lt_one hn).mpr (by linarith)

theorem rankMidpoint_rev {n : ℕ} (r : Fin n) : rankMidpoint n r.rev = 1 - rankMidpoint n r := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  rw [rankMidpoint, rankMidpoint, Fin.val_rev, Nat.cast_sub (Nat.succ_le_of_lt r.isLt),
    Nat.cast_succ]
  field_simp
  ring

def intervalRankCloud (n : ℕ) (I : WeakBruhatInterval n) : CubeSample n 3 :=
  fun j ↦ ![rankMidpoint n j, rankMidpoint n (I.val.1 j), rankMidpoint n (I.val.2 j)]

def avoidanceRankTripleCloud (n : ℕ) (π : Fin 2 → Equiv.Perm (Fin n)) : CubeSample n 3 :=
  fun j ↦ ![rankMidpoint n j, rankMidpoint n (π 0 j), rankMidpoint n (π 1 j)]

theorem intervalRankCloud_mem_openCube (n : ℕ) (I : WeakBruhatInterval n) (j : Fin n) :
    intervalRankCloud n I j ∈ openCubeThree := by
  intro i _
  fin_cases i <;> exact rankMidpoint_mem_Ioo _

theorem intervalRankCloud_avoidance_map (n : ℕ) (π : AvoidancePermutation n 2) (j : Fin n) :
    intervalRankCloud n (avoidanceWeakBruhatEquiv n π) j = intervalCubeMap (avoidanceRankTripleCloud n π.val j) := by
  funext i
  fin_cases i
  · rfl
  · change rankMidpoint n (reversePermutationValues (π.val 1) j) = 1 - rankMidpoint n (π.val 1 j)
    exact rankMidpoint_rev _
  · rfl

def intervalRankEmpiricalProbability (n : ℕ) (I : WeakBruhatInterval n) : ProbabilityMeasure (CubePoint 3) :=
  empiricalCubeProbability n 3 (intervalRankCloud n I)

theorem empiricalCubeMeasure_map_continuous {n d e : ℕ} (hn : 0 < n)
    (f : CubePoint d → CubePoint e) (hf : Continuous f) (x : CubeSample n d) :
    (empiricalCubeMeasure n d x).map f = empiricalCubeMeasure n e (fun j ↦ f (x j)) := by
  rw [empiricalCubeMeasure, if_neg hn.ne', empiricalCubeMeasure, if_neg hn.ne', Measure.map_smul]
  rw [← Measure.sum_fintype, ← Measure.sum_fintype, Measure.map_sum hf.measurable.aemeasurable]
  congr 1
  apply congrArg Measure.sum
  funext j
  exact Measure.map_dirac hf.measurable (x j)

theorem intervalRankEmpiricalProbability_avoidance_map (n : ℕ) (hn : 0 < n)
    (π : AvoidancePermutation n 2) :
    intervalRankEmpiricalProbability n (avoidanceWeakBruhatEquiv n π) =
      (empiricalCubeProbability n 3 (avoidanceRankTripleCloud n π.val)).map
        intervalCubeMap_continuous.measurable.aemeasurable := by
  apply Subtype.ext
  change empiricalCubeMeasure n 3 (intervalRankCloud n (avoidanceWeakBruhatEquiv n π)) =
    (empiricalCubeMeasure n 3 (avoidanceRankTripleCloud n π.val)).map intervalCubeMap
  rw [empiricalCubeMeasure_map_continuous hn _ intervalCubeMap_continuous]
  congr 1
  funext j
  exact intervalRankCloud_avoidance_map n π j

theorem finite_uniform_subtype_map_uniformOn {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (C : Set K) [Fintype C] [Nonempty C] :
    ((PMF.uniformOfFintype C).toMeasure).map (Subtype.val : C → K) = uniformOn C := by
  classical
  have hC : MeasurableSet C := C.toFinite.measurableSet
  have hcount : (Measure.count : Measure K) C = (Fintype.card C : ℝ≥0∞) := by
    rw [Measure.count_apply hC, ← Set.coe_fintypeCard C]
    rfl
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton k)]
  by_cases hk : k ∈ C
  · have hpre : (Subtype.val : C → K) ⁻¹' {k} = {⟨k, hk⟩} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    have hinter : C ∩ {k} = {k} := Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hk)
    rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      uniformOn, cond_apply hC, hinter, Measure.count_singleton, hcount,
      PMF.uniformOfFintype_apply, mul_one]
  · have hpre : (Subtype.val : C → K) ⁻¹' {k} = ∅ := by ext z; simp; exact fun h ↦ hk (h ▸ z.property)
    rw [hpre, measure_empty, uniformOn, cond_apply hC, Set.inter_singleton_eq_empty.mpr hk,
      measure_empty, mul_zero]

theorem uniformAvoidanceSubtype_map_uniformOn (n : ℕ) :
    ((PMF.uniformOfFintype (AvoidancePermutation n 2)).toMeasure).map
      (Subtype.val : AvoidancePermutation n 2 → (Fin 2 → Equiv.Perm (Fin n))) =
        uniformOn (avoidanceRankSet n 2) := by
  letI : Fintype (avoidanceRankSet n 2) := avoidancePermutation_fintype n 2
  letI : Nonempty (avoidanceRankSet n 2) := avoidancePermutation3_nonempty n
  exact finite_uniform_subtype_map_uniformOn (avoidanceRankSet n 2)

def uniformWeakBruhatIntervalLaw (n : ℕ) : Measure (WeakBruhatInterval n) :=
  (PMF.uniformOfFintype (WeakBruhatInterval n)).toMeasure

instance uniformWeakBruhatIntervalLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformWeakBruhatIntervalLaw n) := by
  unfold uniformWeakBruhatIntervalLaw
  infer_instance

theorem uniformAvoidance_map_intervalLaw (n : ℕ) :
    ((PMF.uniformOfFintype (AvoidancePermutation n 2)).toMeasure).map (avoidanceWeakBruhatEquiv n) =
      uniformWeakBruhatIntervalLaw n := (avoidanceWeakBruhatEquiv_measurePreserving n).map_eq

theorem intervalRank_predictor_formula (n : ℕ) (I : WeakBruhatInterval n) (j : Fin n) :
    intervalPredictorError (intervalRankCloud n I j) =
      (rankMidpoint n (I.val.1 j) - normalCDF
        (normalQuantile (rankMidpoint n j) + normalQuantile (rankMidpoint n (I.val.2 j)))) ^ 2 := by
  rw [intervalPredictorError, if_pos (intervalRankCloud_mem_openCube n I j)]
  rfl

theorem intervalRankPredictor_empirical_integral (n : ℕ) (hn : 0 < n) (I : WeakBruhatInterval n) :
    (∫ x, intervalPredictorError x ∂(intervalRankEmpiricalProbability n I : Measure (CubePoint 3))) =
      (∑ j, (rankMidpoint n (I.val.1 j) - normalCDF
        (normalQuantile (rankMidpoint n j) + normalQuantile (rankMidpoint n (I.val.2 j)))) ^ 2) / n := by
  change (∫ x, intervalPredictorError x ∂empiricalCubeMeasure n 3 (intervalRankCloud n I)) = _
  rw [empiricalCubeMeasure, if_neg hn.ne', integral_smul_measure,
    integral_finset_sum_measure (fun j _ ↦ integrable_dirac (by simp :
      ‖intervalPredictorError (intervalRankCloud n I j)‖ₑ < ⊤))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    intervalRank_predictor_formula, div_eq_mul_inv, mul_comm]

def intervalProbabilityMap (ν : ProbabilityMeasure (CubePoint 3)) : ProbabilityMeasure (CubePoint 3) :=
  ν.map intervalCubeMap_continuous.measurable.aemeasurable

theorem intervalProbabilityMap_continuous : Continuous intervalProbabilityMap :=
  ProbabilityMeasure.continuous_map intervalCubeMap_continuous

theorem intervalProbabilityMap_limiting :
    intervalProbabilityMap (limitingCubeProbability 3) = intervalLimitProbability := by
  apply Subtype.ext
  rfl

theorem intervalProbabilityMap_preimage_neighborhood {U : Set (ProbabilityMeasure (CubePoint 3))}
    (hU : U ∈ 𝓝 intervalLimitProbability) :
    intervalProbabilityMap ⁻¹' U ∈ 𝓝 (limitingCubeProbability 3) := by
  have h := (intervalProbabilityMap_continuous.continuousAt (x := limitingCubeProbability 3)).tendsto
  rw [intervalProbabilityMap_limiting] at h
  exact h.eventually hU

/-- Exact finite-law transport, before applying the separately proved rank concentration. -/
theorem uniformInterval_weak_event_eq_avoidance (n : ℕ) (hn : 0 < n)
    (U : Set (ProbabilityMeasure (CubePoint 3))) :
    uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} =
      uniformOn (avoidanceRankSet n 2)
        {π | intervalProbabilityMap (empiricalCubeProbability n 3 (avoidanceRankTripleCloud n π)) ∉ U} := by
  let E : Set (Fin 2 → Equiv.Perm (Fin n)) :=
    {π | intervalProbabilityMap (empiricalCubeProbability n 3 (avoidanceRankTripleCloud n π)) ∉ U}
  have hE : MeasurableSet E := E.toFinite.measurableSet
  have hmap := Measure.map_apply (μ := (PMF.uniformOfFintype (AvoidancePermutation n 2)).toMeasure)
    measurable_subtype_coe hE
  rw [uniformAvoidanceSubtype_map_uniformOn] at hmap
  rw [← uniformAvoidance_map_intervalLaw n,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  calc
    _ = (PMF.uniformOfFintype (AvoidancePermutation n 2)).toMeasure
        ((Subtype.val : AvoidancePermutation n 2 → (Fin 2 → Equiv.Perm (Fin n))) ⁻¹' E) := by
      congr 1
      ext π
      change (intervalRankEmpiricalProbability n (avoidanceWeakBruhatEquiv n π) ∉ U) ↔ _
      rw [intervalRankEmpiricalProbability_avoidance_map n hn π]
      rfl
    _ = _ := hmap.symm

theorem avoidanceRankTripleCloud_eq_permutationRankCloud (n : ℕ)
    (π : Fin 2 → Equiv.Perm (Fin n)) : avoidanceRankTripleCloud n π = permutationRankCloud n 2 π := by
  funext j i
  fin_cases i <;> rfl

/-- Proposition 6.4's empirical law and exponential concentration for genuinely
uniform actual weak-order intervals. Only the explicitly cited H3 and DKW inputs remain. -/
theorem weakBruhat_interval_empirical_concentration (H : HumphreysAlcoveInput 3) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨α, hα, htail⟩ := permutation_rank_empirical_weak_concentration (m := 2) (by decide) H DKW
    (intervalProbabilityMap_preimage_neighborhood hU)
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  rw [uniformInterval_weak_event_eq_avoidance n hnpos]
  simpa only [permutationRankEmpiricalProbability, avoidanceRankTripleCloud_eq_permutationRankCloud,
    Set.mem_preimage] using hn

def intervalPredictorAverage (n : ℕ) (I : WeakBruhatInterval n) : ℝ :=
  (∑ j, (rankMidpoint n (I.val.1 j) - normalCDF
    (normalQuantile (rankMidpoint n j) + normalQuantile (rankMidpoint n (I.val.2 j)))) ^ 2) / n

/-- The printed mean-square predictor assertion for actual uniform intervals. -/
theorem weakBruhat_interval_predictor_exponential_tail (H : HumphreysAlcoveInput 3) (DKW : DKWInput)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | δ < intervalPredictorAverage n I} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨U, hU, hsmall⟩ := intervalPredictorError_weak_neighborhood hδ
  obtain ⟨α, hα, htail⟩ := weakBruhat_interval_empirical_concentration H DKW hU
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply (measure_mono ?_).trans hn
  intro I hbad hmem
  have hs := hsmall (intervalRankEmpiricalProbability n I) hmem
  rw [intervalRankPredictor_empirical_integral n hnpos I] at hs
  exact (not_lt_of_gt hs) hbad

theorem weakBruhat_interval_empirical_in_probability (H : HumphreysAlcoveInput 3) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    Tendsto (fun n : ℕ ↦ uniformWeakBruhatIntervalLaw n
      {I | intervalRankEmpiricalProbability n I ∉ U}) atTop (𝓝 0) := by
  obtain ⟨α, hα, htail⟩ := weakBruhat_interval_empirical_concentration H DKW hU
  exact exponential_tail_tendsto_zero _ hα htail

theorem weakBruhat_interval_predictor_in_probability (H : HumphreysAlcoveInput 3) (DKW : DKWInput)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ uniformWeakBruhatIntervalLaw n
      {I | δ < intervalPredictorAverage n I}) atTop (𝓝 0) := by
  obtain ⟨α, hα, htail⟩ := weakBruhat_interval_predictor_exponential_tail H DKW hδ
  exact exponential_tail_tendsto_zero _ hα htail

def centeredBivariateIntervalProbability (ν : Measure (ℝ × ℝ)) [IsGaussian ν] :
    ProbabilityMeasure (CubePoint 3) :=
  ⟨ν.map intervalGaussianCubeMap,
    Measure.isProbabilityMeasure_map intervalGaussianCubeMap_continuous.measurable.aemeasurable⟩

/-- The empirical statement with any centered bivariate Gaussian specified in the manuscript. -/
theorem weakBruhat_interval_gaussian_source (H : HumphreysAlcoveInput 3) (DKW : DKWInput)
    (ν : Measure (ℝ × ℝ)) [IsGaussian ν]
    (h0 : (∫ z, z.1 ∂ν) = 0) (h1 : (∫ z, z.2 ∂ν) = 0)
    (hv0 : Var[Prod.fst; ν] = 1) (hv1 : Var[Prod.snd; ν] = 1)
    (hcov : cov[Prod.fst, Prod.snd; ν] = -(1 : ℝ) / 2)
    {U : Set (ProbabilityMeasure (CubePoint 3))}
    (hU : U ∈ 𝓝 (centeredBivariateIntervalProbability ν)) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  have heq : centeredBivariateIntervalProbability ν = intervalLimitProbability := by
    apply Subtype.ext
    exact (intervalLimitMeasure_eq_centered_bivariate_gaussian ν h0 h1 hv0 hv1 hcov).symm
  rw [heq] at hU
  exact weakBruhat_interval_empirical_concentration H DKW hU

end Antichain
