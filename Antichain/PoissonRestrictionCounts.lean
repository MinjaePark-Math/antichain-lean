import Antichain.PoissonSpatialIndependence

/-! Literal count marginals and independent Poisson counts in disjoint
measurable regions, for the actual count-plus-iid finite-intensity process. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {X K : Type*} [MeasurableSpace X]

def configurationCount (z : FiniteConfiguration X) : ℕ := z.1

theorem measurable_configurationCount : Measurable (configurationCount (X := X)) := by
  intro S hS
  change MeasurableSet[⨅ n, (inferInstance : MeasurableSpace (Fin n → X)).map
    (configurationMk n)] (configurationCount ⁻¹' S)
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((configurationCount (X := X) ∘ configurationMk (X := X) n) ⁻¹' S)
  have hfun : configurationCount ∘ configurationMk (X := X) n = fun _ => n := rfl
  rw [hfun]
  exact measurable_const hS

theorem poissonConfigurationLaw_count_singleton (r : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] (n : ℕ) :
    ((poissonConfigurationLaw r mu).map configurationCount) {n} =
      poissonPMF r n * (mu Set.univ) ^ n := by
  rw [Measure.map_apply measurable_configurationCount (measurableSet_singleton n),
    poissonConfigurationLaw_event r mu _
      ((measurable_configurationCount) (measurableSet_singleton n))]
  have hpre (k : ℕ) : configurationMk (X := X) k ⁻¹' (configurationCount ⁻¹' {n}) =
      if k = n then Set.univ else ∅ := by
    ext x
    simp [configurationMk, configurationCount]
  simp_rw [hpre]
  simp only [apply_ite, Measure.pi_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, measure_empty, mul_zero]
  rw [tsum_eq_single n]
  · simp
  · intro k hk
    simp [hk]

/-- The actual total count has precisely its Poisson distribution, including
zero intensity and zero rate. -/
theorem finiteIntensityPoissonLaw_count (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] :
    (finiteIntensityPoissonLaw t mu).map configurationCount =
      (poissonPMF (t * (mu Set.univ).toNNReal)).toMeasure := by
  letI : IsFiniteMeasure (normalizedMarkLaw mu) := by
    unfold normalizedMarkLaw
    infer_instance
  apply Measure.ext_of_singleton
  intro n
  rw [finiteIntensityPoissonLaw, poissonConfigurationLaw_count_singleton,
    PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)]
  by_cases hz : mu = 0
  · subst mu
    cases n with
    | zero => simp [normalizedMarkLaw, poissonPMF, poissonPMFReal]
    | succ n =>
      simp [normalizedMarkLaw, poissonPMF, poissonPMFReal]
      change 0 = ENNReal.ofReal ((0 : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ))
      simp
  · letI : NeZero mu := ⟨hz⟩
    simp

def configurationRegionCount (U : Set X) (z : FiniteConfiguration X) : ℕ :=
  configurationCount (configurationRestriction U z)

theorem measurable_configurationRegionCount {U : Set X} (hU : MeasurableSet U) :
    Measurable (configurationRegionCount U) :=
  measurable_configurationCount.comp (measurable_configurationRestriction hU)

theorem finiteIntensityPoissonLaw_regionCount (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U) :
    (finiteIntensityPoissonLaw t mu).map (configurationRegionCount U) =
      (poissonPMF (t * (mu U).toNNReal)).toMeasure := by
  rw [show configurationRegionCount U = configurationCount ∘ configurationRestriction U from rfl,
    ← Measure.map_map measurable_configurationCount (measurable_configurationRestriction hU),
    finiteIntensityPoissonLaw_restriction t mu hU, finiteIntensityPoissonLaw_count,
    Measure.restrict_apply_univ]

theorem finiteIntensityPoissonLaw_disjoint_counts_independent (t : ℝ≥0)
    (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) :
    iIndepFun (fun i => configurationRegionCount (C i)) (finiteIntensityPoissonLaw t mu) :=
  (finiteIntensityPoissonLaw_disjoint_restrictions_independent t mu C hC hdisj).comp
    (fun _ => configurationCount) (fun _ => measurable_configurationCount)

theorem finiteIntensityPoissonLaw_disjoint_counts_joint [Fintype K] (t : ℝ≥0)
    (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (finiteIntensityPoissonLaw t mu).map (fun z i => configurationRegionCount (C i) z) =
      Measure.pi (fun i => (poissonPMF (t * (mu (C i)).toNNReal)).toMeasure) := by
  letI := finiteIntensityPoissonLaw_probability_all t mu
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_configurationRegionCount (hC i)).aemeasurable)).mp
      (finiteIntensityPoissonLaw_disjoint_counts_independent t mu C hC hdisj)
  simp_rw [finiteIntensityPoissonLaw_regionCount t mu (hC _)] at h
  exact h

end Antichain
