import Antichain.TwoPointAntichainPatterns
import Antichain.RankLimitsHoeffding
import Antichain.FinalIntervalApplication

/-! Actual weak-Bruhat interval inversion densities and the new joint
exponential concentration at one third and two thirds. -/

noncomputable section
namespace Antichain
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal Topology

def permutationInversionDensity {n : ℕ} (pi : Equiv.Perm (Fin n)) : ℝ :=
  (Nat.card {p : Fin n × Fin n // p ∈ permutationInversions pi} : ℝ) / (n.choose 2 : ℝ)

def twoSubsetIncreasingPairEquiv (n : ℕ) :
    PatternSubset n 2 ≃ {p : Fin n × Fin n // p.1 < p.2} := by
  classical
  let f : PatternSubset n 2 → {p : Fin n × Fin n // p.1 < p.2} :=
    fun s => ⟨(patternSubsetEnumeration s 0, patternSubsetEnumeration s 1),
      (s.val.orderEmbOfFin s.property).strictMono (by decide)⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t h
    have h0 := congrArg (fun p : {p : Fin n × Fin n // p.1 < p.2} => p.val.1) h
    have h1 := congrArg (fun p : {p : Fin n × Fin n // p.1 < p.2} => p.val.2) h
    have he : (s.val.orderEmbOfFin s.property : Fin 2 → Fin n) = t.val.orderEmbOfFin t.property := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
    apply Subtype.ext
    have hh := congrArg (fun g : Fin 2 → Fin n => Finset.image g Finset.univ) he
    simpa only [Finset.image_orderEmbOfFin_univ] using hh
  · intro p
    let s : PatternSubset n 2 := ⟨{p.val.1, p.val.2}, by simp [p.property.ne]⟩
    have hmono : StrictMono (fun j : Fin 2 => if j = 0 then p.val.1 else p.val.2) := by
      intro j k hjk
      fin_cases j <;> fin_cases k <;> simp_all
      exact p.property
    have he : (fun j : Fin 2 => if j = 0 then p.val.1 else p.val.2) =
        s.val.orderEmbOfFin s.property := by
      apply Finset.orderEmbOfFin_unique
      · intro j
        fin_cases j <;> simp [s]
      · exact hmono
    refine ⟨s, ?_⟩
    apply Subtype.ext
    change (s.val.orderEmbOfFin s.property 0, s.val.orderEmbOfFin s.property 1) = p.val
    rw [← he]
    simp

theorem inversion_card_eq_twoSubset_card {n : ℕ} (pi : Equiv.Perm (Fin n)) :
    Nat.card {p : Fin n × Fin n // p ∈ permutationInversions pi} =
      Nat.card {s : PatternSubset n 2 //
        pi (patternSubsetEnumeration s 1) < pi (patternSubsetEnumeration s 0)} := by
  let e := (twoSubsetIncreasingPairEquiv n).subtypeEquiv
    (p := fun s => pi (patternSubsetEnumeration s 1) < pi (patternSubsetEnumeration s 0))
    (q := fun p => pi p.val.2 < pi p.val.1) (fun _ => Iff.rfl)
  let e' : {p : {p : Fin n × Fin n // p.1 < p.2} // pi p.val.2 < pi p.val.1} ≃
      {p : Fin n × Fin n // p ∈ permutationInversions pi} :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun p : Fin n × Fin n => p.1 < p.2)
      (fun p => pi p.2 < pi p.1)
  exact (Nat.card_congr (e.trans e')).symm

def twoPointRankPatternCondition {n : ℕ} (pi : Fin 2 → Equiv.Perm (Fin n))
    (s : PatternSubset n 2) (i : Fin 3) : Prop :=
  let k := patternSubsetEnumeration s 0
  let l := patternSubsetEnumeration s 1
  if i = 0 then pi 0 l < pi 0 k ∧ pi 1 l < pi 1 k else
    if i = 1 then pi 0 l < pi 0 k ∧ pi 1 k < pi 1 l else
      pi 0 k < pi 0 l ∧ pi 1 l < pi 1 k

theorem subset_rank_twoPointPattern_iff {n : ℕ} (pi : Fin 2 → Equiv.Perm (Fin n))
    (s : PatternSubset n 2) (i : Fin 3) :
    (fun j => permutationRankCloud n 2 pi (patternSubsetEnumeration s j)) ∈
      patternEvent 2 2 (twoPointAntichainPattern i) ↔ twoPointRankPatternCondition pi s i := by
  rw [twoPointAntichainPattern_event]
  have hkl : patternSubsetEnumeration s 0 < patternSubsetEnumeration s 1 :=
    (s.val.orderEmbOfFin s.property).strictMono (by decide)
  have hp (j : Fin 2) : permutationRankCloud n 2 pi (patternSubsetEnumeration s j) =
      ![rankMidpoint n (patternSubsetEnumeration s j),
        rankMidpoint n (pi 0 (patternSubsetEnumeration s j)),
        rankMidpoint n (pi 1 (patternSubsetEnumeration s j))] := by
    funext a
    fin_cases a <;> rfl
  fin_cases i <;>
    simp [twoPointMinorityEvent, twoPointRankPatternCondition, hp,
      Fin.forall_fin_succ, rankMidpoint_lt_iff, hkl, not_lt_of_gt hkl]
  tauto

theorem avoidsIncreasingPair_forces_opposite {n : ℕ} {pi : Fin 2 → Equiv.Perm (Fin n)}
    (hpi : AvoidsIncreasingPair pi) {k l : Fin n} (hkl : k < l) (hthird : pi 1 k < pi 1 l) :
    pi 0 l < pi 0 k := by
  have hnot : ¬pi 0 k < pi 0 l := by
    intro hsecond
    apply hpi k l hkl
    intro i
    fin_cases i
    · exact hsecond
    · exact hthird
  exact lt_of_le_of_ne (le_of_not_gt hnot) ((pi 0).injective.ne hkl.ne')

theorem lower_interval_inversion_density_eq_pattern {n : ℕ}
    (pi : AvoidancePermutation n 2) :
    permutationInversionDensity (reversePermutationValues (pi.val 1)) =
      permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi.val := by
  unfold permutationInversionDensity permutationSubsetPatternFrequency patternSubsetFrequency
  rw [inversion_card_eq_twoSubset_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / (n.choose 2 : ℝ))
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro s
  change _ ↔ (fun j => permutationRankCloud n 2 pi.val (patternSubsetEnumeration s j)) ∈
    patternEvent 2 2 (twoPointAntichainPattern 1)
  rw [subset_rank_twoPointPattern_iff]
  simp only [twoPointRankPatternCondition, Fin.isValue, one_ne_zero, ↓reduceIte,
    reversePermutationValues_apply, Fin.rev_lt_rev]
  exact ⟨fun h => ⟨avoidsIncreasingPair_forces_opposite pi.property
    ((s.val.orderEmbOfFin s.property).strictMono (by decide)) h, h⟩, fun h => h.2⟩

theorem upper_interval_inversion_density_eq_patterns {n : ℕ}
    (pi : Fin 2 → Equiv.Perm (Fin n)) :
    permutationInversionDensity (pi 0) =
      permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi +
        permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi := by
  classical
  let U : PatternSubset n 2 → Prop := fun s =>
    pi 0 (patternSubsetEnumeration s 1) < pi 0 (patternSubsetEnumeration s 0)
  let P : PatternSubset n 2 → Prop := fun s => twoPointRankPatternCondition pi s 1
  let Q : PatternSubset n 2 → Prop := fun s => twoPointRankPatternCondition pi s 0
  have hne (s : PatternSubset n 2) :
      pi 1 (patternSubsetEnumeration s 0) ≠ pi 1 (patternSubsetEnumeration s 1) :=
    (pi 1).injective.ne ((s.val.orderEmbOfFin s.property).strictMono (by decide)).ne
  have heq : ∀ s, U s ↔ P s ∨ Q s := by
    intro s
    dsimp [U, P, Q, twoPointRankPatternCondition]
    constructor
    · intro hu
      rcases lt_or_gt_of_ne (hne s) with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
    · rintro (h | h) <;> exact h.1
  have hd : Disjoint (univ.filter P) (univ.filter Q) := by
    apply Finset.disjoint_left.mpr
    intro s hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    simp only [P, Q, twoPointRankPatternCondition, one_ne_zero, ↓reduceIte] at hp' hq'
    exact (not_lt_of_gt hp'.2) hq'.2
  have hu : univ.filter U = univ.filter P ∪ univ.filter Q := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, heq]
  have hcard : Nat.card {s // U s} = Nat.card {s // P s} + Nat.card {s // Q s} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hu, Finset.card_union_of_disjoint hd]
  have hp (i : Fin 3) :
      permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern i) pi =
        (Nat.card {s : PatternSubset n 2 // twoPointRankPatternCondition pi s i} : ℝ) / (n.choose 2 : ℝ) := by
    unfold permutationSubsetPatternFrequency patternSubsetFrequency
    congr 2
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun s => subset_rank_twoPointPattern_iff pi s i)
  rw [hp 1, hp 0, permutationInversionDensity, inversion_card_eq_twoSubset_card]
  change (Nat.card {s // U s} : ℝ) / (n.choose 2 : ℝ) =
    (Nat.card {s // P s} : ℝ) / (n.choose 2 : ℝ) + (Nat.card {s // Q s} : ℝ) / (n.choose 2 : ℝ)
  rw [hcard, Nat.cast_add, add_div]

theorem interval_inversion_densities_avoidance_map {n : ℕ} (pi : AvoidancePermutation n 2) :
    permutationInversionDensity (avoidanceWeakBruhatEquiv n pi).val.1 =
      permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi.val ∧
    permutationInversionDensity (avoidanceWeakBruhatEquiv n pi).val.2 =
      permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi.val +
        permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi.val :=
  ⟨lower_interval_inversion_density_eq_pattern pi, upper_interval_inversion_density_eq_patterns pi.val⟩

theorem uniformInterval_event_eq_avoidance (n : ℕ) (A : Set (WeakBruhatInterval n))
    (B : Set (Fin 2 → Equiv.Perm (Fin n)))
    (h : ∀ pi : AvoidancePermutation n 2, avoidanceWeakBruhatEquiv n pi ∈ A ↔ pi.val ∈ B) :
    uniformWeakBruhatIntervalLaw n A = uniformOn (avoidanceRankSet n 2) B := by
  rw [← uniformAvoidance_map_intervalLaw n,
    Measure.map_apply (measurable_of_finite _) A.toFinite.measurableSet]
  have hp : (avoidanceWeakBruhatEquiv n) ⁻¹' A =
      (Subtype.val : AvoidancePermutation n 2 → (Fin 2 → Equiv.Perm (Fin n))) ⁻¹' B := by
    ext pi
    exact h pi
  rw [hp, ← Measure.map_apply measurable_subtype_coe B.toFinite.measurableSet,
    uniformAvoidanceSubtype_map_uniformOn]

/-- The new inversion-density corollary, for literal inversion pairs and the
genuine uniform interval law. Its proof uses the three coordinate-symmetric
two-point pattern probabilities and the written Hoeffding rank route. -/
theorem weakBruhat_interval_inversion_density_exponential_concentration
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | delta <
        max |permutationInversionDensity I.val.1 - (1 : ℝ) / 3|
          |permutationInversionDensity I.val.2 - (2 : ℝ) / 3|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  let A : Fin 2 → (n : ℕ) → Set (Fin 2 → Equiv.Perm (Fin n)) := fun i n =>
    {pi | delta / 3 ≤ |permutationSubsetPatternFrequency n 2 2
      (twoPointAntichainPattern (if i = 0 then 1 else 0)) pi - (1 : ℝ) / 3|}
  have hA : ∀ i, ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n 2) (A i n) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    intro i
    have ht := fixed_pattern_frequency_source_hoeffding (m := 2) (by decide) 2
      (twoPointAntichainPattern (if i = 0 then 1 else 0)) (div_pos hdelta (by norm_num : (0 : ℝ) < 3))
    have hp : patternProbability 2 2 (twoPointAntichainPattern (if i = 0 then 1 else 0))
        (limitingCubeProbability (2 + 1)) = (1 : ℝ) / 3 :=
      twoPointAntichainPattern_probability _
    simpa only [hp] using ht
  obtain ⟨alpha, halpha, htail⟩ := finite_union_exponential_tail
    (fun n => uniformOn (avoidanceRankSet n 2)) A hA
  refine ⟨alpha, halpha, ?_⟩
  filter_upwards [htail] with n hn
  let B : Set (Fin 2 → Equiv.Perm (Fin n)) := {pi | delta <
    max |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi - (1 : ℝ) / 3|
      |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi +
        permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (2 : ℝ) / 3|}
  calc
    _ = uniformOn (avoidanceRankSet n 2) B := by
      apply uniformInterval_event_eq_avoidance
      intro pi
      simp only [Set.mem_setOf_eq, B, (interval_inversion_densities_avoidance_map pi).1,
        (interval_inversion_densities_avoidance_map pi).2]
    _ ≤ uniformOn (avoidanceRankSet n 2) (⋃ i, A i n) := by
      apply measure_mono
      intro pi hpi
      by_contra hnot
      have h1 : |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi - (1 : ℝ) / 3| < delta / 3 := by
        apply lt_of_not_ge
        intro h
        exact hnot (Set.mem_iUnion.mpr ⟨0, by simpa [A] using h⟩)
      have h0 : |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (1 : ℝ) / 3| < delta / 3 := by
        apply lt_of_not_ge
        intro h
        exact hnot (Set.mem_iUnion.mpr ⟨1, by simpa [A] using h⟩)
      have hsum := abs_add_le
        (permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi - (1 : ℝ) / 3)
        (permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (1 : ℝ) / 3)
      have hbound : |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi +
          permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (2 : ℝ) / 3| ≤
          |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi - (1 : ℝ) / 3| +
          |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (1 : ℝ) / 3| := by
        have heq : permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi +
            permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (2 : ℝ) / 3 =
            (permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi - (1 : ℝ) / 3) +
            (permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (1 : ℝ) / 3) := by ring
        rw [heq]
        exact hsum
      have h1le : |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi - (1 : ℝ) / 3| ≤ delta := by
        linarith
      have hsumle : |permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 1) pi +
          permutationSubsetPatternFrequency n 2 2 (twoPointAntichainPattern 0) pi - (2 : ℝ) / 3| ≤ delta := by
        linarith
      exact (not_lt_of_ge (max_le h1le hsumle)) hpi
    _ ≤ _ := hn

theorem weakBruhat_interval_inversion_densities_in_probability {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ => uniformWeakBruhatIntervalLaw n {I | delta <
      max |permutationInversionDensity I.val.1 - (1 : ℝ) / 3|
        |permutationInversionDensity I.val.2 - (2 : ℝ) / 3|}) atTop (𝓝 0) := by
  obtain ⟨alpha, ha, ht⟩ := weakBruhat_interval_inversion_density_exponential_concentration hdelta
  exact exponential_tail_tendsto_zero _ ha ht

/-- The revised interval proposition, following its current fixed-order-statistic
Hoeffding proof upstream rather than the older DKW branch. -/
theorem weakBruhat_interval_empirical_concentration_hoeffding
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, ht⟩ := permutation_rank_empirical_weak_concentration_hoeffding
    (m := 2) (by decide) (intervalProbabilityMap_preimage_neighborhood hU)
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  rw [uniformInterval_weak_event_eq_avoidance n hnpos]
  simpa only [permutationRankEmpiricalProbability, avoidanceRankTripleCloud_eq_permutationRankCloud,
    Set.mem_preimage] using hn

theorem weakBruhat_interval_predictor_exponential_tail_hoeffding {delta : ℝ} (hd : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | delta < intervalPredictorAverage n I} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨U, hU, hsmall⟩ := intervalPredictorError_weak_neighborhood hd
  obtain ⟨alpha, ha, ht⟩ := weakBruhat_interval_empirical_concentration_hoeffding hU
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply (measure_mono ?_).trans hn
  intro I hbad hmem
  have hs := hsmall (intervalRankEmpiricalProbability n I) hmem
  rw [intervalRankPredictor_empirical_integral n hnpos I] at hs
  exact (not_lt_of_gt hs) hbad

theorem weakBruhat_interval_empirical_in_probability_hoeffding
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    Tendsto (fun n : ℕ => uniformWeakBruhatIntervalLaw n
      {I | intervalRankEmpiricalProbability n I ∉ U}) atTop (𝓝 0) := by
  obtain ⟨alpha, ha, ht⟩ := weakBruhat_interval_empirical_concentration_hoeffding hU
  exact exponential_tail_tendsto_zero _ ha ht

theorem weakBruhat_interval_predictor_in_probability_hoeffding {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun n : ℕ => uniformWeakBruhatIntervalLaw n
      {I | delta < intervalPredictorAverage n I}) atTop (𝓝 0) := by
  obtain ⟨alpha, ha, ht⟩ := weakBruhat_interval_predictor_exponential_tail_hoeffding hd
  exact exponential_tail_tendsto_zero _ ha ht

theorem weakBruhat_interval_gaussian_source_hoeffding (nu : Measure (ℝ × ℝ)) [IsGaussian nu]
    (h0 : (∫ z, z.1 ∂nu) = 0) (h1 : (∫ z, z.2 ∂nu) = 0)
    (hv0 : Var[Prod.fst; nu] = 1) (hv1 : Var[Prod.snd; nu] = 1)
    (hcov : cov[Prod.fst, Prod.snd; nu] = -(1 : ℝ) / 2)
    {U : Set (ProbabilityMeasure (CubePoint 3))}
    (hU : U ∈ 𝓝 (centeredBivariateIntervalProbability nu)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have heq : centeredBivariateIntervalProbability nu = intervalLimitProbability := by
    apply Subtype.ext
    exact (intervalLimitMeasure_eq_centered_bivariate_gaussian nu h0 h1 hv0 hv1 hcov).symm
  rw [heq] at hU
  exact weakBruhat_interval_empirical_concentration_hoeffding hU

theorem weakBruhat_interval_gaussian_in_probability_hoeffding (nu : Measure (ℝ × ℝ)) [IsGaussian nu]
    (h0 : (∫ z, z.1 ∂nu) = 0) (h1 : (∫ z, z.2 ∂nu) = 0)
    (hv0 : Var[Prod.fst; nu] = 1) (hv1 : Var[Prod.snd; nu] = 1)
    (hcov : cov[Prod.fst, Prod.snd; nu] = -(1 : ℝ) / 2)
    {U : Set (ProbabilityMeasure (CubePoint 3))}
    (hU : U ∈ 𝓝 (centeredBivariateIntervalProbability nu)) :
    Tendsto (fun n : ℕ => uniformWeakBruhatIntervalLaw n
      {I | intervalRankEmpiricalProbability n I ∉ U}) atTop (𝓝 0) := by
  obtain ⟨alpha, ha, ht⟩ := weakBruhat_interval_gaussian_source_hoeffding nu h0 h1 hv0 hv1 hcov hU
  exact exponential_tail_tendsto_zero _ ha ht

end Antichain
