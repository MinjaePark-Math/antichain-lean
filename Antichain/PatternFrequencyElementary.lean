import Antichain.PatternFrequencySubsets
import Antichain.RankPermutonElementary

/-! Fixed literal subset-pattern frequencies without the cited DKW premise. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

set_option maxHeartbeats 800000

theorem permutation_pattern_frequency_exponential_concentration_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1))
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hmu : ∀ i : Fin (m + 1),
      (limitingCubeProbability (m + 1) : Measure (CubePoint (m + 1))).map (fun x => x i) =
        cubeCoordinateLaw := fun i => limitingAntichainMeasure_coordinate_map (by simpa using (show 2 ≤ m + 1 by omega)) i
  have hcont := patternProbability_continuousAt_permuton q m tau (limitingCubeProbability (m + 1)) hmu
  let U : Set (ProbabilityMeasure (CubePoint (m + 1))) :=
    {nu | |patternProbability q m tau nu - patternProbability q m tau (limitingCubeProbability (m + 1))| < epsilon / 2}
  have hball : ∀ᶠ z : ℝ in 𝓝 (patternProbability q m tau (limitingCubeProbability (m + 1))),
      |z - patternProbability q m tau (limitingCubeProbability (m + 1))| < epsilon / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (Metric.ball_mem_nhds (patternProbability q m tau (limitingCubeProbability (m + 1)))
        (show 0 < epsilon / 2 by positivity))
  have hU : U ∈ 𝓝 (limitingCubeProbability (m + 1)) := hcont.eventually hball
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_permuton_exponential_concentration_elementary hm H hU
  have hlarge : ∀ᶠ n : ℕ in atTop, (4 * (q.choose 2 : ℝ)) / epsilon ≤ n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, hlarge, eventually_gt_atTop (0 : ℕ)] with n hn hnlarge hnpos
  letI : NeZero n := ⟨hnpos.ne'⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsmall : (q.choose 2 : ℝ) / n ≤ epsilon / 4 := by
    have hh := (div_le_iff₀ hepsilon).mp hnlarge
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  apply le_trans (measure_mono ?_) hn
  intro pi hbad
  by_contra hnot
  have hbox : permutationRankBoxProbability n m pi ∈ U := not_not.mp (fun h => hnot (Or.inr h))
  have herr := (permutationPatternFrequency_box_error n m q tau pi).trans hsmall
  have htri := abs_sub_le (permutationPatternFrequency n m q tau pi)
    (patternProbability q m tau (permutationRankBoxProbability n m pi))
    (patternProbability q m tau (limitingCubeProbability (m + 1)))
  change |patternProbability q m tau (permutationRankBoxProbability n m pi) -
    patternProbability q m tau (limitingCubeProbability (m + 1))| < epsilon / 2 at hbox
  change epsilon ≤ _ at hbad
  linarith

theorem fixed_pattern_frequency_source_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1))
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationSubsetPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  simp_rw [permutationSubsetPatternFrequency_eq]
  exact permutation_pattern_frequency_exponential_concentration_elementary hm H q tau hepsilon

end Antichain
