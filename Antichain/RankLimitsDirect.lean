import Antichain.RankPermutonElementary
import Antichain.SignedRankElementary
import Antichain.PatternFrequencyElementary
import Antichain.DirectAlcoveInput

/-! Source rank, permuton, signed-class and fixed-pattern conclusions with
all previously cited probability and alcove inputs supplied by actual proofs. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

theorem rank_permuton_exponential_concentration_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U ∨ cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_permuton_exponential_concentration_elementary hd (humphreysAlcoveInput_direct hd) hU

/-- Proposition 6.1's literal closed-cube weak assertion with no external
mathematical theorem parameter. -/
theorem rank_permuton_source_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U)
    (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_permuton_source_elementary hd (humphreysAlcoveInput_direct hd) hUopen hUmem

theorem permutation_rank_empirical_weak_concentration_direct {m : ℕ} (hm : 1 ≤ m)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m) {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_empirical_weak_concentration_elementary hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) hU

theorem permutation_rank_permuton_exponential_concentration_direct {m : ℕ} (hm : 1 ≤ m)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨ permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_permuton_exponential_concentration_elementary hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) hU

theorem signed_rank_closed_cube_permuton_concentration_direct {m : ℕ} (hm : 1 ≤ m)
    (sign : Fin m → Bool) {U : Set (ProbabilityMeasure (ClosedCubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedClosedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | closedPermutationRankEmpiricalProbability n m pi ∉ U ∨
        closedPermutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  signed_rank_closed_cube_permuton_concentration_elementary hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sign hU

theorem permutation_pattern_frequency_exponential_concentration_direct {m : ℕ} (hm : 1 ≤ m)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_pattern_frequency_exponential_concentration_elementary hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) q tau hepsilon

/-- The literal choose(n,q)-normalized fixed-pattern remark, now without
either a DKW or a Coxeter geometry premise. -/
theorem fixed_pattern_frequency_source_direct {m : ℕ} (hm : 1 ≤ m)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationSubsetPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  fixed_pattern_frequency_source_elementary hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) q tau hepsilon

end Antichain
