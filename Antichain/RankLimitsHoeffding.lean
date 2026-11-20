import Antichain.RankPermutonHoeffding
import Antichain.DirectAlcoveInput

/-! Closed source-facing endpoints following the current Hoeffding proof. -/
noncomputable section
namespace Antichain
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology

theorem rank_permuton_exponential_concentration_hoeffding {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U ∨ cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_permuton_exponential_concentration_hoeffding_aux hd (humphreysAlcoveInput_direct hd)
    hU

/-- Theorem 6.2 in the closed-cube weak topology, using the finite Hoeffding
bound at order-statistic thresholds. -/
theorem rank_permuton_source_hoeffding {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U)
    (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_permuton_source_hoeffding_aux hd (humphreysAlcoveInput_direct hd) hUopen hUmem

theorem rank_euclidean_shape_exponential_concentration_hoeffding {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) {delta : ℝ} (hdelt : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | delta < hausdorffDist (euclideanRankSampleSet n d x)
        (closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) ''
          normalQuantileSurface (Fin d)))} ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_euclidean_shape_exponential_concentration_hoeffding_aux hd (humphreysAlcoveInput_direct hd)
    hdelt

theorem permutation_rank_empirical_weak_concentration_hoeffding {m : ℕ} (hm : 1 ≤ m)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m) {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_empirical_weak_concentration_hoeffding_aux hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) hU

theorem permutation_rank_permuton_exponential_concentration_hoeffding {m : ℕ} (hm : 1 ≤ m)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨ permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_permuton_exponential_concentration_hoeffding_aux hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) hU

theorem permutation_rank_euclidean_shape_exponential_concentration_hoeffding {m : ℕ} (hm : 1 ≤ m)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m) {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
        (closure ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
          normalQuantileSurface (Fin (m + 1))))} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_euclidean_shape_exponential_concentration_hoeffding_aux hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) hepsilon

theorem signed_rank_closed_cube_permuton_concentration_hoeffding {m : ℕ} (hm : 1 ≤ m)
    (sign : Fin m → Bool) {U : Set (ProbabilityMeasure (ClosedCubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedClosedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | closedPermutationRankEmpiricalProbability n m pi ∉ U ∨
        closedPermutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  signed_rank_closed_cube_permuton_concentration_hoeffding_aux hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sign hU

theorem signed_rank_euclidean_shape_exponential_concentration_hoeffding {m : ℕ} (hm : 1 ≤ m)
    (sign : Fin m → Bool) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign
        {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
          (signedEuclideanLimitShape m sign)} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  signed_rank_euclidean_shape_exponential_concentration_hoeffding_aux hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sign hepsilon

theorem permutation_pattern_frequency_exponential_concentration_hoeffding {m : ℕ} (hm : 1 ≤ m)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_pattern_frequency_exponential_concentration_hoeffding_aux hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) q tau hepsilon

theorem fixed_pattern_frequency_source_hoeffding {m : ℕ} (hm : 1 ≤ m)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationSubsetPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  fixed_pattern_frequency_source_hoeffding_aux hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) q tau hepsilon


end Antichain
