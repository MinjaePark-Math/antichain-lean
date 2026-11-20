import Antichain.DKWReverseMartingale
import Antichain.DirectAlcoveInput
import Antichain.RankPermuton
import Antichain.RankShapeTransfer
import Antichain.SignedRankLimits
import Antichain.PatternFrequencySubsets
import Antichain.FinalIntervalApplication

/-! Source-facing rank conclusions following the written sharp-DKW route.
The exact finite-n DKW bound is proved in DKWReverseMartingale; the alcove
package is also supplied by its actual proof.  No cited probability or
geometry record is a hypothesis of any theorem in this file. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology

theorem rank_displacement_exponential_tail_sharp (d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (rankDisplacementEvent n d epsilon) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_displacement_exponential_tail sharpDKWInput_proved d hd hepsilon

theorem rank_permuton_exponential_concentration_sharp {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U ∨ cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_permuton_exponential_concentration hd (humphreysAlcoveInput_direct hd)
    sharpDKWInput_proved hU

/-- Proposition 6.1 in its literal closed-cube weak space, using the written
sharp-DKW order-statistic argument with both formerly cited inputs proved. -/
theorem rank_permuton_source_sharp {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U)
    (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_permuton_source hd (humphreysAlcoveInput_direct hd) sharpDKWInput_proved hUopen hUmem

theorem rank_euclidean_shape_exponential_concentration_sharp {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) {delta : ℝ} (hdelt : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | delta < hausdorffDist (euclideanRankSampleSet n d x)
        (closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) ''
          normalQuantileSurface (Fin d)))} ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_euclidean_shape_exponential_concentration hd (humphreysAlcoveInput_direct hd)
    sharpDKWInput_proved hdelt

theorem permutation_rank_empirical_weak_concentration_sharp {m : ℕ} (hm : 1 ≤ m)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m) {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_empirical_weak_concentration hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sharpDKWInput_proved hU

theorem permutation_rank_permuton_exponential_concentration_sharp {m : ℕ} (hm : 1 ≤ m)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨ permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_permuton_exponential_concentration hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sharpDKWInput_proved hU

theorem permutation_rank_euclidean_shape_exponential_concentration_sharp {m : ℕ} (hm : 1 ≤ m)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m) {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
        (closure ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
          normalQuantileSurface (Fin (m + 1))))} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_rank_euclidean_shape_exponential_concentration hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sharpDKWInput_proved hepsilon

theorem signed_rank_closed_cube_permuton_concentration_sharp {m : ℕ} (hm : 1 ≤ m)
    (sign : Fin m → Bool) {U : Set (ProbabilityMeasure (ClosedCubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedClosedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | closedPermutationRankEmpiricalProbability n m pi ∉ U ∨
        closedPermutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  signed_rank_closed_cube_permuton_concentration hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sharpDKWInput_proved sign hU

theorem signed_rank_euclidean_shape_exponential_concentration_sharp {m : ℕ} (hm : 1 ≤ m)
    (sign : Fin m → Bool) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign
        {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
          (signedEuclideanLimitShape m sign)} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  signed_rank_euclidean_shape_exponential_concentration hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sharpDKWInput_proved sign hepsilon

theorem permutation_pattern_frequency_exponential_concentration_sharp {m : ℕ} (hm : 1 ≤ m)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  permutation_pattern_frequency_exponential_concentration hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sharpDKWInput_proved q tau hepsilon

theorem fixed_pattern_frequency_source_sharp {m : ℕ} (hm : 1 ≤ m)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationSubsetPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  fixed_pattern_frequency_source hm
    (humphreysAlcoveInput_direct (show 2 ≤ m + 1 by omega)) sharpDKWInput_proved q tau hepsilon

theorem weakBruhat_interval_empirical_concentration_sharp
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  weakBruhat_interval_empirical_concentration
    (humphreysAlcoveInput_direct (by decide : 2 ≤ 3)) sharpDKWInput_proved hU

theorem weakBruhat_interval_predictor_exponential_tail_sharp {delta : ℝ} (hd : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | delta < intervalPredictorAverage n I} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  weakBruhat_interval_predictor_exponential_tail
    (humphreysAlcoveInput_direct (by decide : 2 ≤ 3)) sharpDKWInput_proved hd

theorem weakBruhat_interval_empirical_in_probability_sharp
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    Tendsto (fun n : ℕ => uniformWeakBruhatIntervalLaw n
      {I | intervalRankEmpiricalProbability n I ∉ U}) atTop (𝓝 0) :=
  weakBruhat_interval_empirical_in_probability
    (humphreysAlcoveInput_direct (by decide : 2 ≤ 3)) sharpDKWInput_proved hU

theorem weakBruhat_interval_predictor_in_probability_sharp {delta : ℝ} (hd : 0 < delta) :
    Tendsto (fun n : ℕ => uniformWeakBruhatIntervalLaw n
      {I | delta < intervalPredictorAverage n I}) atTop (𝓝 0) :=
  weakBruhat_interval_predictor_in_probability
    (humphreysAlcoveInput_direct (by decide : 2 ≤ 3)) sharpDKWInput_proved hd

theorem weakBruhat_interval_gaussian_source_sharp (nu : Measure (ℝ × ℝ)) [IsGaussian nu]
    (h0 : (∫ z, z.1 ∂nu) = 0) (h1 : (∫ z, z.2 ∂nu) = 0)
    (hv0 : Var[Prod.fst; nu] = 1) (hv1 : Var[Prod.snd; nu] = 1)
    (hcov : cov[Prod.fst, Prod.snd; nu] = -(1 : ℝ) / 2)
    {U : Set (ProbabilityMeasure (CubePoint 3))}
    (hU : U ∈ 𝓝 (centeredBivariateIntervalProbability nu)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  weakBruhat_interval_gaussian_source
    (humphreysAlcoveInput_direct (by decide : 2 ≤ 3)) sharpDKWInput_proved nu h0 h1 hv0 hv1 hcov hU

end Antichain
