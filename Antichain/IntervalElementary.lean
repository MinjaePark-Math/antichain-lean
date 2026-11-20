import Antichain.RankPermutonElementary
import Antichain.DirectAlcoveInput
import Antichain.FinalIntervalApplication

/-! Actual uniform weak-order interval limits with no external mathematical inputs. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

theorem weakBruhat_interval_empirical_concentration_elementary
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | intervalRankEmpiricalProbability n I ∉ U} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨α, hα, htail⟩ := permutation_rank_empirical_weak_concentration_elementary
    (m := 2) (by decide) (humphreysAlcoveInput_direct (by decide : 2 ≤ 3))
    (intervalProbabilityMap_preimage_neighborhood hU)
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  rw [uniformInterval_weak_event_eq_avoidance n hnpos]
  simpa only [permutationRankEmpiricalProbability, avoidanceRankTripleCloud_eq_permutationRankCloud,
    Set.mem_preimage] using hn

/-- The literal printed mean-square predictor error under the actual finite
uniform interval law, without a cited concentration premise. -/
theorem weakBruhat_interval_predictor_exponential_tail_elementary {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      uniformWeakBruhatIntervalLaw n {I | δ < intervalPredictorAverage n I} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  obtain ⟨U, hU, hsmall⟩ := intervalPredictorError_weak_neighborhood hδ
  obtain ⟨α, hα, htail⟩ := weakBruhat_interval_empirical_concentration_elementary hU
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply (measure_mono ?_).trans hn
  intro I hbad hmem
  have hs := hsmall (intervalRankEmpiricalProbability n I) hmem
  rw [intervalRankPredictor_empirical_integral n hnpos I] at hs
  exact (not_lt_of_gt hs) hbad

theorem weakBruhat_interval_empirical_in_probability_elementary
    {U : Set (ProbabilityMeasure (CubePoint 3))} (hU : U ∈ 𝓝 intervalLimitProbability) :
    Tendsto (fun n : ℕ ↦ uniformWeakBruhatIntervalLaw n
      {I | intervalRankEmpiricalProbability n I ∉ U}) atTop (𝓝 0) := by
  obtain ⟨α, hα, htail⟩ := weakBruhat_interval_empirical_concentration_elementary hU
  exact exponential_tail_tendsto_zero _ hα htail

theorem weakBruhat_interval_predictor_in_probability_elementary {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ uniformWeakBruhatIntervalLaw n
      {I | δ < intervalPredictorAverage n I}) atTop (𝓝 0) := by
  obtain ⟨α, hα, htail⟩ := weakBruhat_interval_predictor_exponential_tail_elementary hδ
  exact exponential_tail_tendsto_zero _ hα htail

/-- The source's arbitrary centered bivariate Gaussian with unit variances
and covariance -1/2, under the actual uniform interval law. -/
theorem weakBruhat_interval_gaussian_source_elementary (ν : Measure (ℝ × ℝ)) [IsGaussian ν]
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
  exact weakBruhat_interval_empirical_concentration_elementary hU

end Antichain
