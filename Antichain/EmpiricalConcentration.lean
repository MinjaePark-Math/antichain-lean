import Antichain.CubeConcentration

/-! The full actual weak empirical concentration theorem and continuity-set frequencies. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

/-- Theorem 2.1's weak-neighborhood estimate for the actual uniform-antichain
sample and actual limiting law. All probabilistic and finite-test steps are
supplied; only the major cited alcove geometry remains an external premise. -/
theorem empirical_cube_weak_concentration (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | empiricalCubeProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => cubeAntichainLaw n d)
    (fun n x => empiricalCubeProbability n d x) (limitingCubeProbability d) ?_ hU
  intro g epsilon hepsilon
  obtain ⟨alpha, ha, htail⟩ := cube_test_exponential_tail hd H g hepsilon
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have heq : {x : CubeSample n d | epsilon ≤
      |(∫ u, g u ∂(empiricalCubeProbability n d x : Measure (CubePoint d))) -
        ∫ u, g u ∂(limitingCubeProbability d : Measure (CubePoint d))|} =
      {x : CubeSample n d | epsilon ≤ |(∑ j, g (x j)) / (n : ℝ) -
        ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [empiricalCubeProbability_integral n d hnpos x g]
    rfl
  rwa [heq]

def empiricalSetFrequency (n d : ℕ) (B : Set (CubePoint d)) (x : CubeSample n d) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => x j ∈ B)).card : ℝ) / (n : ℝ)

theorem empiricalCubeProbability_set_eq_frequency (n d : ℕ) (hn : 0 < n)
    (B : Set (CubePoint d)) (x : CubeSample n d) :
    ((empiricalCubeProbability n d x : Measure (CubePoint d)) B).toReal =
      empiricalSetFrequency n d B x := by
  classical
  change (empiricalCubeMeasure n d x B).toReal = _
  simp [empiricalCubeMeasure, hn.ne', Measure.smul_apply, Measure.finset_sum_apply,
    Measure.dirac_apply, Set.indicator, empiricalSetFrequency, div_eq_mul_inv,
    mul_comm]

/-- The continuity-set consequence, in the stronger exponential form, with
the literal fraction of sampled labels in B. -/
theorem empirical_continuity_set_concentration (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {B : Set (CubePoint d)} (hB : limitingAntichainMeasure (Fin d) (frontier B) = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤
        |empiricalSetFrequency n d B x - (limitingAntichainMeasure (Fin d) B).toReal|} ≤
          ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := continuity_set_concentration_of_weak
    (fun n => cubeAntichainLaw n d) (fun n x => empiricalCubeProbability n d x)
    (limitingCubeProbability d) (fun U hU => empirical_cube_weak_concentration hd H hU) hB hepsilon
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have heq : {x : CubeSample n d | epsilon ≤
      |((empiricalCubeProbability n d x : Measure (CubePoint d)) B).toReal -
        ((limitingCubeProbability d : Measure (CubePoint d)) B).toReal|} =
      {x : CubeSample n d | epsilon ≤
        |empiricalSetFrequency n d B x - (limitingAntichainMeasure (Fin d) B).toReal|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [empiricalCubeProbability_set_eq_frequency n d hnpos B x]
    rfl
  rwa [heq] at hn

end Antichain
