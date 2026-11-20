import Antichain.RankPermuton
import Antichain.ElementaryCDFConcentration

/-! Actual weak rank/permuton consequences of the proved elementary CDF tail. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

set_option maxHeartbeats 800000

variable {d : ℕ} [NeZero d]

theorem rank_empirical_test_exponential_tail_elementary (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤
        |(∫ u, g u ∂(rankEmpiricalProbability n d x : Measure (CubePoint d))) -
          ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨delta, hdelta, htransport⟩ := empirical_test_error_of_coordinate_close d g
    (show 0 < epsilon / 4 by positivity)
  obtain ⟨ar, har, hdisplacement⟩ := rank_displacement_exponential_tail_elementary d hd hdelta
  obtain ⟨ax, hax, hsample⟩ := cube_test_exponential_tail hd H g
    (show 0 < epsilon / 2 by positivity)
  let A : Bool → ∀ n : ℕ, Set (CubeSample n d) := fun b n =>
    if b then rankDisplacementEvent n d delta else
      {x | epsilon / 2 ≤ |(∑ j, g (x j)) / n - ∫ u, g u ∂limitingAntichainMeasure (Fin d)|}
  have hA (b : Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (A b n) ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    cases b
    · exact ⟨ax, hax, hsample⟩
    · exact ⟨ar, har, hdisplacement⟩
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail (fun n => cubeAntichainLaw n d) A hA
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply le_trans (measure_mono_ae ?_) hn
  filter_upwards [cubeAntichainLaw_ae_geometry n d] with x hx
  intro hbad
  by_contra hnot
  have hclose : ∀ j i, |x j i - cubeRankCloud n d x j i| ≤ delta := by
    intro j i
    exact le_of_not_gt (fun h => hnot (Set.mem_iUnion.mpr ⟨true, ⟨j, i, h⟩⟩))
  have hsampleSmall : |(∑ j, g (x j)) / n - ∫ u, g u ∂limitingAntichainMeasure (Fin d)| < epsilon / 2 :=
    lt_of_not_ge (fun h => hnot (Set.mem_iUnion.mpr ⟨false, h⟩))
  have herr := htransport n hnpos x (cubeRankCloud n d x) hx.1 (cubeRankCloud_mem_cube n d x) hclose
  change epsilon ≤ |(∫ u, g u ∂(empiricalCubeProbability n d (cubeRankCloud n d x) : Measure (CubePoint d))) - _| at hbad
  rw [empiricalCubeProbability_integral n d hnpos _ g] at hbad
  have htri := abs_sub_le ((∑ j, g (cubeRankCloud n d x j)) / n) ((∑ j, g (x j)) / n)
    (∫ u, g u ∂limitingAntichainMeasure (Fin d))
  rw [abs_sub_comm ((∑ j, g (cubeRankCloud n d x j)) / n) ((∑ j, g (x j)) / n)] at htri
  linarith

theorem rank_empirical_weak_concentration_elementary (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => cubeAntichainLaw n d)
    (fun n x => rankEmpiricalProbability n d x) (limitingCubeProbability d) ?_ hU
  intro g epsilon hepsilon
  exact rank_empirical_test_exponential_tail_elementary hd H g hepsilon

theorem rank_box_test_exponential_tail_elementary (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤
        |(∫ u, g u ∂(cubeRankBoxProbability n d x : Measure (CubePoint d))) -
          ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_empirical_test_exponential_tail_elementary hd H g
    (show 0 < epsilon / 2 by positivity)
  have herr := rankBoxProbability_test_error d g (show 0 < epsilon / 4 by positivity)
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, herr] with n hn hnerror
  apply le_trans (measure_mono ?_) hn
  intro x hx
  have he := hnerror (coordinateRankPermutations n d x)
  change |(∫ u, g u ∂(cubeRankBoxProbability n d x : Measure (CubePoint d))) -
    (∫ u, g u ∂(rankEmpiricalProbability n d x : Measure (CubePoint d)))| ≤ epsilon / 4 at he
  have htri := abs_sub_le
    (∫ u, g u ∂(cubeRankBoxProbability n d x : Measure (CubePoint d)))
    (∫ u, g u ∂(rankEmpiricalProbability n d x : Measure (CubePoint d)))
    (∫ u, g u ∂limitingAntichainMeasure (Fin d))
  change epsilon ≤ |(∫ u, g u ∂(cubeRankBoxProbability n d x : Measure (CubePoint d))) - _| at hx
  change epsilon / 2 ≤ _
  linarith

theorem rank_box_weak_concentration_elementary (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => cubeAntichainLaw n d)
    (fun n x => cubeRankBoxProbability n d x) (limitingCubeProbability d) ?_ hU
  intro g epsilon hepsilon
  exact rank_box_test_exponential_tail_elementary hd H g hepsilon

/-- Proposition 6.1: both actual midpoint empirical ranks and actual uniformly
spread rank boxes concentrate exponentially in every fixed weak neighborhood. -/

theorem rank_permuton_exponential_concentration_elementary (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U ∨ cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hA (b : Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (if b then {x | rankEmpiricalProbability n d x ∉ U}
        else {x | cubeRankBoxProbability n d x ∉ U}) ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    cases b
    · exact rank_box_weak_concentration_elementary hd H hU
    · exact rank_empirical_weak_concentration_elementary hd H hU
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail (I := Bool)
    (Ω := fun n => CubeSample n d) (fun n => cubeAntichainLaw n d)
    (fun b n => if b then {x | rankEmpiricalProbability n d x ∉ U}
      else {x | cubeRankBoxProbability n d x ∉ U}) hA
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  apply le_trans (measure_mono ?_) hn
  intro x hx
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨true, hx⟩
  · exact Set.mem_iUnion.mpr ⟨false, hx⟩

theorem permutation_rank_permuton_exponential_concentration_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1))
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨
          permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_permuton_exponential_concentration_elementary (show 2 ≤ m + 1 by omega) H hU
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← cubeAntichain_normalizedRanks_uniformOn n m,
    Measure.map_apply (cubeNormalizedRanks_measurable n m) (Set.to_countable _).measurableSet]
  simpa only [Set.preimage_setOf_eq, permutationRankEmpiricalProbability_normalized,
    permutationRankBoxProbability_normalized] using hn

theorem permutation_rank_empirical_weak_concentration_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1))
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_permuton_exponential_concentration_elementary hm H hU
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  exact (measure_mono (fun _ hx => Or.inl hx)).trans hn

theorem rank_closed_cube_permuton_exponential_concentration_elementary (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))}
    (hU : U ∈ 𝓝 (closedCubeLimitingProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  change U ∈ 𝓝 (projectClosedCubeProbability d (limitingCubeProbability d)) at hU
  have hV : projectClosedCubeProbability d ⁻¹' U ∈ 𝓝 (limitingCubeProbability d) :=
    ((projectClosedCubeProbability_continuous d).tendsto (limitingCubeProbability d)).eventually hU
  obtain ⟨alpha, ha, htail⟩ := rank_permuton_exponential_concentration_elementary (d := d) hd H hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  change cubeAntichainLaw n d {x | projectClosedCubeProbability d (rankEmpiricalProbability n d x) ∉ U ∨
    projectClosedCubeProbability d (cubeRankBoxProbability n d x) ∉ U} ≤ _ at hn
  exact hn

/-- The weak-neighborhood assertion of Proposition 6.1 in the literal
closed-cube probability space. The Hausdorff assertion is separately
`rank_euclidean_shape_exponential_concentration`. -/

theorem rank_permuton_source_elementary (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U)
    (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_closed_cube_permuton_exponential_concentration_elementary hd H (hUopen.mem_nhds hUmem)

end Antichain
