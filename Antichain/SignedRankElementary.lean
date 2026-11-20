import Antichain.SignedRankLimits
import Antichain.RankPermutonElementary

/-! Actual signed weak limits from the proved elementary CDF control. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology BoundedContinuousFunction

set_option maxHeartbeats 800000

theorem signed_rank_empirical_weak_concentration_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hV : signedCubeProbabilityMap m sign ⁻¹' U ∈ 𝓝 (limitingCubeProbability (m + 1)) :=
    ((signedCubeProbabilityMap_continuous m sign).tendsto (limitingCubeProbability (m + 1))).eventually hU
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_empirical_weak_concentration_elementary hm H hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  rw [← uniformSignedAvoidanceLaw_reflect n m hm sign,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hn
  convert hn using 1
  congr 1
  ext pi
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have heq := permutationRankEmpiricalProbability_reflect n m hnpos sign (reflectRankTuple sign pi)
  rw [reflectRankTuple_involutive] at heq
  rw [← heq]

theorem signed_rank_empirical_test_tail_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    (g : CubePoint (m + 1) →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | epsilon ≤
        |(∫ u, g u ∂(permutationRankEmpiricalProbability n m pi : Measure (CubePoint (m + 1)))) -
          ∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1)))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  let U : Set (ProbabilityMeasure (CubePoint (m + 1))) :=
    {nu | |(∫ u, g u ∂(nu : Measure (CubePoint (m + 1)))) -
      ∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1)))| < epsilon}
  have hUopen : IsOpen U :=
    isOpen_lt ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).sub continuous_const).abs
      continuous_const
  have hUmem : signedLimitingCubeProbability m sign ∈ U := by
    simp only [U, Set.mem_setOf_eq, sub_self, abs_zero]
    exact hepsilon
  obtain ⟨alpha, ha, htail⟩ := signed_rank_empirical_weak_concentration_elementary hm H sign (hUopen.mem_nhds hUmem)
  refine ⟨alpha, ha, ?_⟩
  simpa only [U, Set.mem_setOf_eq, not_lt] using htail

theorem signed_rank_box_test_tail_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    (g : CubePoint (m + 1) →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | epsilon ≤
        |(∫ u, g u ∂(permutationRankBoxProbability n m pi : Measure (CubePoint (m + 1)))) -
          ∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1)))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := signed_rank_empirical_test_tail_elementary hm H sign g
    (show 0 < epsilon / 2 by positivity)
  have herr := rankBoxProbability_test_error (m + 1) g (show 0 < epsilon / 4 by positivity)
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, herr] with n hn hnerror
  apply le_trans (measure_mono ?_) hn
  intro pi hbad
  have he := hnerror (Fin.cons (Equiv.refl (Fin n)) pi)
  change |(∫ u, g u ∂(permutationRankBoxProbability n m pi : Measure (CubePoint (m + 1)))) -
    ∫ u, g u ∂(permutationRankEmpiricalProbability n m pi : Measure (CubePoint (m + 1)))| ≤ epsilon / 4 at he
  have htri := abs_sub_le
    (∫ u, g u ∂(permutationRankBoxProbability n m pi : Measure (CubePoint (m + 1))))
    (∫ u, g u ∂(permutationRankEmpiricalProbability n m pi : Measure (CubePoint (m + 1))))
    (∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1))))
  change epsilon ≤ _ at hbad
  change epsilon / 2 ≤ _
  linarith

theorem signed_rank_box_weak_concentration_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => uniformSignedAvoidanceLaw n m sign)
    (fun n pi => permutationRankBoxProbability n m pi) (signedLimitingCubeProbability m sign) ?_ hU
  intro g epsilon hepsilon
  exact signed_rank_box_test_tail_elementary hm H sign g hepsilon

theorem signed_rank_permuton_exponential_concentration_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨
        permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  let A : Bool → ∀ n : ℕ, Set (Fin m → Equiv.Perm (Fin n)) := fun b n =>
    if b then {pi | permutationRankEmpiricalProbability n m pi ∉ U}
    else {pi | permutationRankBoxProbability n m pi ∉ U}
  have hA (b : Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign (A b n) ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    cases b
    · exact signed_rank_box_weak_concentration_elementary hm H sign hU
    · exact signed_rank_empirical_weak_concentration_elementary hm H sign hU
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail
    (fun n => uniformSignedAvoidanceLaw n m sign) A hA
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  apply le_trans (measure_mono ?_) hn
  intro pi hpi
  rcases hpi with hpi | hpi
  · exact Set.mem_iUnion.mpr ⟨true, hpi⟩
  · exact Set.mem_iUnion.mpr ⟨false, hpi⟩

theorem signed_rank_closed_cube_permuton_concentration_elementary {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (ClosedCubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedClosedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | closedPermutationRankEmpiricalProbability n m pi ∉ U ∨
        closedPermutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  change U ∈ 𝓝 (projectClosedCubeProbability (m + 1) (signedLimitingCubeProbability m sign)) at hU
  have hV : projectClosedCubeProbability (m + 1) ⁻¹' U ∈ 𝓝 (signedLimitingCubeProbability m sign) :=
    ((projectClosedCubeProbability_continuous (m + 1)).tendsto (signedLimitingCubeProbability m sign)).eventually hU
  obtain ⟨alpha, ha, htail⟩ := signed_rank_permuton_exponential_concentration_elementary hm H sign hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  change uniformSignedAvoidanceLaw n m sign
    {pi | projectClosedCubeProbability (m + 1) (permutationRankEmpiricalProbability n m pi) ∉ U ∨
      projectClosedCubeProbability (m + 1) (permutationRankBoxProbability n m pi) ∉ U} ≤ _ at hn
  exact hn

end Antichain
