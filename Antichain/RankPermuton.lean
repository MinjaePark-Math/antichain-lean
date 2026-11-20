import Antichain.RankBoxes
import Antichain.RankShapeTransfer
import Antichain.CubeProbabilitySpace

/-! Actual rank empirical measures and uniform-box permuton concentration. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

set_option maxHeartbeats 800000

theorem empirical_test_error_of_coordinate_close (d : ℕ) (g : CubePoint d →ᵇ ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n : ℕ, 0 < n → ∀ x y : CubeSample n d,
      (∀ j, x j ∈ cubePointSet d) → (∀ j, y j ∈ cubePointSet d) →
      (∀ j i, |x j i - y j i| ≤ delta) →
      |(∑ j, g (x j)) / n - (∑ j, g (y j)) / n| ≤ epsilon := by
  obtain ⟨eta, heta, huc⟩ := Metric.uniformContinuousOn_iff.mp
    ((cubePointSet_isCompact d).uniformContinuousOn_of_continuous g.continuous.continuousOn)
      epsilon hepsilon
  refine ⟨eta / 2, half_pos heta, ?_⟩
  intro n hn x y hxcube hycube hclose
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have herr (j : Fin n) : |g (x j) - g (y j)| ≤ epsilon := by
    have hdist : dist (x j) (y j) < eta := by
      have hh : dist (x j) (y j) ≤ eta / 2 :=
        (dist_pi_le_iff (half_pos heta).le).mpr (fun i => by simpa only [Real.dist_eq] using hclose j i)
      exact hh.trans_lt (by linarith)
    exact (huc (x j) (hxcube j) (y j) (hycube j) hdist).le
  calc
    _ = |∑ j, (g (x j) - g (y j))| / n := by
      rw [Finset.sum_sub_distrib, ← sub_div, abs_div, abs_of_pos hnR]
    _ ≤ (∑ j, |g (x j) - g (y j)|) / n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ (∑ _j : Fin n, epsilon) / n :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => herr j)) hnR.le
    _ = epsilon := by simp [hnR.ne']

variable {d : ℕ} [NeZero d]

theorem rank_empirical_test_exponential_tail (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (DKW : DKWInput) (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤
        |(∫ u, g u ∂(rankEmpiricalProbability n d x : Measure (CubePoint d))) -
          ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨delta, hdelta, htransport⟩ := empirical_test_error_of_coordinate_close d g
    (show 0 < epsilon / 4 by positivity)
  obtain ⟨ar, har, hdisplacement⟩ := rank_displacement_exponential_tail DKW d hd hdelta
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

theorem rank_empirical_weak_concentration (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => cubeAntichainLaw n d)
    (fun n x => rankEmpiricalProbability n d x) (limitingCubeProbability d) ?_ hU
  intro g epsilon hepsilon
  exact rank_empirical_test_exponential_tail hd H DKW g hepsilon

theorem rank_box_test_exponential_tail (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (DKW : DKWInput) (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤
        |(∫ u, g u ∂(cubeRankBoxProbability n d x : Measure (CubePoint d))) -
          ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_empirical_test_exponential_tail hd H DKW g
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

theorem rank_box_weak_concentration (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => cubeAntichainLaw n d)
    (fun n x => cubeRankBoxProbability n d x) (limitingCubeProbability d) ?_ hU
  intro g epsilon hepsilon
  exact rank_box_test_exponential_tail hd H DKW g hepsilon

/-- Proposition 6.1: both actual midpoint empirical ranks and actual uniformly
spread rank boxes concentrate exponentially in every fixed weak neighborhood. -/
theorem rank_permuton_exponential_concentration (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U ∨ cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hA (b : Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (if b then {x | rankEmpiricalProbability n d x ∉ U}
        else {x | cubeRankBoxProbability n d x ∉ U}) ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    cases b
    · exact rank_box_weak_concentration hd H DKW hU
    · exact rank_empirical_weak_concentration hd H DKW hU
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

def permutationRankCloud (n m : ℕ) (pi : Fin m → Equiv.Perm (Fin n)) : CubeSample n (m + 1) :=
  rankCenterCloud n (m + 1) (Fin.cons (Equiv.refl (Fin n)) pi)

def permutationRankEmpiricalProbability (n m : ℕ) (pi : Fin m → Equiv.Perm (Fin n)) :
    ProbabilityMeasure (CubePoint (m + 1)) :=
  empiricalCubeProbability n (m + 1) (permutationRankCloud n m pi)

def permutationRankBoxProbability (n m : ℕ) (pi : Fin m → Equiv.Perm (Fin n)) :
    ProbabilityMeasure (CubePoint (m + 1)) :=
  rankBoxProbability n (m + 1) (Fin.cons (Equiv.refl (Fin n)) pi)

theorem normalized_rank_coordinate (n m : ℕ) (r : Fin (m + 1) → Equiv.Perm (Fin n))
    (i : Fin (m + 1)) (j : Fin n) :
    (Fin.cons (Equiv.refl (Fin n)) (normalizeRankTuple n m r) :
      Fin (m + 1) → Equiv.Perm (Fin n)) i j = r i ((r 0).symm j) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · simp [normalizeRankTuple, Equiv.trans_apply]

theorem empiricalCubeProbability_reindex (n d : ℕ) (x : CubeSample n d) (e : Equiv.Perm (Fin n)) :
    empiricalCubeProbability n d (fun j => x (e j)) = empiricalCubeProbability n d x := by
  apply Subtype.ext
  change empiricalCubeMeasure n d (fun j => x (e j)) = empiricalCubeMeasure n d x
  by_cases hn : n = 0
  · simp [empiricalCubeMeasure, hn]
  · simp only [empiricalCubeMeasure, if_neg hn]
    congr 1
    exact Equiv.sum_comp e (fun j => Measure.dirac (x j))

theorem rankBoxProbability_normalize (n m : ℕ) (r : Fin (m + 1) → Equiv.Perm (Fin n)) :
    rankBoxProbability n (m + 1) (Fin.cons (Equiv.refl (Fin n)) (normalizeRankTuple n m r)) =
      rankBoxProbability n (m + 1) r := by
  apply Subtype.ext
  change rankBoxMeasure n (m + 1) _ = rankBoxMeasure n (m + 1) r
  by_cases hn : n = 0
  · simp [rankBoxMeasure, hn]
  · simp only [rankBoxMeasure, if_neg hn]
    have hbox (j : Fin n) :
        rankBoxLaw n (m + 1) (Fin.cons (Equiv.refl (Fin n)) (normalizeRankTuple n m r)) j =
          rankBoxLaw n (m + 1) r ((r 0).symm j) := by
      unfold rankBoxLaw rankBoxPoint
      congr 1
      funext u i
      rw [normalized_rank_coordinate]
    simp_rw [hbox]
    rw [Measure.sum_fintype, Measure.sum_fintype]
    congr 1
    exact Equiv.sum_comp (r 0).symm (rankBoxLaw n (m + 1) r)

theorem permutationRankEmpiricalProbability_normalized (n m : ℕ) (x : CubeSample n (m + 1)) :
    permutationRankEmpiricalProbability n m (cubeNormalizedRanks n m x) =
      rankEmpiricalProbability n (m + 1) x := by
  let r := coordinateRankPermutations n (m + 1) x
  have hcloud : permutationRankCloud n m (cubeNormalizedRanks n m x) =
      fun j => cubeRankCloud n (m + 1) x ((r 0).symm j) := by
    funext j i
    change rankMidpoint n ((Fin.cons (Equiv.refl (Fin n)) (normalizeRankTuple n m r) :
      Fin (m + 1) → Equiv.Perm (Fin n)) i j) =
      rankMidpoint n (r i ((r 0).symm j))
    rw [normalized_rank_coordinate]
  change empiricalCubeProbability n (m + 1) _ = empiricalCubeProbability n (m + 1) _
  rw [hcloud]
  exact empiricalCubeProbability_reindex _ _ _ _

theorem permutationRankBoxProbability_normalized (n m : ℕ) (x : CubeSample n (m + 1)) :
    permutationRankBoxProbability n m (cubeNormalizedRanks n m x) =
      cubeRankBoxProbability n (m + 1) x :=
  rankBoxProbability_normalize n m (coordinateRankPermutations n (m + 1) x)

theorem permutation_rank_permuton_exponential_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨
          permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_permuton_exponential_concentration (show 2 ≤ m + 1 by omega) H DKW hU
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← cubeAntichain_normalizedRanks_uniformOn n m,
    Measure.map_apply (cubeNormalizedRanks_measurable n m) (Set.to_countable _).measurableSet]
  simpa only [Set.preimage_setOf_eq, permutationRankEmpiricalProbability_normalized,
    permutationRankBoxProbability_normalized] using hn

theorem permutation_rank_empirical_weak_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_permuton_exponential_concentration hm H DKW hU
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  exact (measure_mono (fun _ hx => Or.inl hx)).trans hn

theorem empiricalCubeProbability_ae_mem_cube (n d : ℕ) (x : CubeSample n d)
    (hx : ∀ j, x j ∈ cubePointSet d) :
    ∀ᵐ u ∂(empiricalCubeProbability n d x : Measure (CubePoint d)), u ∈ cubePointSet d := by
  change ∀ᵐ u ∂empiricalCubeMeasure n d x, u ∈ cubePointSet d
  by_cases hn : n = 0
  · rw [empiricalCubeMeasure, if_pos hn]
    apply (ae_dirac_iff (measurableSet_cubePointSet d)).mpr
    intro i _
    norm_num
  · rw [empiricalCubeMeasure, if_neg hn]
    apply Measure.ae_smul_measure
    rw [← Measure.sum_fintype]
    exact Measure.ae_sum_iff.mpr (fun j =>
      (ae_dirac_iff (measurableSet_cubePointSet d)).mpr (hx j))

def closedRankEmpiricalProbability (n d : ℕ) (x : CubeSample n d) :
    ProbabilityMeasure (ClosedCubePoint d) :=
  projectClosedCubeProbability d (rankEmpiricalProbability n d x)

def closedRankBoxProbability (n d : ℕ) (x : CubeSample n d) :
    ProbabilityMeasure (ClosedCubePoint d) :=
  projectClosedCubeProbability d (cubeRankBoxProbability n d x)

theorem include_closedRankEmpiricalProbability (n d : ℕ) (x : CubeSample n d) :
    includeClosedCubeProbability d (closedRankEmpiricalProbability n d x) =
      rankEmpiricalProbability n d x :=
  include_projectClosedCubeProbability_of_ae d _
    (empiricalCubeProbability_ae_mem_cube n d _ (cubeRankCloud_mem_cube n d x))

theorem include_closedRankBoxProbability (n d : ℕ) (x : CubeSample n d) :
    includeClosedCubeProbability d (closedRankBoxProbability n d x) =
      cubeRankBoxProbability n d x :=
  include_projectClosedCubeProbability_of_ae d _
    (rankBoxMeasure_ae_mem_cube n d (coordinateRankPermutations n d x))

/-- The actual closed-cube spread measure has exactly uniform coordinate
marginals, so it is a permuton in the manuscript's probability space. -/
theorem closedRankBoxProbability_coordinate_uniform (n d : ℕ) (x : CubeSample n d) (i : Fin d) :
    (closedRankBoxProbability n d x : Measure (ClosedCubePoint d)).map (fun u => u.val i) =
      cubeCoordinateLaw := by
  change (closedRankBoxProbability n d x : Measure (ClosedCubePoint d)).map
    ((fun u : CubePoint d => u i) ∘ (Subtype.val : ClosedCubePoint d → CubePoint d)) = _
  rw [← Measure.map_map (measurable_pi_apply i) measurable_subtype_coe]
  change (includeClosedCubeProbability d (closedRankBoxProbability n d x) :
    Measure (CubePoint d)).map (fun u => u i) = _
  rw [include_closedRankBoxProbability]
  exact rankBoxMeasure_coordinate_uniform n d (coordinateRankPermutations n d x) i

theorem rank_closed_cube_permuton_exponential_concentration (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))}
    (hU : U ∈ 𝓝 (closedCubeLimitingProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  change U ∈ 𝓝 (projectClosedCubeProbability d (limitingCubeProbability d)) at hU
  have hV : projectClosedCubeProbability d ⁻¹' U ∈ 𝓝 (limitingCubeProbability d) :=
    ((projectClosedCubeProbability_continuous d).tendsto (limitingCubeProbability d)).eventually hU
  obtain ⟨alpha, ha, htail⟩ := rank_permuton_exponential_concentration (d := d) hd H DKW hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  change cubeAntichainLaw n d {x | projectClosedCubeProbability d (rankEmpiricalProbability n d x) ∉ U ∨
    projectClosedCubeProbability d (cubeRankBoxProbability n d x) ∉ U} ≤ _ at hn
  exact hn

/-- The weak-neighborhood assertion of Proposition 6.1 in the literal
closed-cube probability space. The Hausdorff assertion is separately
`rank_euclidean_shape_exponential_concentration`. -/
theorem rank_permuton_source (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (DKW : DKWInput)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U)
    (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_closed_cube_permuton_exponential_concentration hd H DKW (hUopen.mem_nhds hUmem)

end Antichain
