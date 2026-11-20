import Antichain.RankPermuton
import Antichain.SignedRankLimits
import Antichain.PatternFrequencySubsets
import Antichain.RankHoeffding

/-! The actual manuscript weak/box/Hausdorff/pattern transfers, now driven
by its fixed-order-statistic Hoeffding argument rather than DKW. -/
noncomputable section
namespace Antichain
open MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {d : ℕ} [NeZero d]

theorem rank_empirical_test_exponential_tail_hoeffding_aux (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤
        |(∫ u, g u ∂(rankEmpiricalProbability n d x : Measure (CubePoint d))) -
          ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨delta, hdelta, htransport⟩ := empirical_test_error_of_coordinate_close d g
    (show 0 < epsilon / 4 by positivity)
  obtain ⟨ar, har, hdisplacement⟩ := rank_displacement_exponential_tail_hoeffding d hd hdelta
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

theorem rank_empirical_weak_concentration_hoeffding_aux (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => cubeAntichainLaw n d)
    (fun n x => rankEmpiricalProbability n d x) (limitingCubeProbability d) ?_ hU
  intro g epsilon hepsilon
  exact rank_empirical_test_exponential_tail_hoeffding_aux hd H g hepsilon

theorem rank_box_test_exponential_tail_hoeffding_aux (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤
        |(∫ u, g u ∂(cubeRankBoxProbability n d x : Measure (CubePoint d))) -
          ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_empirical_test_exponential_tail_hoeffding_aux hd H g
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

theorem rank_box_weak_concentration_hoeffding_aux (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => cubeAntichainLaw n d)
    (fun n x => cubeRankBoxProbability n d x) (limitingCubeProbability d) ?_ hU
  intro g epsilon hepsilon
  exact rank_box_test_exponential_tail_hoeffding_aux hd H g hepsilon

theorem rank_permuton_exponential_concentration_hoeffding_aux (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (CubePoint d))} (hU : U ∈ 𝓝 (limitingCubeProbability d)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | rankEmpiricalProbability n d x ∉ U ∨ cubeRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hA (b : Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (if b then {x | rankEmpiricalProbability n d x ∉ U}
        else {x | cubeRankBoxProbability n d x ∉ U}) ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    cases b
    · exact rank_box_weak_concentration_hoeffding_aux hd H hU
    · exact rank_empirical_weak_concentration_hoeffding_aux hd H hU
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

theorem permutation_rank_permuton_exponential_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1))
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨
          permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_permuton_exponential_concentration_hoeffding_aux (show 2 ≤ m + 1 by omega) H hU
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← cubeAntichain_normalizedRanks_uniformOn n m,
    Measure.map_apply (cubeNormalizedRanks_measurable n m) (Set.to_countable _).measurableSet]
  simpa only [Set.preimage_setOf_eq, permutationRankEmpiricalProbability_normalized,
    permutationRankBoxProbability_normalized] using hn

theorem permutation_rank_empirical_weak_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1))
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (limitingCubeProbability (m + 1))) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_permuton_exponential_concentration_hoeffding_aux hm H hU
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  exact (measure_mono (fun _ hx => Or.inl hx)).trans hn

theorem rank_closed_cube_permuton_exponential_concentration_hoeffding_aux (hd : 2 ≤ d)
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
  obtain ⟨alpha, ha, htail⟩ := rank_permuton_exponential_concentration_hoeffding_aux (d := d) hd H hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  change cubeAntichainLaw n d {x | projectClosedCubeProbability d (rankEmpiricalProbability n d x) ∉ U ∨
    projectClosedCubeProbability d (cubeRankBoxProbability n d x) ∉ U} ≤ _ at hn
  exact hn

theorem rank_permuton_source_hoeffding_aux (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U)
    (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | closedRankEmpiricalProbability n d x ∉ U ∨
        closedRankBoxProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  rank_closed_cube_permuton_exponential_concentration_hoeffding_aux hd H (hUopen.mem_nhds hUmem)

theorem rank_euclidean_shape_exponential_concentration_hoeffding_aux {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | δ < hausdorffDist (euclideanRankSampleSet n d x)
        (closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) ''
          normalQuantileSurface (Fin d)))} ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  let S : Set (EuclideanSpace ℝ (Fin d)) := closure
    ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) '' normalQuantileSurface (Fin d))
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
  obtain ⟨a, ha, hrank⟩ := rank_displacement_exponential_tail_hoeffding d hd
    (show 0 < δ / (2 * Real.sqrt (d : ℝ)) by positivity)
  obtain ⟨b, hb, hshape⟩ := euclidean_shape_exponential_concentration hd H (half_pos hδ)
  let A : Bool → ∀ n, Set (CubeSample n d) := fun p n =>
    if p then rankDisplacementEvent n d (δ / (2 * Real.sqrt (d : ℝ)))
    else {x | δ / 2 < hausdorffDist (euclideanSampleSet n d x) S}
  have hA (p : Bool) : ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (A p n) ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
    cases p
    · exact ⟨b, hb, hshape⟩
    · exact ⟨a, ha, hrank⟩
  obtain ⟨α, hα, htail⟩ := finite_union_exponential_tail (fun n => cubeAntichainLaw n d) A hA
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply le_trans (measure_mono ?_) hn
  intro x hx
  rcases rank_cloud_euclidean_shape_event_subset n hnpos hδ S hx with hdisp | hshape
  · exact Set.mem_iUnion.mpr ⟨true, hdisp⟩
  · exact Set.mem_iUnion.mpr ⟨false, hshape⟩

theorem signed_rank_empirical_weak_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hV : signedCubeProbabilityMap m sign ⁻¹' U ∈ 𝓝 (limitingCubeProbability (m + 1)) :=
    ((signedCubeProbabilityMap_continuous m sign).tendsto (limitingCubeProbability (m + 1))).eventually hU
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_empirical_weak_concentration_hoeffding_aux hm H hV
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

theorem signed_rank_empirical_test_tail_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
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
  obtain ⟨alpha, ha, htail⟩ := signed_rank_empirical_weak_concentration_hoeffding_aux hm H sign (hUopen.mem_nhds hUmem)
  refine ⟨alpha, ha, ?_⟩
  simpa only [U, Set.mem_setOf_eq, not_lt] using htail

theorem signed_rank_box_test_tail_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    (g : CubePoint (m + 1) →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | epsilon ≤
        |(∫ u, g u ∂(permutationRankBoxProbability n m pi : Measure (CubePoint (m + 1)))) -
          ∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1)))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := signed_rank_empirical_test_tail_hoeffding_aux hm H sign g
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

theorem signed_rank_box_weak_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => uniformSignedAvoidanceLaw n m sign)
    (fun n pi => permutationRankBoxProbability n m pi) (signedLimitingCubeProbability m sign) ?_ hU
  intro g epsilon hepsilon
  exact signed_rank_box_test_tail_hoeffding_aux hm H sign g hepsilon

theorem signed_rank_permuton_exponential_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
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
    · exact signed_rank_box_weak_concentration_hoeffding_aux hm H sign hU
    · exact signed_rank_empirical_weak_concentration_hoeffding_aux hm H sign hU
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail
    (fun n => uniformSignedAvoidanceLaw n m sign) A hA
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  apply le_trans (measure_mono ?_) hn
  intro pi hpi
  rcases hpi with hpi | hpi
  · exact Set.mem_iUnion.mpr ⟨true, hpi⟩
  · exact Set.mem_iUnion.mpr ⟨false, hpi⟩

theorem permutation_rank_euclidean_shape_exponential_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m) {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
        (closure ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
          normalQuantileSurface (Fin (m + 1))))} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_euclidean_shape_exponential_concentration_hoeffding_aux
    (show 2 ≤ m + 1 by omega) H hepsilon
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← cubeAntichain_normalizedRanks_uniformOn n m,
    Measure.map_apply (cubeNormalizedRanks_measurable n m) (Set.toFinite _).measurableSet]
  simpa only [Set.preimage_setOf_eq, permutationEuclideanRankSet_normalized] using hn

theorem signed_rank_euclidean_shape_exponential_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (sign : Fin m → Bool)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign
        {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi) (signedEuclideanLimitShape m sign)} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_euclidean_shape_exponential_concentration_hoeffding_aux hm H hepsilon
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← uniformSignedAvoidanceLaw_reflect n m hm sign,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hn
  have hdist (pi : Fin m → Equiv.Perm (Fin n)) :
      hausdorffDist (permutationEuclideanRankSet n m pi) (signedEuclideanLimitShape m sign) =
        hausdorffDist (permutationEuclideanRankSet n m (reflectRankTuple sign pi))
          (closure ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
            normalQuantileSurface (Fin (m + 1)))) := by
    rw [signedEuclideanLimitShape,
      ← reflectRankTuple_involutive sign pi, permutationEuclideanRankSet_reflect,
      hausdorffDist_image (signedEuclideanReflection_isometry m sign),
      reflectRankTuple_involutive]
  simpa only [Set.preimage_setOf_eq, hdist] using hn

theorem signed_rank_closed_cube_permuton_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
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
  obtain ⟨alpha, ha, htail⟩ := signed_rank_permuton_exponential_concentration_hoeffding_aux hm H sign hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  change uniformSignedAvoidanceLaw n m sign
    {pi | projectClosedCubeProbability (m + 1) (permutationRankEmpiricalProbability n m pi) ∉ U ∨
      projectClosedCubeProbability (m + 1) (permutationRankBoxProbability n m pi) ∉ U} ≤ _ at hn
  exact hn

theorem permutation_pattern_frequency_exponential_concentration_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
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
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_permuton_exponential_concentration_hoeffding_aux hm H hU
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

theorem fixed_pattern_frequency_source_hoeffding_aux {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1))
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationSubsetPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  simp_rw [permutationSubsetPatternFrequency_eq]
  exact permutation_pattern_frequency_exponential_concentration_hoeffding_aux hm H q tau hepsilon

end Antichain
