import Antichain.ElementaryCDFConcentration
import Antichain.DirectAlcoveInput
import Antichain.RankShapeTransfer
import Antichain.SignedRankLimits

/-! Actual Euclidean rank-cloud limits with no external alcove or DKW premise. -/

noncomputable section

namespace Antichain

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology ENNReal

theorem rank_euclidean_shape_exponential_concentration_elementary {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | δ < hausdorffDist (euclideanRankSampleSet n d x)
        (closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) ''
          normalQuantileSurface (Fin d)))} ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  let S : Set (EuclideanSpace ℝ (Fin d)) := closure
    ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) '' normalQuantileSurface (Fin d))
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
  obtain ⟨a, ha, hrank⟩ := rank_displacement_exponential_tail_elementary d hd
    (show 0 < δ / (2 * Real.sqrt (d : ℝ)) by positivity)
  obtain ⟨b, hb, hshape⟩ := euclidean_shape_exponential_concentration hd
    (humphreysAlcoveInput_direct hd) (half_pos hδ)
  let A : Bool → ∀ n, Set (CubeSample n d) := fun p n ↦
    if p then rankDisplacementEvent n d (δ / (2 * Real.sqrt (d : ℝ)))
    else {x | δ / 2 < hausdorffDist (euclideanSampleSet n d x) S}
  have hA (p : Bool) : ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (A p n) ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
    cases p
    · exact ⟨b, hb, hshape⟩
    · exact ⟨a, ha, hrank⟩
  obtain ⟨α, hα, htail⟩ := finite_union_exponential_tail (fun n ↦ cubeAntichainLaw n d) A hA
  refine ⟨α, hα, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply le_trans (measure_mono ?_) hn
  intro x hx
  rcases rank_cloud_euclidean_shape_event_subset n hnpos hδ S hx with hdisp | hshape
  · exact Set.mem_iUnion.mpr ⟨true, hdisp⟩
  · exact Set.mem_iUnion.mpr ⟨false, hshape⟩

theorem permutation_rank_euclidean_shape_exponential_concentration_elementary {m : ℕ}
    (hm : 1 ≤ m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
          (closure ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
            normalQuantileSurface (Fin (m + 1))))} ≤
          ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_euclidean_shape_exponential_concentration_elementary
    (show 2 ≤ m + 1 by omega) hepsilon
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← cubeAntichain_normalizedRanks_uniformOn n m,
    Measure.map_apply (cubeNormalizedRanks_measurable n m) (Set.toFinite _).measurableSet]
  simpa only [Set.preimage_setOf_eq, permutationEuclideanRankSet_normalized] using hn

/-- The actual uniform signed-avoidance class converges to its reflected
surface in the literal native Euclidean Hausdorff metric. -/
theorem signed_rank_euclidean_shape_exponential_concentration_elementary {m : ℕ}
    (hm : 1 ≤ m) (sign : Fin m → Bool) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign
        {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
          (signedEuclideanLimitShape m sign)} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ :=
    permutation_rank_euclidean_shape_exponential_concentration_elementary hm hepsilon
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

end Antichain
