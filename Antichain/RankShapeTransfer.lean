import Antichain.RankCDF
import Antichain.ShapeGeometry

/-! The actual rank-midpoint point cloud has the same Euclidean Hausdorff
limit, using the proved DKW coupling and the proved antichain shape theorem. -/

noncomputable section

namespace Antichain

open Set Filter MeasureTheory Metric
open scoped Topology

def euclideanRankSampleSet (n d : ℕ) (x : CubeSample n d) : Set (EuclideanSpace ℝ (Fin d)) :=
  euclideanSampleSet n d (cubeRankCloud n d x)

/-- Pointwise coordinate displacement controls the literal Euclidean
Hausdorff distance between the two finite labelled clouds. -/
theorem finite_cloud_euclidean_hausdorff_le (n d : ℕ) (x y : CubeSample n d)
    {ε : ℝ} (hε : 0 ≤ ε) (hxy : ∀ j i, |x j i - y j i| ≤ ε) :
    hausdorffDist (euclideanSampleSet n d x) (euclideanSampleSet n d y) ≤
      Real.sqrt (d : ℝ) * ε := by
  have hpoint (j : Fin n) : dist (WithLp.toLp 2 (x j) : EuclideanSpace ℝ (Fin d))
      (WithLp.toLp 2 (y j)) ≤ Real.sqrt (d : ℝ) * ε := by
    apply (cube_euclidean_dist_le d (x j) (y j)).trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact (dist_pi_le_iff hε).mpr (fun i => by simpa only [Real.dist_eq] using hxy j i)
  apply hausdorffDist_le_of_mem_dist (mul_nonneg (Real.sqrt_nonneg _) hε)
  · rintro _ ⟨j, rfl⟩
    exact ⟨WithLp.toLp 2 (y j), ⟨j, rfl⟩, hpoint j⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨WithLp.toLp 2 (x j), ⟨j, rfl⟩, by simpa only [dist_comm] using hpoint j⟩

theorem finite_cloud_hausdorffEdist_ne_top (n d : ℕ) (hn : 0 < n)
    (x y : CubeSample n d) :
    EMetric.hausdorffEdist (euclideanSampleSet n d x) (euclideanSampleSet n d y) ≠ ⊤ := by
  apply hausdorffEdist_ne_top_of_nonempty_of_bounded
  · exact ⟨WithLp.toLp 2 (x ⟨0, hn⟩), ⟨⟨0, hn⟩, rfl⟩⟩
  · exact ⟨WithLp.toLp 2 (y ⟨0, hn⟩), ⟨⟨0, hn⟩, rfl⟩⟩
  · exact (Set.finite_range _).isBounded
  · exact (Set.finite_range _).isBounded

theorem rank_cloud_euclidean_shape_event_subset {d : ℕ} [NeZero d] (n : ℕ) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ) (S : Set (EuclideanSpace ℝ (Fin d))) :
    {x : CubeSample n d | δ < hausdorffDist (euclideanRankSampleSet n d x) S} ⊆
      rankDisplacementEvent n d (δ / (2 * Real.sqrt (d : ℝ))) ∪
        {x | δ / 2 < hausdorffDist (euclideanSampleSet n d x) S} := by
  intro x hbad
  by_contra hnot
  have hdisp : x ∉ rankDisplacementEvent n d (δ / (2 * Real.sqrt (d : ℝ))) :=
    fun hx => hnot (Or.inl hx)
  have hshape : hausdorffDist (euclideanSampleSet n d x) S ≤ δ / 2 :=
    le_of_not_gt (fun hx => hnot (Or.inr hx))
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
  have hcoord : ∀ j i, |cubeRankCloud n d x j i - x j i| ≤ δ / (2 * Real.sqrt (d : ℝ)) := by
    intro j i
    rw [abs_sub_comm]
    exact le_of_not_gt (fun hx => hdisp ⟨j, i, hx⟩)
  have hnear := finite_cloud_euclidean_hausdorff_le n d (cubeRankCloud n d x) x
    (show 0 ≤ δ / (2 * Real.sqrt (d : ℝ)) by positivity) hcoord
  have hnear' : hausdorffDist (euclideanRankSampleSet n d x) (euclideanSampleSet n d x) ≤ δ / 2 := by
    convert hnear using 1
    field_simp
  have htri : hausdorffDist (euclideanRankSampleSet n d x) S ≤
      hausdorffDist (euclideanRankSampleSet n d x) (euclideanSampleSet n d x) +
        hausdorffDist (euclideanSampleSet n d x) S :=
    hausdorffDist_triangle (finite_cloud_hausdorffEdist_ne_top n d hn (cubeRankCloud n d x) x)
  exact not_lt_of_ge (le_trans htri (by linarith)) hbad

/-- The Hausdorff conclusion of Proposition 6.1 for the actual rank-point
cloud. The only external premises are the cited alcove geometry and the
precisely stated DKW inequality. No concentration assertion is assumed. -/
theorem rank_euclidean_shape_exponential_concentration {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (DKW : DKWInput)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | δ < hausdorffDist (euclideanRankSampleSet n d x)
        (closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) ''
          normalQuantileSurface (Fin d)))} ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  let S : Set (EuclideanSpace ℝ (Fin d)) := closure
    ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) '' normalQuantileSurface (Fin d))
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
  obtain ⟨a, ha, hrank⟩ := rank_displacement_exponential_tail DKW d hd
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

end Antichain
