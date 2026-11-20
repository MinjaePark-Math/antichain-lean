import Antichain.ReferenceSimplex
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! A sample-count-independent finite net of admissible simplex boundary heights. -/

noncomputable section

namespace Antichain

open Set Metric
open scoped Topology BoundedContinuousFunction

/-- The actual directed floor cost in the reference simplex's native Euclidean space. -/
def nativeFloorCost {d : ℕ} [NeZero d] (u v : FloorSpace (Fin d)) : ℝ :=
  heightGauge (Real.sqrt (d : ℝ)) (fun i => u.val i - v.val i)

theorem nativeFloorCost_nonneg {d : ℕ} [NeZero d] (u v : FloorSpace (Fin d)) :
    0 ≤ nativeFloorCost u v := by
  apply heightGauge_nonneg
  have hu : ∑ i, u.val i = 0 := u.property
  have hv : ∑ i, v.val i = 0 := v.property
  rw [Finset.sum_sub_distrib, hu, hv, sub_self]

theorem nativeFloorCost_le_norm {d : ℕ} [NeZero d] (hd : 2 ≤ d) (u v : FloorSpace (Fin d)) :
    nativeFloorCost u v ≤ Real.sqrt ((d : ℝ) - 1) * ‖u - v‖ := by
  have hu : ∑ i, u.val i = 0 := u.property
  have hv : ∑ i, v.val i = 0 := v.property
  have hz : ∑ i, (u.val i - v.val i) = 0 := by rw [Finset.sum_sub_distrib, hu, hv, sub_self]
  have h := (heightGauge_norm_bounds_euclidean (ι := Fin d) (by simpa using hd)
    (fun i => u.val i - v.val i) hz).2
  simpa only [Fintype.card_fin, nativeFloorCost] using h

theorem norm_div_sqrt_le_nativeFloorCost {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (u v : FloorSpace (Fin d)) :
    ‖u - v‖ / Real.sqrt ((d : ℝ) - 1) ≤ nativeFloorCost u v := by
  have hu : ∑ i, u.val i = 0 := u.property
  have hv : ∑ i, v.val i = 0 := v.property
  have hz : ∑ i, (u.val i - v.val i) = 0 := by rw [Finset.sum_sub_distrib, hu, hv, sub_self]
  have h := (heightGauge_norm_bounds_euclidean (ι := Fin d) (by simpa using hd)
    (fun i => u.val i - v.val i) hz).1
  simpa only [Fintype.card_fin, nativeFloorCost] using h

abbrev SimplexBoundary (d : ℕ) := {u : FloorSpace (Fin d) // u ∈ frontier (referenceSimplex d)}

theorem simplexBoundary_compactSpace {d : ℕ} (hd : 2 ≤ d) : CompactSpace (SimplexBoundary d) := by
  have hs : frontier (referenceSimplex d) ⊆ referenceSimplex d :=
    frontier_subset_closure.trans (isClosed_referenceSimplex d).closure_subset
  exact isCompact_iff_compactSpace.mp
    ((isCompact_referenceSimplex hd).of_isClosed_subset isClosed_frontier hs)

/-- This class is defined independently of a sample size. It contains every
boundary restriction of the uniformly bounded directional extensions in Lemma 5.2. -/
def admissibleBoundaryProfiles (d : ℕ) [NeZero d] (C : ℝ) : Set (SimplexBoundary d →ᵇ ℝ) :=
  {h | (∀ u, |h u| ≤ C) ∧ ∀ u v, h u - h v ≤ nativeFloorCost u.val v.val}

theorem admissibleBoundaryProfile_lipschitz {d : ℕ} [NeZero d] (hd : 2 ≤ d) (C : ℝ)
    (h : SimplexBoundary d →ᵇ ℝ) (hh : h ∈ admissibleBoundaryProfiles d C) :
    LipschitzWith ⟨Real.sqrt ((d : ℝ) - 1), Real.sqrt_nonneg _⟩ h := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have huv := (hh.2 u v).trans (nativeFloorCost_le_norm hd u.val v.val)
  have hvu := (hh.2 v u).trans (nativeFloorCost_le_norm hd v.val u.val)
  rw [norm_sub_rev] at hvu
  change |h u - h v| ≤ Real.sqrt ((d : ℝ) - 1) * ‖u.val - v.val‖
  exact abs_le.mpr ⟨by linarith, huv⟩

/-- The actual profile class has compact closure by Arzelà--Ascoli. -/
theorem admissibleBoundaryProfiles_compact_closure {d : ℕ} [NeZero d] (hd : 2 ≤ d) (C : ℝ) :
    IsCompact (closure (admissibleBoundaryProfiles d C)) := by
  letI : CompactSpace (SimplexBoundary d) := simplexBoundary_compactSpace hd
  apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-C) C) isCompact_Icc
  · intro h u hh
    exact abs_le.mp (hh.1 u)
  · exact (LipschitzWith.uniformEquicontinuous
      (fun h : admissibleBoundaryProfiles d C => (h.val : SimplexBoundary d → ℝ))
      ⟨Real.sqrt ((d : ℝ) - 1), Real.sqrt_nonneg _⟩
      (fun h => admissibleBoundaryProfile_lipschitz hd C h.val h.property)).equicontinuous

/-- A finite uniform approximation set, with centers that themselves satisfy
the directional inequality, independent of the number of sampled points. -/
theorem finite_admissible_boundary_profile_net {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (C : ℝ) (hC : 0 ≤ C) (τ : ℝ) (hτ : 0 < τ) :
    ∃ reps : Finset (SimplexBoundary d →ᵇ ℝ), reps.Nonempty ∧
      (∀ h ∈ reps, h ∈ admissibleBoundaryProfiles d C) ∧
      (∀ h ∈ admissibleBoundaryProfiles d C, ∃ q ∈ reps, dist h q < τ) := by
  classical
  have hz : (0 : SimplexBoundary d →ᵇ ℝ) ∈ admissibleBoundaryProfiles d C := by
    refine ⟨?_, ?_⟩
    · intro u
      simpa using hC
    · intro u v
      simpa using nativeFloorCost_nonneg u.val v.val
  obtain ⟨t, hts, htfinite, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure
      (admissibleBoundaryProfiles_compact_closure hd C) hτ
  refine ⟨htfinite.toFinset, ?_, ?_, ?_⟩
  · have hzcover := hcover hz
    simp only [Set.mem_iUnion] at hzcover
    obtain ⟨q, hq, _⟩ := hzcover
    exact ⟨q, htfinite.mem_toFinset.mpr hq⟩
  · intro h hh
    exact hts (htfinite.mem_toFinset.mp hh)
  · intro h hh
    have hhcover := hcover hh
    simp only [Set.mem_iUnion] at hhcover
    obtain ⟨q, hq, hdist⟩ := hhcover
    exact ⟨q, htfinite.mem_toFinset.mpr hq, hdist⟩

end Antichain
