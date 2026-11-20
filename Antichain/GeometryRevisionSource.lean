import Antichain.DirectAlcoveInput

/-! Exact source-facing additions in the revised tiling proposition. -/

noncomputable section

namespace Antichain

open Set
open scoped Topology

variable {d : ℕ} [NeZero d]

/-- The newly explicit clause in the tiling proposition: every actual orbit
meets the closed reference alcove at exactly one point. Words represent the
actual generated maps; no uniqueness of words is asserted. -/
theorem alcove_unique_representative_source (hd : 2 ≤ d) (x : FloorSpace (Fin d)) :
    ∃! y : FloorSpace (Fin d),
      y ∈ referenceSimplex d ∧ ∃ word : List (Fin d), reflectionWordMap d word y = x := by
  have hx : x ∈ ⋃ t : AlcoveTile d, (t : Set (FloorSpace (Fin d))) := by
    rw [alcoveTile_covers_direct hd]
    exact Set.mem_univ x
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
  obtain ⟨w, hw⟩ := t.property
  change x ∈ t.val at hxt
  rw [← hw] at hxt
  obtain ⟨y, hy, hmap⟩ := hxt
  refine ⟨y, ⟨hy, w, hmap⟩, ?_⟩
  rintro z ⟨hz, v, hv⟩
  exact closed_alcove_representative_unique_direct hd v w z y hz hy (hv.trans hmap.symm)

omit [NeZero d] in
/-- The all-pairs description of the interior stated in the revised proof. -/
theorem interior_referenceSimplex_iff_pair_differences (x : FloorSpace (Fin d)) :
    x ∈ interior (referenceSimplex d) ↔
      ∀ i j : Fin d, i < j → 0 < x.val i - x.val j ∧ x.val i - x.val j < 1 := by
  rw [interior_referenceSimplex_eq_core_direct]
  constructor
  · intro hx i j hij
    exact ⟨sub_pos.mpr (hx.1 i j hij), hx.2 i j⟩
  · intro hx
    refine ⟨fun i j hij => sub_pos.mp (hx i j hij).1, fun i j => ?_⟩
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hx i j hij).2
    · simp
    · have h := (hx j i hji).1
      linarith

end Antichain
