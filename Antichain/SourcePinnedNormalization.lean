import Antichain.PinnedVolume

/-! The one-point pinned section has exactly the actual floor volume. -/

noncomputable section

namespace Antichain

open MeasureTheory Set
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

theorem pinnedAntichainSet_one_point (B : Set (FloorSpace ι)) :
    pinnedAntichainSet B 0 =
      (Set.univ.pi (fun _ : Fin 1 ↦ B)) ×ˢ (Set.univ : Set (Fin 0 → ℝ)) := by
  ext p
  simp only [pinnedAntichainSet, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ_pi,
    Set.mem_univ, and_true]
  constructor
  · exact And.left
  · intro hp
    refine ⟨hp, ?_⟩
    intro j k hjk
    exact False.elim (hjk (Fin.ext (by omega)))

theorem pinnedMass_one_point {B : Set (FloorSpace ι)} (_hB : MeasurableSet B) :
    pinnedMass B 0 = floorVolume B := by
  rw [pinnedMass, pinnedAntichainSet_one_point]
  change ((volume : Measure (Fin 1 → FloorSpace ι)).prod
    (volume : Measure (Fin 0 → ℝ)))
      ((Set.univ.pi (fun _ : Fin 1 ↦ B)) ×ˢ (Set.univ : Set (Fin 0 → ℝ))) = _
  rw [Measure.prod_prod]
  change (Measure.pi (fun _ : Fin 1 ↦ (volume : Measure (FloorSpace ι))))
      (Set.univ.pi (fun _ : Fin 1 ↦ B)) *
    (Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ))) Set.univ = _
  rw [Measure.pi_pi]
  simp [floorVolume]

theorem pinnedVolume_one_point {B : Set (FloorSpace ι)} (hB : MeasurableSet B) :
    pinnedVolume B 0 = (floorVolume B).toReal := by
  rw [pinnedVolume, pinnedMass_one_point hB]

/-- The literal `S_1(B)=|B|` normalization in the manuscript's convention. -/
theorem pinned_one_point_source {B : Set (FloorSpace ι)} (hB : MeasurableSet B) :
    pinnedMass B 0 = floorVolume B ∧ pinnedVolume B 0 = (floorVolume B).toReal :=
  ⟨pinnedMass_one_point hB, pinnedVolume_one_point hB⟩

end Antichain
