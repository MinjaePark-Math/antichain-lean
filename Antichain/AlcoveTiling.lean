import Antichain.TileSymmetries
import Mathlib.Data.Set.Countable
import Mathlib.Topology.LocallyFinite
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.AEDisjoint

/-!
Actual distinct reflected alcoves, with duplicate reflection words collapsed.
`HumphreysAlcoveInput` is an explicit external cited input, never an axiom or
default instance. It records only the cited Coxeter-group geometric theorems.
The elementary Euclidean, convexity, measure and diameter facts are proved here.

Source references are the manuscript's Humphreys, Reflection Groups and Coxeter
Groups (1990), Proposition 4.3, Theorem 4.5(c), and Theorem 4.8. The exact theorem
pages have not been independently checked in an openly accessible copy.
-/

noncomputable section

namespace Antichain

open Set MeasureTheory
open scoped Pointwise ENNReal

variable (d : ℕ) [NeZero d]

/-- Distinct actual tile sets; repeated words do not create repeated tiles. -/
def AlcoveTile := {B : Set (FloorSpace (Fin d)) // ∃ word : List (Fin d), reflectionTile d word = B}

instance : SetLike (AlcoveTile d) (FloorSpace (Fin d)) where
  coe t := t.val
  coe_injective' := Subtype.val_injective

def wordAlcove (word : List (Fin d)) : AlcoveTile d := ⟨reflectionTile d word, word, rfl⟩

theorem wordAlcove_surjective : Function.Surjective (wordAlcove d) := by
  rintro ⟨B, word, hword⟩
  exact ⟨word, Subtype.ext hword⟩

instance alcoveTile_countable : Countable (AlcoveTile d) :=
  (wordAlcove_surjective d).countable

instance alcoveTile_encodable : Encodable (AlcoveTile d) := Encodable.ofCountable _

theorem reflectionWordMap_isometry (word : List (Fin d)) : Isometry (reflectionWordMap d word) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [reflectionWordMap_eq_affine, reflectionWordMap_eq_affine, dist_add_left]
  exact (floorPermutation (wordPermutation d word)).isometry.dist_eq x y

theorem reflectionWordMap_surjective (word : List (Fin d)) :
    Function.Surjective (reflectionWordMap d word) := by
  intro y
  refine ⟨(floorPermutation (wordPermutation d word)).symm (y - wordTranslation d word), ?_⟩
  rw [reflectionWordMap_eq_affine]
  simp

/-- Every actual tile is literally a translation of a coordinate-permuted Δ. -/
theorem alcoveTile_eq_affine (t : AlcoveTile d) :
    ∃ a : FloorSpace (Fin d), ∃ e : Fin d ≃ Fin d,
      (t : Set (FloorSpace (Fin d))) = (fun x ↦ a + floorPermutation e x) '' referenceSimplex d := by
  obtain ⟨word, hword⟩ := t.property
  exact ⟨wordTranslation d word, wordPermutation d word, hword.symm.trans (reflectionTile_eq_affine d word)⟩

theorem isCompact_alcoveTile (hd : 2 ≤ d) (t : AlcoveTile d) :
    IsCompact (t : Set (FloorSpace (Fin d))) := by
  obtain ⟨word, hword⟩ := t.property
  change IsCompact t.val
  rw [← hword, reflectionTile]
  exact (isCompact_referenceSimplex hd).image (reflectionWordMap_isometry d word).continuous

theorem isClosed_alcoveTile (hd : 2 ≤ d) (t : AlcoveTile d) :
    IsClosed (t : Set (FloorSpace (Fin d))) := (isCompact_alcoveTile d hd t).isClosed

theorem measurableSet_alcoveTile (hd : 2 ≤ d) (t : AlcoveTile d) :
    MeasurableSet (t : Set (FloorSpace (Fin d))) := (isClosed_alcoveTile d hd t).measurableSet

theorem alcoveTile_nonempty (hd : 2 ≤ d) (t : AlcoveTile d) :
    (t : Set (FloorSpace (Fin d))).Nonempty := by
  obtain ⟨word, hword⟩ := t.property
  change t.val.Nonempty
  rw [← hword, reflectionTile]
  exact (referenceSimplex_interior_nonempty hd).mono interior_subset |>.image _

omit [NeZero d] in
theorem alcove_referenceSimplex_convex : Convex ℝ (referenceSimplex d) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i j hij
    change a * x.val j + b * y.val j ≤ a * x.val i + b * y.val i
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.1 hij) ha)
      (mul_le_mul_of_nonneg_left (hy.1 hij) hb)
  · intro i j
    change a * x.val i + b * y.val i - (a * x.val j + b * y.val j) ≤ 1
    have hx' := mul_le_mul_of_nonneg_left (hx.2 i j) ha
    have hy' := mul_le_mul_of_nonneg_left (hy.2 i j) hb
    nlinarith

theorem convex_alcoveTile (t : AlcoveTile d) : Convex ℝ (t : Set (FloorSpace (Fin d))) := by
  obtain ⟨a, e, heq⟩ := alcoveTile_eq_affine d t
  rw [heq, ← Set.image_image]
  exact ((alcove_referenceSimplex_convex d).linear_image (floorPermutation e).toLinearMap).translate a

theorem volume_frontier_alcoveTile (t : AlcoveTile d) :
    (volume : Measure (FloorSpace (Fin d))) (frontier (t : Set (FloorSpace (Fin d)))) = 0 :=
  (convex_alcoveTile d t).addHaar_frontier volume

/-- Equal canonical Euclidean volumes, independently of the external tiling theorem. -/
theorem volume_alcoveTile (hd : 2 ≤ d) (t : AlcoveTile d) :
    (volume : Measure (FloorSpace (Fin d))) (t : Set (FloorSpace (Fin d))) =
      floorVolume (referenceSimplex d) := by
  obtain ⟨a, e, heq⟩ := alcoveTile_eq_affine d t
  have hmp : MeasurePreserving (fun x : FloorSpace (Fin d) ↦ a + floorPermutation e x) volume volume :=
    (measurePreserving_add_left volume a).comp (floorPermutation e).measurePreserving
  have hinj : Function.Injective (fun x : FloorSpace (Fin d) ↦ a + floorPermutation e x) :=
    fun _ _ h ↦ (floorPermutation e).injective (add_left_cancel h)
  have h := hmp.measure_preimage (measurableSet_alcoveTile d hd t).nullMeasurableSet
  rw [heq, Set.preimage_image_eq _ hinj] at h
  simpa only [heq, floorVolume] using h.symm

theorem alcoveTile_dist_le (hd : 2 ≤ d) (t : AlcoveTile d)
    {x y : FloorSpace (Fin d)} (hx : x ∈ t) (hy : y ∈ t) : dist x y ≤ 2 * (d : ℝ) := by
  obtain ⟨word, hword⟩ := t.property
  change x ∈ t.val at hx
  change y ∈ t.val at hy
  rw [← hword] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [(reflectionWordMap_isometry d word).dist_eq, dist_eq_norm]
  exact (norm_sub_le u v).trans (by
    linarith [norm_le_dimension_of_mem_referenceSimplex hd hu,
      norm_le_dimension_of_mem_referenceSimplex hd hv])

/-- Only the externally cited Coxeter-alcove facts. These visible fields supply
no tile-volume, Gaussian, counting, gluing or asymptotic conclusion. -/
structure HumphreysAlcoveInput : Prop where
  covers : (⋃ t : AlcoveTile d, (t : Set (FloorSpace (Fin d)))) = Set.univ
  disjoint_interiors : Pairwise (fun t u : AlcoveTile d ↦
    Disjoint (interior (t : Set (FloorSpace (Fin d)))) (interior (u : Set (FloorSpace (Fin d)))))
  locally_finite : LocallyFinite (fun t : AlcoveTile d ↦ (t : Set (FloorSpace (Fin d))))
  same_tile_map_unique : ∀ w v : List (Fin d), reflectionTile d w = reflectionTile d v →
    reflectionWordMap d w = reflectionWordMap d v
  closed_alcove_orbit_representative_unique : ∀ (w v : List (Fin d)) (x y : FloorSpace (Fin d)),
    x ∈ referenceSimplex d → y ∈ referenceSimplex d →
      reflectionWordMap d w x = reflectionWordMap d v y → x = y

theorem alcoveTile_aedisjoint (h : HumphreysAlcoveInput d) :
    Pairwise (fun t u : AlcoveTile d ↦ AEDisjoint (volume : Measure (FloorSpace (Fin d)))
      (t : Set (FloorSpace (Fin d))) (u : Set (FloorSpace (Fin d)))) := by
  intro t u htu
  exact ((h.disjoint_interiors htu).aedisjoint).congr
    (interior_ae_eq_of_null_frontier (volume_frontier_alcoveTile d t)).symm
    (interior_ae_eq_of_null_frontier (volume_frontier_alcoveTile d u)).symm

def scaledAlcove (ε : ℝ) (t : AlcoveTile d) : Set (FloorSpace (Fin d)) :=
  ε • (t : Set (FloorSpace (Fin d)))

theorem isCompact_scaledAlcove (hd : 2 ≤ d) (ε : ℝ) (t : AlcoveTile d) :
    IsCompact (scaledAlcove d ε t) := by
  change IsCompact ((fun x : FloorSpace (Fin d) ↦ ε • x) '' (t : Set (FloorSpace (Fin d))))
  exact (isCompact_alcoveTile d hd t).image (continuous_const.smul continuous_id)

theorem measurableSet_scaledAlcove (hd : 2 ≤ d) (ε : ℝ) (t : AlcoveTile d) :
    MeasurableSet (scaledAlcove d ε t) := (isCompact_scaledAlcove d hd ε t).measurableSet

theorem scaledAlcove_nonempty (hd : 2 ≤ d) (ε : ℝ) (t : AlcoveTile d) :
    (scaledAlcove d ε t).Nonempty := (alcoveTile_nonempty d hd t).image (fun x ↦ ε • x)

theorem volume_scaledAlcove (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (t : AlcoveTile d) :
    (volume : Measure (FloorSpace (Fin d))) (scaledAlcove d ε t) =
      ENNReal.ofReal ε ^ (d - 1) * floorVolume (referenceSimplex d) := by
  rw [scaledAlcove, Measure.addHaar_smul_of_nonneg volume hε.le,
    finrank_floorSpace, Fintype.card_fin, volume_alcoveTile d hd t,
    ENNReal.ofReal_pow hε.le]

theorem scaledAlcove_dist_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (t : AlcoveTile d)
    {x y : FloorSpace (Fin d)} (hx : x ∈ scaledAlcove d ε t) (hy : y ∈ scaledAlcove d ε t) :
    dist x y ≤ ε * (2 * (d : ℝ)) := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left (alcoveTile_dist_le d hd t hu hv) hε.le

theorem scaledAlcove_covers (h : HumphreysAlcoveInput d) {ε : ℝ} (hε : 0 < ε) :
    (⋃ t : AlcoveTile d, scaledAlcove d ε t) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : ε⁻¹ • x ∈ ⋃ t : AlcoveTile d, (t : Set (FloorSpace (Fin d))) := by
    rw [h.covers]
    exact Set.mem_univ _
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨t, ε⁻¹ • x, ht, by simp [hε.ne']⟩

theorem scaledAlcove_aedisjoint (h : HumphreysAlcoveInput d) {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun t u : AlcoveTile d ↦ AEDisjoint (volume : Measure (FloorSpace (Fin d)))
      (scaledAlcove d ε t) (scaledAlcove d ε u)) := by
  intro t u htu
  change volume ((ε • (t : Set (FloorSpace (Fin d)))) ∩ (ε • (u : Set (FloorSpace (Fin d))))) = 0
  rw [← Set.smul_set_inter₀ hε.ne', Measure.addHaar_smul_of_nonneg volume hε.le,
    (alcoveTile_aedisjoint d h htu).eq, mul_zero]

theorem convex_scaledAlcove (ε : ℝ) (t : AlcoveTile d) : Convex ℝ (scaledAlcove d ε t) :=
  (convex_alcoveTile d t).smul ε

theorem volume_frontier_scaledAlcove (ε : ℝ) (t : AlcoveTile d) :
    (volume : Measure (FloorSpace (Fin d))) (frontier (scaledAlcove d ε t)) = 0 :=
  (convex_scaledAlcove d ε t).addHaar_frontier volume

/-- The actual affine reflection-word map as a homeomorphism, with an explicit
inverse inherited from its coordinate permutation and translation. -/
def reflectionWordHomeomorph (word : List (Fin d)) : FloorSpace (Fin d) ≃ₜ FloorSpace (Fin d) :=
  (floorPermutation (wordPermutation d word)).toHomeomorph.trans
    (Homeomorph.addLeft (wordTranslation d word))

theorem reflectionWordHomeomorph_apply (word : List (Fin d)) (x : FloorSpace (Fin d)) :
    reflectionWordHomeomorph d word x = reflectionWordMap d word x := by
  rw [reflectionWordMap_eq_affine]
  rfl

theorem scaledAlcove_locallyFinite (h : HumphreysAlcoveInput d) {ε : ℝ} (hε : 0 < ε) :
    LocallyFinite (scaledAlcove d ε) := by
  have hf := h.locally_finite.preimage_continuous
    (g := fun x : FloorSpace (Fin d) ↦ ε⁻¹ • x) (continuous_const.smul continuous_id)
  convert hf using 1
  funext t
  ext x
  exact Set.mem_smul_set_iff_inv_smul_mem₀ hε.ne' _ _

theorem scaledAlcove_disjoint_interiors (h : HumphreysAlcoveInput d) {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun t u : AlcoveTile d ↦ Disjoint (interior (scaledAlcove d ε t))
      (interior (scaledAlcove d ε u))) := by
  intro t u htu
  simp only [scaledAlcove, interior_smul₀ hε.ne']
  apply Set.disjoint_left.mpr
  intro x hx hu
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hε.ne'] at hx hu
  exact Set.disjoint_left.mp (h.disjoint_interiors htu) hx hu

/-- Assign each common boundary to the containing tile with least encoded index.
This is a measurable genuine partition; it does not discard boundary points. -/
def alcoveCell (ε : ℝ) (t : AlcoveTile d) : Set (FloorSpace (Fin d)) :=
  scaledAlcove d ε t \ ⋃ s : {u : AlcoveTile d // Encodable.encode u < Encodable.encode t},
    scaledAlcove d ε s.val

theorem alcoveCell_subset (ε : ℝ) (t : AlcoveTile d) : alcoveCell d ε t ⊆ scaledAlcove d ε t :=
  Set.diff_subset

theorem measurableSet_alcoveCell (hd : 2 ≤ d) (ε : ℝ) (t : AlcoveTile d) :
    MeasurableSet (alcoveCell d ε t) :=
  (measurableSet_scaledAlcove d hd ε t).diff
    (MeasurableSet.iUnion (fun s ↦ measurableSet_scaledAlcove d hd ε s.val))

theorem alcoveCell_pairwise_disjoint (ε : ℝ) :
    Pairwise (fun t u : AlcoveTile d ↦ Disjoint (alcoveCell d ε t) (alcoveCell d ε u)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  rintro x ⟨ht, hnot⟩ ⟨hu, hnot'⟩
  have hcode : Encodable.encode t ≠ Encodable.encode u :=
    fun heq ↦ htu (Encodable.encode_injective heq)
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · exact hnot' (Set.mem_iUnion.mpr ⟨⟨t, hlt⟩, ht⟩)
  · exact hnot (Set.mem_iUnion.mpr ⟨⟨u, hgt⟩, hu⟩)

theorem alcoveCell_covers (h : HumphreysAlcoveInput d) {ε : ℝ} (hε : 0 < ε) :
    (⋃ t : AlcoveTile d, alcoveCell d ε t) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ t : AlcoveTile d, scaledAlcove d ε t := by
    rw [scaledAlcove_covers d h hε]
    exact Set.mem_univ x
  obtain ⟨t₀, ht₀⟩ := Set.mem_iUnion.mp hx
  have hex : ∃ n : ℕ, ∃ t : AlcoveTile d, Encodable.encode t = n ∧ x ∈ scaledAlcove d ε t :=
    ⟨Encodable.encode t₀, t₀, rfl, ht₀⟩
  obtain ⟨t, htcode, ht⟩ := Nat.find_spec hex
  apply Set.mem_iUnion.mpr
  refine ⟨t, ht, ?_⟩
  intro hprev
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hprev
  have hmin := Nat.find_min' hex (show ∃ u : AlcoveTile d,
      Encodable.encode u = Encodable.encode s.val ∧ x ∈ scaledAlcove d ε u from ⟨s.val, rfl, hs⟩)
  have hlt := s.property
  omega

theorem volume_alcoveCell (hd : 2 ≤ d) (h : HumphreysAlcoveInput d) {ε : ℝ}
    (hε : 0 < ε) (t : AlcoveTile d) :
    (volume : Measure (FloorSpace (Fin d))) (alcoveCell d ε t) =
      ENNReal.ofReal ε ^ (d - 1) * floorVolume (referenceSimplex d) := by
  have had : AEDisjoint (volume : Measure (FloorSpace (Fin d))) (scaledAlcove d ε t)
      (⋃ s : {u : AlcoveTile d // Encodable.encode u < Encodable.encode t}, scaledAlcove d ε s.val) := by
    apply AEDisjoint.iUnion_right_iff.mpr
    intro s
    apply scaledAlcove_aedisjoint d h hε
    intro heq
    have hlt := s.property
    have hc := congrArg Encodable.encode heq
    omega
  exact had.measure_diff_left.trans (volume_scaledAlcove d hd hε t)

end Antichain
