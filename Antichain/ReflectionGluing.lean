import Antichain.SegmentSubdivision
import Antichain.AlcoveTiling
import Antichain.BoundaryMatching
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Actual directional gluing across the cited locally finite closed alcove cover.
No gluing conclusion is included among the external Coxeter inputs. -/

noncomputable section

namespace Antichain

open Set Filter Metric
open scoped Topology Pointwise

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem nearby_share_closed_cover_member {I : Type*}
    (B : I → Set (FloorSpace (Fin d))) (hcover : ⋃ i, B i = univ)
    (hclosed : ∀ i, IsClosed (B i)) (hlocal : LocallyFinite B) (x : FloorSpace (Fin d)) :
    ∀ᶠ y in 𝓝 x, ∃ i, x ∈ B i ∧ y ∈ B i := by
  filter_upwards [hlocal.iInter_compl_mem_nhds hclosed x] with y hy
  have hycover : y ∈ ⋃ i, B i := hcover.symm ▸ mem_univ y
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hycover
  refine ⟨i, ?_, hi⟩
  by_contra hx
  exact (Set.mem_iInter₂.mp hy i hx) hi

/-- Local directional inequalities on an actual locally finite closed cover
globalize along every straight segment. This is proved by continuous interval
induction, using positive homogeneity of the exact directed cost. -/
theorem global_directional_of_closed_locallyFinite_cover {I : Type*} (hd : 2 ≤ d)
    (B : I → Set (FloorSpace (Fin d))) (hcover : ⋃ i, B i = univ)
    (hclosed : ∀ i, IsClosed (B i)) (hlocal : LocallyFinite B)
    (H : FloorSpace (Fin d) → ℝ)
    (hH : ∀ i, ∀ x ∈ B i, ∀ y ∈ B i, H x - H y ≤ nativeFloorCost x y) :
    ∀ u v, H u - H v ≤ nativeFloorCost u v := by
  have hnear : ∀ x, ∀ᶠ y in 𝓝 x,
      H x - H y ≤ nativeFloorCost x y ∧ H y - H x ≤ nativeFloorCost y x := by
    intro x
    filter_upwards [nearby_share_closed_cover_member B hcover hclosed hlocal x] with y hy
    obtain ⟨i, hxi, hyi⟩ := hy
    exact ⟨hH i x hxi y hyi, hH i y hyi x hxi⟩
  have hcont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hbound : ∀ᶠ y in 𝓝 x,
        dist (H y) (H x) ≤ Real.sqrt ((d : ℝ) - 1) * dist y x := by
      filter_upwards [hnear x] with y hy
      have hxy := hy.1.trans (nativeFloorCost_le_norm hd x y)
      have hyx := hy.2.trans (nativeFloorCost_le_norm hd y x)
      rw [norm_sub_rev] at hxy
      change |H y - H x| ≤ Real.sqrt ((d : ℝ) - 1) * ‖y - x‖
      exact abs_le.mpr ⟨by linarith, hyx⟩
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) hbound
    simpa using ((continuous_const.mul (continuous_id.dist continuous_const)).tendsto x :
      Tendsto (fun y : FloorSpace (Fin d) => Real.sqrt ((d : ℝ) - 1) * dist y x)
        (𝓝 x) (𝓝 (Real.sqrt ((d : ℝ) - 1) * dist x x)))
  intro u v
  let k := nativeFloorCost u v
  let g : ℝ → ℝ := fun t => H (floorSegment u v t) + k * t
  have hg : Continuous g := (hcont.comp (floorSegment_continuous u v)).add
    (continuous_const.mul continuous_id)
  let S : Set ℝ := {t | g 0 ≤ g t}
  have hS : IsClosed (S ∩ Set.Icc 0 1) :=
    (isClosed_le continuous_const hg).inter isClosed_Icc
  have hzero : (0 : ℝ) ∈ S := by change g 0 ≤ g 0; exact le_rfl
  have hone : (1 : ℝ) ∈ S := hS.mem_of_ge_of_forall_exists_gt hzero zero_le_one (by
    intro t ht
    have hevent : ∀ᶠ s in 𝓝[>] t,
        (H (floorSegment u v t) - H (floorSegment u v s) ≤
          nativeFloorCost (floorSegment u v t) (floorSegment u v s)) ∧ s < 1 := by
      have hlocal_t : ∀ᶠ s in 𝓝 t,
          H (floorSegment u v t) - H (floorSegment u v s) ≤
            nativeFloorCost (floorSegment u v t) (floorSegment u v s) := by
        filter_upwards [(floorSegment_continuous u v).continuousAt.eventually
          (hnear (floorSegment u v t))] with s hs
        exact hs.1
      exact (hlocal_t.and (eventually_lt_nhds ht.2.2)).filter_mono nhdsWithin_le_nhds
    obtain ⟨s, hs, hts⟩ := (hevent.and self_mem_nhdsWithin).exists
    have hcost := floorSegment_directed_cost u v t s hts.le
    have hgs : g t ≤ g s := by
      dsimp [g]
      rw [hcost] at hs
      dsimp [k]
      linarith [hs.1]
    exact ⟨s, ht.1.trans hgs, hts, hs.2.le⟩)
  change H (floorSegment u v 0) + k * 0 ≤ H (floorSegment u v 1) + k * 1 at hone
  simp only [floorSegment, sub_zero, one_smul, zero_smul, add_zero, sub_self,
    zero_add, mul_zero, mul_one] at hone
  dsimp [k] at hone
  linarith

def alcoveWord (t : AlcoveTile d) : List (Fin d) := Classical.choose t.property

theorem alcoveWord_spec (t : AlcoveTile d) :
    reflectionTile d (alcoveWord t) = (t : Set (FloorSpace (Fin d))) := Classical.choose_spec t.property

def alcoveChart (t : AlcoveTile d) : FloorSpace (Fin d) ≃ₜ FloorSpace (Fin d) :=
  reflectionWordHomeomorph d (alcoveWord t)

theorem alcoveChart_apply (t : AlcoveTile d) (x : FloorSpace (Fin d)) :
    alcoveChart t x = reflectionWordMap d (alcoveWord t) x :=
  reflectionWordHomeomorph_apply d (alcoveWord t) x

theorem alcoveChart_image_reference (t : AlcoveTile d) :
    alcoveChart t '' referenceSimplex d = (t : Set (FloorSpace (Fin d))) := by
  have hmap : (alcoveChart t : FloorSpace (Fin d) → FloorSpace (Fin d)) =
      reflectionWordMap d (alcoveWord t) := funext (alcoveChart_apply t)
  rw [hmap]
  exact alcoveWord_spec t

theorem alcoveChart_symm_mem_reference {t : AlcoveTile d} {x : FloorSpace (Fin d)} (hx : x ∈ t) :
    (alcoveChart t).symm x ∈ referenceSimplex d := by
  change x ∈ (t : Set (FloorSpace (Fin d))) at hx
  rw [← alcoveChart_image_reference t] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  simpa using ha

theorem nativeFloorCost_reflectionWord (w : List (Fin d)) (u v : FloorSpace (Fin d)) :
    nativeFloorCost (reflectionWordMap d w u) (reflectionWordMap d w v) = nativeFloorCost u v := by
  have heq : (fun i => (reflectionWordMap d w u).val i - (reflectionWordMap d w v).val i) =
      (fun i => u.val (wordPermutation d w i) - v.val (wordPermutation d w i)) := by
    funext i
    simp only [reflectionWordMap_eq_affine, Submodule.coe_add, PiLp.add_apply,
      floorPermutation_apply]
    ring
  unfold nativeFloorCost
  rw [heq]
  exact heightGauge_equiv _ (fun i => u.val i - v.val i) (wordPermutation d w)

theorem nativeFloorCost_alcoveChart_symm (t : AlcoveTile d) (x y : FloorSpace (Fin d)) :
    nativeFloorCost ((alcoveChart t).symm x) ((alcoveChart t).symm y) = nativeFloorCost x y := by
  have h := nativeFloorCost_reflectionWord (alcoveWord t) ((alcoveChart t).symm x) ((alcoveChart t).symm y)
  rw [← alcoveChart_apply, ← alcoveChart_apply] at h
  simpa using h.symm

/-- The cited unique closed-alcove representative gives identical base preimages
at every actual tile overlap. -/
theorem overlapping_alcove_preimages_eq (h : HumphreysAlcoveInput d)
    (t u : AlcoveTile d) {x : FloorSpace (Fin d)} (ht : x ∈ t) (hu : x ∈ u) :
    (alcoveChart t).symm x = (alcoveChart u).symm x := by
  apply h.closed_alcove_orbit_representative_unique (alcoveWord t) (alcoveWord u)
    ((alcoveChart t).symm x) ((alcoveChart u).symm x)
    (alcoveChart_symm_mem_reference ht) (alcoveChart_symm_mem_reference hu)
  rw [← alcoveChart_apply, ← alcoveChart_apply]
  simp

/-- At a meeting of distinct tiles the common preimage is on the actual
reference boundary; an interior preimage would belong to both tile interiors. -/
theorem overlapping_alcove_preimage_mem_frontier (h : HumphreysAlcoveInput d)
    (t u : AlcoveTile d) (htu : t ≠ u) {x : FloorSpace (Fin d)} (ht : x ∈ t) (hu : x ∈ u) :
    (alcoveChart t).symm x ∈ frontier (referenceSimplex d) := by
  refine ⟨subset_closure (alcoveChart_symm_mem_reference ht), ?_⟩
  intro hint
  have hpre := overlapping_alcove_preimages_eq h t u ht hu
  have hxt : x ∈ interior (t : Set (FloorSpace (Fin d))) := by
    rw [← alcoveChart_image_reference t, ← (alcoveChart t).image_interior]
    exact ⟨(alcoveChart t).symm x, hint, (alcoveChart t).apply_symm_apply x⟩
  have hxu : x ∈ interior (u : Set (FloorSpace (Fin d))) := by
    rw [← alcoveChart_image_reference u, ← (alcoveChart u).image_interior]
    exact ⟨(alcoveChart u).symm x, hpre ▸ hint, (alcoveChart u).apply_symm_apply x⟩
  exact Set.disjoint_left.mp (h.disjoint_interiors htu) hxt hxu

theorem transported_extensions_agree_on_overlap (h : HumphreysAlcoveInput d)
    (F : AlcoveTile d → FloorSpace (Fin d) → ℝ) (boundary : SimplexBoundary d → ℝ)
    (hboundary : ∀ t a (ha : a ∈ frontier (referenceSimplex d)), F t a = boundary ⟨a, ha⟩)
    (t u : AlcoveTile d) {x : FloorSpace (Fin d)} (ht : x ∈ t) (hu : x ∈ u) :
    F t ((alcoveChart t).symm x) = F u ((alcoveChart u).symm x) := by
  by_cases htu : t = u
  · subst u
    rfl
  have ha := overlapping_alcove_preimage_mem_frontier h t u htu ht hu
  have heq := overlapping_alcove_preimages_eq h t u ht hu
  have hb : (alcoveChart u).symm x ∈ frontier (referenceSimplex d) := heq ▸ ha
  rw [hboundary t _ ha, hboundary u _ hb]
  congr 1
  exact Subtype.ext heq

def coveringAlcove (h : HumphreysAlcoveInput d) (x : FloorSpace (Fin d)) : AlcoveTile d :=
  Classical.choose (show ∃ t : AlcoveTile d, x ∈ t from
    Set.mem_iUnion.mp (h.covers.symm ▸ Set.mem_univ x))

theorem coveringAlcove_mem (h : HumphreysAlcoveInput d) (x : FloorSpace (Fin d)) :
    x ∈ coveringAlcove h x := by
  unfold coveringAlcove
  exact Classical.choose_spec (show ∃ t : AlcoveTile d, x ∈ t from
    Set.mem_iUnion.mp (h.covers.symm ▸ Set.mem_univ x))

def gluedAlcoveHeight (h : HumphreysAlcoveInput d)
    (F : AlcoveTile d → FloorSpace (Fin d) → ℝ) (x : FloorSpace (Fin d)) : ℝ :=
  F (coveringAlcove h x) ((alcoveChart (coveringAlcove h x)).symm x)

theorem gluedAlcoveHeight_eq_transport (h : HumphreysAlcoveInput d)
    (F : AlcoveTile d → FloorSpace (Fin d) → ℝ) (boundary : SimplexBoundary d → ℝ)
    (hboundary : ∀ t a (ha : a ∈ frontier (referenceSimplex d)), F t a = boundary ⟨a, ha⟩)
    (t : AlcoveTile d) {x : FloorSpace (Fin d)} (hx : x ∈ t) :
    gluedAlcoveHeight h F x = F t ((alcoveChart t).symm x) :=
  transported_extensions_agree_on_overlap h F boundary hboundary _ t (coveringAlcove_mem h x) hx

/-- The actual transported extensions glue to a global directional height
function. Only the explicitly cited alcove geometry enters as an external input. -/
theorem gluedAlcoveHeight_directional (hd : 2 ≤ d) (h : HumphreysAlcoveInput d)
    (F : AlcoveTile d → FloorSpace (Fin d) → ℝ) (boundary : SimplexBoundary d → ℝ)
    (hboundary : ∀ t a (ha : a ∈ frontier (referenceSimplex d)), F t a = boundary ⟨a, ha⟩)
    (hF : ∀ t, ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
      F t a - F t b ≤ nativeFloorCost a b) :
    ∀ x y, gluedAlcoveHeight h F x - gluedAlcoveHeight h F y ≤ nativeFloorCost x y := by
  apply global_directional_of_finite_segment_subdivision
    (fun t : AlcoveTile d => (t : Set (FloorSpace (Fin d)))) h.covers
    (isClosed_alcoveTile d hd) (convex_alcoveTile d) h.locally_finite
  intro t x hx y hy
  rw [gluedAlcoveHeight_eq_transport h F boundary hboundary t hx,
    gluedAlcoveHeight_eq_transport h F boundary hboundary t hy]
  exact (hF t _ (alcoveChart_symm_mem_reference hx) _ (alcoveChart_symm_mem_reference hy)).trans_eq
    (nativeFloorCost_alcoveChart_symm t x y)

theorem nativeFloorCost_smul (a : ℝ) (ha : 0 ≤ a) (u v : FloorSpace (Fin d)) :
    nativeFloorCost (a • u) (a • v) = a * nativeFloorCost u v := by
  have heq : (fun i => (a • u).val i - (a • v).val i) =
      (fun i => a * (u.val i - v.val i)) := by
    funext i
    simp only [Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul]
    ring
  unfold nativeFloorCost
  rw [heq]
  exact heightGauge_smul _ a ha _

def scaledGluedAlcoveHeight (ε : ℝ) (h : HumphreysAlcoveInput d)
    (F : AlcoveTile d → FloorSpace (Fin d) → ℝ) (x : FloorSpace (Fin d)) : ℝ :=
  ε * gluedAlcoveHeight h F (ε⁻¹ • x)

theorem scaledGluedAlcoveHeight_directional (hd : 2 ≤ d) (h : HumphreysAlcoveInput d)
    (ε : ℝ) (hε : 0 < ε) (F : AlcoveTile d → FloorSpace (Fin d) → ℝ)
    (boundary : SimplexBoundary d → ℝ)
    (hboundary : ∀ t a (ha : a ∈ frontier (referenceSimplex d)), F t a = boundary ⟨a, ha⟩)
    (hF : ∀ t, ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
      F t a - F t b ≤ nativeFloorCost a b) :
    ∀ x y, scaledGluedAlcoveHeight ε h F x - scaledGluedAlcoveHeight ε h F y ≤
      nativeFloorCost x y := by
  intro x y
  have hg := mul_le_mul_of_nonneg_left
    (gluedAlcoveHeight_directional hd h F boundary hboundary hF (ε⁻¹ • x) (ε⁻¹ • y)) hε.le
  rw [nativeFloorCost_smul _ (inv_nonneg.mpr hε.le), ← mul_assoc,
    mul_inv_cancel₀ hε.ne', one_mul] at hg
  simpa only [scaledGluedAlcoveHeight, mul_sub] using hg

theorem scaledGluedAlcoveHeight_eq_transport (h : HumphreysAlcoveInput d)
    (ε : ℝ) (hε : ε ≠ 0) (F : AlcoveTile d → FloorSpace (Fin d) → ℝ)
    (boundary : SimplexBoundary d → ℝ)
    (hboundary : ∀ t a (ha : a ∈ frontier (referenceSimplex d)), F t a = boundary ⟨a, ha⟩)
    (t : AlcoveTile d) {a : FloorSpace (Fin d)} (ha : a ∈ referenceSimplex d) :
    scaledGluedAlcoveHeight ε h F (ε • alcoveChart t a) = ε * F t a := by
  unfold scaledGluedAlcoveHeight
  rw [inv_smul_smul₀ hε]
  rw [gluedAlcoveHeight_eq_transport h F boundary hboundary t
    (by
      change alcoveChart t a ∈ (t : Set (FloorSpace (Fin d)))
      rw [← alcoveChart_image_reference]
      exact ⟨a, ha, rfl⟩)]
  simp

/-- The literal independent copies in the selected scaled alcoves, with the
assignment of labels and within-tile positions kept explicit. -/
def replicatedConfiguration (m q N : ℕ) (ε : ℝ) (tiles : Fin q → AlcoveTile d)
    (p : Fin q → FloorHeightConfiguration m d) (e : Fin N → Fin q × Fin m) :
    FloorHeightConfiguration N d :=
  (fun j => ε • alcoveChart (tiles (e j).1) ((p (e j).1).1 (e j).2),
    fun j => ε * (p (e j).1).2 (e j).2)

/-- Independent configurations with a common boundary profile remain an
antichain after transport to any distinct collection of actual scaled alcoves.
The global extension is constructed from the cited geometry and the proved
directional gluing theorem. -/
theorem replicatedConfiguration_admissible (hd : 2 ≤ d) (h : HumphreysAlcoveInput d)
    (m q N : ℕ) [NeZero q] (ε : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    (p : Fin q → FloorHeightConfiguration m d) (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ i j, (p i).1 j ∈ referenceSimplex d)
    (hext : ∀ i, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E ((p i).1 j) = (p i).2 j) ∧
      (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b))
    (e : Fin N → Fin q × Fin m) :
    replicatedConfiguration m q N ε tiles p e ∈ flooredAntichainEvent N d ∧
      ∃ E : FloorSpace (Fin d) → ℝ,
        (∀ j, E ((replicatedConfiguration m q N ε tiles p e).1 j) =
          (replicatedConfiguration m q N ε tiles p e).2 j) ∧
        (∀ a b, E a - E b ≤ nativeFloorCost a b) := by
  classical
  choose E hE using hext
  let index : AlcoveTile d → Fin q := fun t =>
    if hi : ∃ i, tiles i = t then Classical.choose hi else 0
  have hindex (i : Fin q) : index (tiles i) = i := by
    dsimp [index]
    rw [dif_pos ⟨i, rfl⟩]
    exact htiles (Classical.choose_spec (show ∃ j, tiles j = tiles i from ⟨i, rfl⟩))
  let F : AlcoveTile d → FloorSpace (Fin d) → ℝ := fun t => E (index t)
  have hb : ∀ t a (ha : a ∈ frontier (referenceSimplex d)), F t a = boundary ⟨a, ha⟩ := by
    intro t a ha
    exact (hE (index t)).2.1 ⟨a, ha⟩
  have hdir : ∀ t, ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
      F t a - F t b ≤ nativeFloorCost a b := by
    intro t a _ b _
    exact (hE (index t)).2.2 a b
  let G := scaledGluedAlcoveHeight ε h F
  have hG : ∀ a b, G a - G b ≤ nativeFloorCost a b :=
    scaledGluedAlcoveHeight_directional hd h ε hε F boundary hb hdir
  have hagree (j : Fin N) : G ((replicatedConfiguration m q N ε tiles p e).1 j) =
      (replicatedConfiguration m q N ε tiles p e).2 j := by
    change scaledGluedAlcoveHeight ε h F
      (ε • alcoveChart (tiles (e j).1) ((p (e j).1).1 (e j).2)) = _
    rw [scaledGluedAlcoveHeight_eq_transport h ε hε.ne' F boundary hb _ (hf _ _)]
    dsimp [F]
    rw [hindex, (hE (e j).1).1]
    rfl
  refine ⟨(flooredAntichainEvent_iff_native_constraints N _).mpr ?_, G, hagree, hG⟩
  intro j k
  rw [← hagree j, ← hagree k]
  exact hG _ _

theorem replicatedConfiguration_height_bound (m q N : ℕ) (ε C : ℝ) (hε : 0 ≤ ε)
    (tiles : Fin q → AlcoveTile d) (p : Fin q → FloorHeightConfiguration m d)
    (hp : ∀ i j, |(p i).2 j| ≤ C) (e : Fin N → Fin q × Fin m) :
    ∀ j, |(replicatedConfiguration m q N ε tiles p e).2 j| ≤ C * ε := by
  intro j
  change |ε * (p (e j).1).2 (e j).2| ≤ _
  rw [abs_mul, abs_of_nonneg hε, mul_comm C ε]
  exact mul_le_mul_of_nonneg_left (hp _ _) hε

end Antichain
