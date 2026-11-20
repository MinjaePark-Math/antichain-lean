import Antichain.SegmentGeometry
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.List.Chain

/-! Actual finite subdivisions through locally finite closed convex covers.
The finite chain is constructed from the cover, not supplied as an input. -/

noncomputable section

namespace Antichain

open Set Filter Metric
open scoped Topology Pointwise

set_option maxHeartbeats 1000000

def intervalTileStep {I : Type*} (S : Finset I) (A : I → Set ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∃ i ∈ S, Icc a b ⊆ A i

/-- A finite closed order-convex cover of an interval gives a genuine finite
chain of subintervals, each contained in one cover member. -/
theorem finite_closed_interval_subdivision {I : Type*} (S : Finset I) (A : I → Set ℝ)
    (hclosed : ∀ i ∈ S, IsClosed (A i)) (hord : ∀ i ∈ S, (A i).OrdConnected)
    (a b : ℝ) (hab : a ≤ b)
    (hcover : ∀ t ∈ Icc a b, ∃ i ∈ S, t ∈ A i) :
    Relation.ReflTransGen (intervalTileStep S A) a b := by
  classical
  induction S using Finset.strongInductionOn generalizing a b with
  | _ S ih =>
    by_cases heq : a = b
    · subst b
      exact .refl
    have hablt : a < b := lt_of_le_of_ne hab heq
    obtain ⟨i, hi, hai⟩ := hcover a ⟨le_rfl, hab⟩
    have hcompact : IsCompact (A i ∩ Icc a b) :=
      isCompact_Icc.inter_left (hclosed i hi)
    obtain ⟨c, hc⟩ := hcompact.exists_isGreatest ⟨a, hai, le_rfl, hab⟩
    have hac : a ≤ c := hc.1.2.1
    have hcb : c ≤ b := hc.1.2.2
    have hstep : intervalTileStep S A a c := by
      refine ⟨hac, i, hi, ?_⟩
      exact (hord i hi).out hai hc.1.1
    by_cases hceq : c = b
    · subst c
      exact .single hstep
    have hcblt : c < b := lt_of_le_of_ne hcb hceq
    let U : Set ℝ := ⋃ j ∈ S.erase i, A j
    have hUclosed : IsClosed U := isClosed_biUnion_finset
      (fun j hj => hclosed j (Finset.mem_of_mem_erase hj))
    have hright : Ioc c b ⊆ U := by
      intro t ht
      obtain ⟨j, hj, htj⟩ := hcover t ⟨hac.trans ht.1.le, ht.2⟩
      have hji : j ≠ i := by
        intro hji
        subst j
        have htc : t ≤ c := hc.2 ⟨htj, hac.trans ht.1.le, ht.2⟩
        exact not_le_of_gt ht.1 htc
      exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, htj⟩
    have htail : ∀ t ∈ Icc c b, ∃ j ∈ S.erase i, t ∈ A j := by
      have hsub : Icc c b ⊆ U := by
        rw [← closure_Ioc hcblt.ne]
        exact closure_minimal hright hUclosed
      intro t ht
      obtain ⟨j, hj, htj⟩ := Set.mem_iUnion₂.mp (hsub ht)
      exact ⟨j, hj, htj⟩
    have hrest := ih (S.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hclosed j (Finset.mem_of_mem_erase hj))
      (fun j hj => hord j (Finset.mem_of_mem_erase hj)) c b hcb htail
    have hrest' : Relation.ReflTransGen (intervalTileStep S A) c b :=
      hrest.mono (fun x y hxy => ⟨hxy.1, by
        obtain ⟨j, hj, hsub⟩ := hxy.2
        exact ⟨j, Finset.mem_of_mem_erase hj, hsub⟩⟩)
    exact (Relation.ReflTransGen.single hstep).trans hrest'

/-- The finite subdivision is also exposed as a literal finite endpoint list,
starting at a and ending at b, with each successive interval in one tile. -/
theorem finite_closed_interval_subdivision_list {I : Type*} (S : Finset I) (A : I → Set ℝ)
    (hclosed : ∀ i ∈ S, IsClosed (A i)) (hord : ∀ i ∈ S, (A i).OrdConnected)
    (a b : ℝ) (hab : a ≤ b)
    (hcover : ∀ t ∈ Icc a b, ∃ i ∈ S, t ∈ A i) :
    ∃ l : List ℝ, (a :: l).IsChain (intervalTileStep S A) ∧
      (a :: l).getLast (List.cons_ne_nil _ _) = b :=
  List.exists_isChain_cons_of_relationReflTransGen
    (finite_closed_interval_subdivision S A hclosed hord a b hab hcover)

variable {d : ℕ}

def segmentCoverStep {I : Type*} (B : I → Set (FloorSpace (Fin d)))
    (u v : FloorSpace (Fin d)) (s t : ℝ) : Prop :=
  s ≤ t ∧ ∃ i, ∀ r ∈ Icc s t, floorSegment u v r ∈ B i

/-- Local finiteness reduces the actual compact straight segment to finitely
many closed convex cover members.  Applying the finite interval construction
produces a finite subsegment chain through those actual members. -/
theorem locallyFinite_closed_convex_segment_subdivision {I : Type*}
    (B : I → Set (FloorSpace (Fin d))) (hcover : ⋃ i, B i = univ)
    (hclosed : ∀ i, IsClosed (B i)) (hconvex : ∀ i, Convex ℝ (B i))
    (hlocal : LocallyFinite B) (u v : FloorSpace (Fin d)) :
    Relation.ReflTransGen (segmentCoverStep B u v) 0 1 := by
  classical
  let K : Set (FloorSpace (Fin d)) := floorSegment u v '' Icc (0 : ℝ) 1
  have hcompact : IsCompact K := isCompact_Icc.image (floorSegment_continuous u v)
  have hfinite := hlocal.finite_nonempty_inter_compact hcompact
  let S : Finset I := hfinite.toFinset
  let A : I → Set ℝ := fun i => (floorSegment u v) ⁻¹' B i
  have hAclosed (i : I) (_ : i ∈ S) : IsClosed (A i) :=
    (hclosed i).preimage (floorSegment_continuous u v)
  have hAord (i : I) (_ : i ∈ S) : (A i).OrdConnected := by
    have hh := (hconvex i).affine_preimage (AffineMap.lineMap u v)
    have hmap : (AffineMap.lineMap u v : ℝ → FloorSpace (Fin d)) = floorSegment u v := by
      funext t
      exact AffineMap.lineMap_apply_module u v t
    rw [hmap] at hh
    exact hh.ordConnected
  have hAcov : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i ∈ S, t ∈ A i := by
    intro t ht
    have hx : floorSegment u v t ∈ ⋃ i, B i := hcover.symm ▸ mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hiS : i ∈ S := by
      apply hfinite.mem_toFinset.mpr
      exact ⟨floorSegment u v t, hi, t, ht, rfl⟩
    exact ⟨i, hiS, hi⟩
  have hchain := finite_closed_interval_subdivision S A hAclosed hAord 0 1 zero_le_one hAcov
  exact hchain.mono (fun s t hst => ⟨hst.1, by
    obtain ⟨i, _, hsub⟩ := hst.2
    exact ⟨i, hsub⟩⟩)

/-- A literal finite endpoint list in [0,1], starting at zero and ending at
one, each successive closed subsegment lying inside one actual cover tile. -/
theorem locallyFinite_closed_convex_segment_subdivision_list {I : Type*}
    (B : I → Set (FloorSpace (Fin d))) (hcover : ⋃ i, B i = univ)
    (hclosed : ∀ i, IsClosed (B i)) (hconvex : ∀ i, Convex ℝ (B i))
    (hlocal : LocallyFinite B) (u v : FloorSpace (Fin d)) :
    ∃ l : List ℝ, ((0 : ℝ) :: l).IsChain (segmentCoverStep B u v) ∧
      ((0 : ℝ) :: l).getLast (List.cons_ne_nil _ _) = 1 :=
  List.exists_isChain_cons_of_relationReflTransGen
    (locallyFinite_closed_convex_segment_subdivision B hcover hclosed hconvex hlocal u v)

/-- Telescope the genuine finite subdivision and use the exact positive
homogeneity of the directional cost on each subsegment.  No continuity or
interval-induction global gluing theorem is used in this proof. -/
theorem global_directional_of_finite_segment_subdivision {I : Type*} [NeZero d]
    (B : I → Set (FloorSpace (Fin d))) (hcover : ⋃ i, B i = univ)
    (hclosed : ∀ i, IsClosed (B i)) (hconvex : ∀ i, Convex ℝ (B i))
    (hlocal : LocallyFinite B) (H : FloorSpace (Fin d) → ℝ)
    (hH : ∀ i, ∀ x ∈ B i, ∀ y ∈ B i, H x - H y ≤ nativeFloorCost x y) :
    ∀ u v, H u - H v ≤ nativeFloorCost u v := by
  intro u v
  have htel : ∀ s t, Relation.ReflTransGen (segmentCoverStep B u v) s t →
      H (floorSegment u v s) - H (floorSegment u v t) ≤
        (t - s) * nativeFloorCost u v := by
    intro s t hst
    induction hst with
    | refl => simp
    | @tail t z hst htz ih =>
      obtain ⟨htzle, i, hipiece⟩ := htz
      have hh := hH i (floorSegment u v t) (hipiece t ⟨le_rfl, htzle⟩)
        (floorSegment u v z) (hipiece z ⟨htzle, le_rfl⟩)
      rw [floorSegment_directed_cost u v t z htzle] at hh
      nlinarith
  have hh := htel 0 1
    (locallyFinite_closed_convex_segment_subdivision B hcover hclosed hconvex hlocal u v)
  simpa only [floorSegment, sub_zero, one_smul, zero_smul, add_zero, sub_self,
    zero_add, one_mul] using hh

end Antichain
