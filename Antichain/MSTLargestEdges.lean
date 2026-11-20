import Antichain.MSTGaugeBound

/-! The revised written minimum-tree proof: delete the j largest edges,
obtain exactly j+1 components, and pack one norm ball per component. -/

noncomputable section

namespace Antichain

open SimpleGraph MeasureTheory Set Finset
open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

def deletedComponentGraph (T : SimpleGraph V) (D : Finset (Sym2 V)) :
    SimpleGraph (T.deleteEdges (D : Set (Sym2 V))).ConnectedComponent :=
  SimpleGraph.fromEdgeSet
    (Sym2.map (T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk '' (D : Set (Sym2 V)))

omit [Fintype V] in
theorem reachable_deletedComponentGraph_of_walk (T : SimpleGraph V) (D : Finset (Sym2 V))
    {a b : V} (p : T.Walk a b) :
    (deletedComponentGraph T D).Reachable
      ((T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk a)
      ((T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk b) := by
  classical
  induction p with
  | nil => exact .refl _
  | @cons a b c hab p ih =>
    have hedge : (deletedComponentGraph T D).Reachable
        ((T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk a)
        ((T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk b) := by
      by_cases hsame : (T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk a =
          (T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk b
      · exact hsame ▸ .refl _
      · apply SimpleGraph.Adj.reachable
        change s(_, _) ∈ Sym2.map
          (T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk '' (D : Set (Sym2 V)) ∧ _
        refine ⟨?_, hsame⟩
        have hD : s(a, b) ∈ D := by
          by_contra hn
          apply hsame
          apply SimpleGraph.ConnectedComponent.sound
          exact (show (T.deleteEdges (D : Set (Sym2 V))).Adj a b from
            ⟨hab, fun hDadj => hn hDadj.1⟩).reachable
        exact ⟨s(a, b), hD, rfl⟩
    exact hedge.trans ih

omit [Fintype V] in
theorem connected_deletedComponentGraph {T : SimpleGraph V} (hT : T.Connected)
    (D : Finset (Sym2 V)) : (deletedComponentGraph T D).Connected := by
  classical
  haveI : Nonempty V := hT.nonempty
  haveI : Nonempty (T.deleteEdges (D : Set (Sym2 V))).ConnectedComponent :=
    ⟨(T.deleteEdges (D : Set (Sym2 V))).connectedComponentMk (Classical.choice inferInstance)⟩
  apply SimpleGraph.Connected.mk
  intro C E
  let F := T.deleteEdges (D : Set (Sym2 V))
  have h := reachable_deletedComponentGraph_of_walk T D
    (hT (graphComponentRepresentative F C) (graphComponentRepresentative F E)).some
  change (deletedComponentGraph T D).Reachable
    (F.connectedComponentMk (graphComponentRepresentative F C))
    (F.connectedComponentMk (graphComponentRepresentative F E)) at h
  simpa only [graphComponentRepresentative_spec] using h

theorem component_count_delete_le {T : SimpleGraph V} (hT : T.Connected)
    (D : Finset (Sym2 V)) :
    Nat.card (T.deleteEdges (D : Set (Sym2 V))).ConnectedComponent ≤ D.card + 1 := by
  classical
  let F := T.deleteEdges (D : Set (Sym2 V))
  let H := deletedComponentGraph T D
  letI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  letI : Fintype H.edgeSet := Fintype.ofFinite _
  have hH := (connected_deletedComponentGraph hT D).card_vert_le_card_edgeSet_add_one
  have hsub : H.edgeFinset ⊆ D.image (Sym2.map F.connectedComponentMk) := by
    intro e he
    have he' := SimpleGraph.mem_edgeFinset.mp he
    change e ∈ (deletedComponentGraph T D).edgeSet at he'
    rw [deletedComponentGraph, SimpleGraph.edgeSet_fromEdgeSet] at he'
    obtain ⟨a, ha, rfl⟩ := he'.1
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hc := (Finset.card_mono hsub).trans (Finset.card_image_le)
  have hc' : Nat.card H.edgeSet ≤ D.card := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    exact hc
  exact hH.trans (Nat.add_le_add_right hc' 1)

theorem tree_delete_component_count {T : SimpleGraph V} [Fintype T.edgeSet]
    (hT : T.IsTree) (D : Finset (Sym2 V)) (hD : D ⊆ T.edgeFinset) :
    Nat.card (T.deleteEdges (D : Set (Sym2 V))).ConnectedComponent = D.card + 1 := by
  classical
  apply le_antisymm (component_count_delete_le hT.isConnected D)
  let F := T.deleteEdges (D : Set (Sym2 V))
  letI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  have hcount := card_vertices_le_edges_add_components F
  have hedges : F.edgeFinset = T.edgeFinset \ D := by
    ext e
    simp [F, SimpleGraph.edgeSet_deleteEdges]
  rw [hedges, Finset.card_sdiff_of_subset hD] at hcount
  have htree := hT.card_edgeFinset
  simp only [← Nat.card_eq_fintype_card] at hcount htree
  change _ ≤ Nat.card F.ConnectedComponent
  have hc := Finset.card_le_card hD
  omega

theorem minimumSpanningTree_delete_separation (w : Sym2 V → ℝ)
    {T : SimpleGraph V} (hT : IsMinimumSpanningTree w T) (D : Finset (Sym2 V))
    (ell : ℝ) (hlong : ∀ e ∈ D, ell ≤ w e) {a b : V}
    (hsep : ¬(T.deleteEdges (D : Set (Sym2 V))).Reachable a b) : ell ≤ w s(a, b) := by
  apply minimumSpanningTree_threshold_separation w hT ell
  intro hreach
  apply hsep
  apply hreach.mono
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  intro he
  exact not_lt_of_ge (hlong s(x, y) he.1) hxy.2

variable {d : ℕ} [NeZero d]

def largestTreeEdges {T : SimpleGraph V} {r : ℕ} (e : Fin r ≃ T.edgeSet)
    (j : Fin r) : Finset (Sym2 V) :=
  (Finset.Iic j).image (fun k => (e k).val)

omit [Fintype V] in
theorem largestTreeEdges_card {T : SimpleGraph V} {r : ℕ}
    (e : Fin r ≃ T.edgeSet) (j : Fin r) : (largestTreeEdges e j).card = j.val + 1 := by
  classical
  have hg : Function.Injective (fun k : Fin r => (e k).val) :=
    Subtype.val_injective.comp e.injective
  rw [largestTreeEdges, Finset.card_image_of_injective _ hg, Fin.card_Iic]

omit [Fintype V] in
theorem largestTreeEdges_subset {T : SimpleGraph V} [Fintype T.edgeSet] {r : ℕ}
    (e : Fin r ≃ T.edgeSet) (j : Fin r) : largestTreeEdges e j ⊆ T.edgeFinset := by
  intro a ha
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
  exact SimpleGraph.mem_edgeFinset.mpr (e k).property

theorem mst_sorted_edge_bound_largest (hd : 2 ≤ d) (p : V → FloorSpace (Fin d))
    {T : SimpleGraph V} [Fintype T.edgeSet]
    (hT : IsMinimumSpanningTree (symmetricGaugeEdgeWeight p) T)
    {R : ℝ} (hR : 0 ≤ R) (hp : ∀ a, symmetricFloorGauge (p a) ≤ R)
    (hpair : ∀ a b, symmetricGaugeEdgeWeight p s(a, b) ≤ R)
    {r : ℕ} (e : Fin r ≃ T.edgeSet)
    (he : Antitone (fun j => symmetricGaugeEdgeWeight p (e j).val)) (j : Fin r) :
    symmetricGaugeEdgeWeight p (e j).val ≤
      3 * R * (((j.val + 2 : ℕ) : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
  classical
  let ell := symmetricGaugeEdgeWeight p (e j).val
  let D := largestTreeEdges e j
  let F := T.deleteEdges (D : Set (Sym2 V))
  letI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  have hcount : Nat.card F.ConnectedComponent = j.val + 2 := by
    rw [tree_delete_component_count hT.1 D (largestTreeEdges_subset e j), largestTreeEdges_card]
  have hell : 0 ≤ ell := symmetricGaugeEdgeWeight_nonneg p _
  have hellR : ell ≤ R := by
    have hall : ∀ f : Sym2 V, symmetricGaugeEdgeWeight p f ≤ R := by
      intro f
      induction f using Sym2.ind with
      | _ a b => exact hpair a b
    exact hall _
  have hlong : ∀ a ∈ D, ell ≤ symmetricGaugeEdgeWeight p a := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    exact he (Finset.mem_Iic.mp hk)
  let q : F.ConnectedComponent → FloorSpace (Fin d) :=
    fun C => p (graphComponentRepresentative F C)
  have hsep : Pairwise (fun C E : F.ConnectedComponent =>
      ell ≤ symmetricFloorGauge (q C - q E)) := by
    intro C E hCE
    apply minimumSpanningTree_delete_separation (symmetricGaugeEdgeWeight p) hT D ell hlong
    intro hreach
    apply hCE
    have h := SimpleGraph.ConnectedComponent.sound hreach
    change F.connectedComponentMk (graphComponentRepresentative F C) =
      F.connectedComponentMk (graphComponentRepresentative F E) at h
    simpa only [graphComponentRepresentative_spec] using h
  have hpack := symmetricGauge_packing_power_bound hd (Finset.univ : Finset F.ConnectedComponent)
    q hell hR hellR (fun C _ => hp _) (fun C _ E _ hCE => hsep hCE)
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card, hcount] at hpack
  have hbound := radius_bound_of_packing_power
    (by positivity : (0 : ℝ) < ((j.val + 2 : ℕ) : ℝ))
    (div_nonneg hell (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : (0 : ℝ) ≤ 3 * R / 2) (by omega : d - 1 ≠ 0) hpack
  change ell ≤ _
  nlinarith

theorem mst_edge_product_bound_largest (hd : 2 ≤ d) (p : V → FloorSpace (Fin d))
    {T : SimpleGraph V} [Fintype T.edgeSet]
    (hT : IsMinimumSpanningTree (symmetricGaugeEdgeWeight p) T)
    {R : ℝ} (hR : 0 ≤ R) (hp : ∀ a, symmetricFloorGauge (p a) ≤ R)
    (hpair : ∀ a b, symmetricGaugeEdgeWeight p s(a, b) ≤ R)
    {r : ℕ} (hr : T.edgeFinset.card = r) :
    (∏ f ∈ T.edgeFinset, symmetricGaugeEdgeWeight p f) ≤
      (3 * R) ^ r * ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) := by
  classical
  have hcard : Fintype.card T.edgeSet = r := (SimpleGraph.edgeFinset_card).symm.trans hr
  obtain ⟨e, he⟩ := exists_antitone_weight_enumeration
    (fun f : T.edgeSet => symmetricGaugeEdgeWeight p f.val) hcard
  have hprod : (∏ j : Fin r, symmetricGaugeEdgeWeight p (e j).val) =
      ∏ f ∈ T.edgeFinset, symmetricGaugeEdgeWeight p f := by
    rw [e.prod_comp (fun f : T.edgeSet => symmetricGaugeEdgeWeight p f.val)]
    exact (Finset.prod_subtype T.edgeFinset (fun _ => SimpleGraph.mem_edgeFinset)
      (symmetricGaugeEdgeWeight p)).symm
  rw [← hprod]
  calc
    _ ≤ ∏ j : Fin r, (3 * R *
        (((j.val + 2 : ℕ) : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹))) :=
      Finset.prod_le_prod (fun j _ => symmetricGaugeEdgeWeight_nonneg p _)
        (fun j _ => mst_sorted_edge_bound_largest hd p hT hR hp hpair e he j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, prod_successive_rpow]

end Antichain
