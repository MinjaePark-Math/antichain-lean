import Antichain.MinimumSpanningTree
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The finite graph component bound needed after deleting long MST edges. -/

noncomputable section

namespace Antichain

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def graphEdgeDifference (G : SimpleGraph V) : (V → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ) where
  toFun x e := x e.val.out.1 - x e.val.out.2
  map_add' x y := by ext e; simp; ring
  map_smul' a x := by ext e; simp; ring

omit [Fintype V] [DecidableEq V] in
theorem sym2_out_values_eq_iff (x : V → ℝ) (a b : V) :
    x s(a, b).out.1 = x s(a, b).out.2 ↔ x a = x b := by
  have h := (s(a, b) : Sym2 V).out_eq
  change s(s(a, b).out.1, s(a, b).out.2) = s(a, b) at h
  rcases Sym2.eq_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [ha, hb]
  · simp only [ha, hb, eq_comm]

theorem graphEdgeDifference_ker (G : SimpleGraph V) [DecidableRel G.Adj] :
    LinearMap.ker (graphEdgeDifference G) =
      LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ)) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, Matrix.toLin'_apply,
    G.lapMatrix_mulVec_eq_zero_iff_forall_adj]
  constructor
  · intro hx a b hab
    have h := congrFun hx ⟨s(a, b), hab⟩
    change x s(a, b).out.1 - x s(a, b).out.2 = 0 at h
    exact (sym2_out_values_eq_iff x a b).mp (sub_eq_zero.mp h)
  · intro hx
    funext e
    change x e.val.out.1 - x e.val.out.2 = 0
    apply sub_eq_zero.mpr
    apply hx
    change s(e.val.out.1, e.val.out.2) ∈ G.edgeSet
    have hrep : s(e.val.out.1, e.val.out.2) = e.val := e.val.out_eq
    rw [hrep]
    exact e.property

/-- Any finite graph has at least |V|-|E| connected components. Applying this
to a tree after deleting j edges gives at least j+1 components. -/
theorem card_vertices_le_edges_add_components (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent] :
    Fintype.card V ≤ G.edgeFinset.card + Fintype.card G.ConnectedComponent := by
  classical
  have hd := (graphEdgeDifference G).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (graphEdgeDifference G))
  rw [Module.finrank_fintype_fun_eq_card] at hd hr
  rw [graphEdgeDifference_ker G,
    ← G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix] at hd
  rw [← SimpleGraph.edgeFinset_card] at hr
  simp only [← Nat.card_eq_fintype_card] at hd hr ⊢
  omega

/-- Deleting all tree edges of weight at least ell leaves at least one more
component than the number of deleted edges, exactly as required in the
written minimum-spanning-tree packing argument. -/
theorem treeBelow_component_count (T : SimpleGraph V) [Fintype T.edgeSet]
    (hT : T.IsTree) (w : Sym2 V → ℝ) (ell : ℝ) :
    (T.edgeFinset.filter (fun e => ell ≤ w e)).card + 1 ≤
      Nat.card (treeBelow T w ell).ConnectedComponent := by
  classical
  let F := treeBelow T w ell
  letI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  have hcount := card_vertices_le_edges_add_components F
  have hedges : F.edgeFinset = T.edgeFinset.filter (fun e => w e < ell) := by
    ext e
    induction e using Sym2.ind with
    | _ a b => simp [F, treeBelow]
  rw [hedges] at hcount
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := T.edgeFinset) (p := fun e => w e < ell)
  simp only [not_lt] at hpart
  have htree := hT.card_edgeFinset
  simp only [← Nat.card_eq_fintype_card] at hcount htree
  change _ ≤ Nat.card F.ConnectedComponent
  omega

omit [Fintype V] [DecidableEq V] in
def graphComponentRepresentative (G : SimpleGraph V) (C : G.ConnectedComponent) : V :=
  Classical.choose C.exists_rep

omit [Fintype V] [DecidableEq V] in
theorem graphComponentRepresentative_spec (G : SimpleGraph V) (C : G.ConnectedComponent) :
    G.connectedComponentMk (graphComponentRepresentative G C) = C :=
  Classical.choose_spec C.exists_rep

omit [Fintype V] [DecidableEq V] in
theorem graphComponentRepresentative_injective (G : SimpleGraph V) :
    Function.Injective (graphComponentRepresentative G) := by
  intro C D heq
  have h := congrArg G.connectedComponentMk heq
  simpa only [graphComponentRepresentative_spec] using h

theorem minimumSpanningTree_component_representatives_separated
    (w : Sym2 V → ℝ) {T : SimpleGraph V} (hT : IsMinimumSpanningTree w T)
    (ell : ℝ) :
    Pairwise (fun C D : (treeBelow T w ell).ConnectedComponent =>
      ell ≤ w s(graphComponentRepresentative (treeBelow T w ell) C,
        graphComponentRepresentative (treeBelow T w ell) D)) := by
  intro C D hCD
  apply minimumSpanningTree_threshold_separation w hT ell
  intro hreach
  apply hCD
  have h := SimpleGraph.ConnectedComponent.eq.mpr hreach
  simpa only [graphComponentRepresentative_spec] using h

end Antichain
