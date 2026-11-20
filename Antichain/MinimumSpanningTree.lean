import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Actual finite minimum spanning trees and the threshold-separation lemma
used by the written proof of the local pinned-volume upper bound. -/

noncomputable section

namespace Antichain

open SimpleGraph Finset Set

variable {V : Type*} [Fintype V] [DecidableEq V]

def treeWeight (w : Sym2 V → ℝ) (T : SimpleGraph V) : ℝ := by
  classical
  exact ∑ e ∈ T.edgeFinset, w e

omit [DecidableEq V] in
theorem treeWeight_eq_sum (w : Sym2 V → ℝ) (T : SimpleGraph V) [Fintype T.edgeSet] :
    treeWeight w T = ∑ e ∈ T.edgeFinset, w e := by
  classical
  unfold treeWeight
  apply Finset.sum_congr
  · ext e
    simp
  · intro e _
    rfl

def IsMinimumSpanningTree (w : Sym2 V → ℝ) (T : SimpleGraph V) : Prop :=
  T.IsTree ∧ ∀ S : SimpleGraph V, S.IsTree → treeWeight w T ≤ treeWeight w S

omit [DecidableEq V] in
theorem exists_minimumSpanningTree [Nonempty V] (w : Sym2 V → ℝ) :
    ∃ T : SimpleGraph V, IsMinimumSpanningTree w T := by
  classical
  obtain ⟨T, _, hT⟩ := (SimpleGraph.connected_top (V := V)).exists_isTree_le
  obtain ⟨S, hS, hmin⟩ := Set.exists_min_image
    {S : SimpleGraph V | S.IsTree} (treeWeight w) (Set.toFinite _) ⟨T, hT⟩
  exact ⟨S, hS, fun R hR => hmin R hR⟩

def treeBelow (T : SimpleGraph V) (w : Sym2 V → ℝ) (ell : ℝ) : SimpleGraph V where
  Adj a b := T.Adj a b ∧ w s(a, b) < ell
  symm a b h := ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩
  loopless a h := T.loopless a h.1

omit [Fintype V] [DecidableEq V] in
theorem treeBelow_le (T : SimpleGraph V) (w : Sym2 V → ℝ) (ell : ℝ) :
    treeBelow T w ell ≤ T := fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] in
theorem reachable_treeBelow_of_walk {T : SimpleGraph V} (w : Sym2 V → ℝ)
    (ell : ℝ) {a b : V} (p : T.Walk a b)
    (hp : ∀ e ∈ p.edges, w e < ell) : (treeBelow T w ell).Reachable a b := by
  induction p with
  | nil => exact .refl _
  | @cons a b c hab p ih =>
    exact (show (treeBelow T w ell).Adj a b from
      ⟨hab, hp s(a, b) (by simp)⟩).reachable.trans (ih (fun e he => hp e (by simp [he])))

theorem treeWeight_sup_edge (w : Sym2 V → ℝ) (T : SimpleGraph V)
    {a b : V} (hne : a ≠ b) (hnot : ¬T.Adj a b) :
    treeWeight w (T ⊔ SimpleGraph.edge a b) = treeWeight w T + w s(a, b) := by
  classical
  rw [treeWeight_eq_sum, treeWeight_eq_sum]
  rw [T.edgeFinset_sup_edge hnot hne, Finset.sum_cons]
  ring

theorem treeWeight_delete_add (w : Sym2 V → ℝ) (T : SimpleGraph V)
    {e : Sym2 V} (he : e ∈ T.edgeSet) :
    treeWeight w (T.deleteEdges {e}) + w e = treeWeight w T := by
  classical
  rw [treeWeight_eq_sum, treeWeight_eq_sum]
  have hdel : (T.deleteEdges {e}).edgeFinset = T.edgeFinset.erase e := by
    ext f
    simp [SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [hdel]
  exact Finset.sum_erase_add _ _ (SimpleGraph.mem_edgeFinset.mpr he)

omit [Fintype V] [DecidableEq V] in
theorem connected_delete_of_not_bridge {T : SimpleGraph V} (hT : T.Connected)
    {e : Sym2 V} (he : ¬ T.IsBridge e) : (T.deleteEdges {e}).Connected := by
  induction e using Sym2.ind with
  | _ a b => exact hT.connected_delete_edge_of_not_isBridge he

theorem tree_of_connected_exchange {T : SimpleGraph V} (hT : T.IsTree)
    {a b : V} (hne : a ≠ b) (hnot : ¬T.Adj a b) {e : Sym2 V}
    (he : e ∈ T.edgeSet)
    (hconn : ((T ⊔ SimpleGraph.edge a b).deleteEdges {e}).Connected) :
    ((T ⊔ SimpleGraph.edge a b).deleteEdges {e}).IsTree := by
  classical
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨hconn, ?_⟩
  have he' : e ∈ (T ⊔ SimpleGraph.edge a b).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_sup_left (SimpleGraph.mem_edgeFinset.mpr he)
  have hcard := T.card_edgeFinset_sup_edge hnot hne
  have htree := hT.card_edgeFinset
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    Nat.card_eq_fintype_card]
  have hdel : ((T ⊔ SimpleGraph.edge a b).deleteEdges {e}).edgeFinset =
      (T ⊔ SimpleGraph.edge a b).edgeFinset.erase e := by
    ext f
    simp [SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [hdel, Finset.card_erase_of_mem he']
  omega

/-- The written MST cut/exchange principle: after deleting every tree edge
of weight at least ell, distinct remaining components cannot be joined by a
complete-graph edge of weight less than ell. -/
theorem minimumSpanningTree_threshold_separation (w : Sym2 V → ℝ)
    {T : SimpleGraph V} (hT : IsMinimumSpanningTree w T)
    (ell : ℝ) {a b : V}
    (hsep : ¬(treeBelow T w ell).Reachable a b) : ell ≤ w s(a, b) := by
  classical
  by_contra hbad
  have hshort : w s(a, b) < ell := lt_of_not_ge hbad
  have hne : a ≠ b := by
    intro hab
    subst b
    exact hsep (.refl _)
  have hnot : ¬T.Adj a b := by
    intro hab
    exact hsep (show (treeBelow T w ell).Adj a b from ⟨hab, hshort⟩).reachable
  obtain ⟨p, hp⟩ := hT.1.isConnected.exists_isPath a b
  have hlong : ∃ e ∈ p.edges, ell ≤ w e := by
    by_contra! hall
    exact hsep (reachable_treeBelow_of_walk w ell p hall)
  obtain ⟨e, he, hweight⟩ := hlong
  have heT : e ∈ T.edgeSet := p.edges_subset_edgeSet he
  let H := T ⊔ SimpleGraph.edge a b
  let pH : H.Walk a b := p.mapLe le_sup_left
  have hpH : pH.IsPath := hp.mapLe le_sup_left
  have hnew : H.Adj b a := by
    apply (show SimpleGraph.edge a b ≤ H from le_sup_right)
    exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩
  have hnew_not : s(b, a) ∉ pH.edges := by
    intro hmem
    have hmem' : s(a, b) ∈ p.edges := by
      simpa only [pH, Walk.edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun,
        id_eq, Sym2.eq_swap] using hmem
    exact hnot (p.adj_of_mem_edges hmem')
  let cycle : H.Walk b b := Walk.cons hnew pH
  have hcycle : cycle.IsCycle := Path.cons_isCycle ⟨pH, hpH⟩ hnew hnew_not
  have hecycle : e ∈ cycle.edges := by
    simp only [cycle, Walk.edges_cons, List.mem_cons]
    right
    simpa only [pH, Walk.edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq] using he
  have hnotbridge : ¬H.IsBridge e := by
    intro hbridge
    exact (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hbridge).2 cycle hcycle hecycle
  have hHconn : H.Connected := hT.1.isConnected.mono le_sup_left
  have hconn := connected_delete_of_not_bridge hHconn hnotbridge
  have htree := tree_of_connected_exchange hT.1 hne hnot heT hconn
  have hmin := hT.2 (H.deleteEdges {e}) htree
  have heH : e ∈ H.edgeSet := SimpleGraph.edgeSet_mono le_sup_left heT
  have hsum := treeWeight_delete_add w H heH
  have hsup := treeWeight_sup_edge w T hne hnot
  change treeWeight w H = _ at hsup
  linarith

end Antichain
