import Antichain.ParentHeightCoordinates
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring

/-! Actual rooted finite-tree orderings for the manuscript's tree-height chart.
The construction orders vertices by graph distance, breaking ties by label.
-/

noncomputable section

namespace Antichain

open SimpleGraph Finset

/-- A separate vertex carrier allows an auxiliary distance order without
changing the ordinary order on the source label type. -/
structure RootedOrderVertex (r : ℕ) where
  label : Fin (r + 1)

def rootedOrderVertexEquiv (r : ℕ) : RootedOrderVertex r ≃ Fin (r + 1) where
  toFun v := v.label
  invFun v := ⟨v⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (r : ℕ) : Fintype (RootedOrderVertex r) :=
  Fintype.ofEquiv (Fin (r + 1)) (rootedOrderVertexEquiv r).symm

theorem connected_exists_adj_dist_lt {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (root v : V) (hv : v ≠ root) :
    ∃ u, G.Adj v u ∧ G.dist root u < G.dist root v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v root
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v u root hadj tail =>
    refine ⟨u, hadj, ?_⟩
    have hle := G.dist_le tail
    have hlen : tail.length + 1 = G.dist v root := by simpa using hp
    rw [SimpleGraph.dist_comm (G := G) (u := root) (v := u),
      SimpleGraph.dist_comm (G := G) (u := root) (v := v)]
    omega

theorem exists_root_fixed_earlier_parent {r : ℕ} (G : SimpleGraph (Fin (r + 1)))
    (hG : G.Connected) :
    ∃ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 ∧
      ∃ parent : EarlierParent r,
        ∀ j, G.Adj (σ j.succ) (σ (parentLabel parent j)) := by
  classical
  let key : RootedOrderVertex r → ℕ :=
    fun v => G.dist 0 v.label * (r + 1) + v.label.val
  have hkey : Function.Injective key := by
    intro u v h
    apply (rootedOrderVertexEquiv r).injective
    apply Fin.ext
    have hm := congrArg (fun x => x % (r + 1)) h
    have hu : u.label.val % (r + 1) = u.label.val := Nat.mod_eq_of_lt u.label.isLt
    have hv : v.label.val % (r + 1) = v.label.val := Nat.mod_eq_of_lt v.label.isLt
    simpa only [key, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
      Nat.zero_mod, zero_add, hu, hv] using hm
  letI : LinearOrder (RootedOrderVertex r) := LinearOrder.lift' key hkey
  let e : Fin (r + 1) ≃o RootedOrderVertex r :=
    Fintype.orderIsoFinOfCardEq (RootedOrderVertex r)
      ((Fintype.card_congr (rootedOrderVertexEquiv r)).trans (Fintype.card_fin _))
  let σ : Equiv.Perm (Fin (r + 1)) := e.toEquiv.trans (rootedOrderVertexEquiv r)
  have hσapply (i : Fin (r + 1)) : σ i = (e i).label := rfl
  have hinv (v : Fin (r + 1)) : σ.symm v = e.symm ⟨v⟩ := rfl
  have hinv0 : σ.symm 0 = 0 := by
    apply le_antisymm
    · rw [hinv]
      have hle : (⟨(0 : Fin (r + 1))⟩ : RootedOrderVertex r) ≤ e 0 := by
        change key ⟨0⟩ ≤ key (e 0)
        simp [key, SimpleGraph.dist_self]
      simpa using e.symm.monotone hle
    · exact Fin.zero_le _
  have hroot : σ 0 = 0 := by
    have h := congrArg σ hinv0
    simpa using h.symm
  refine ⟨σ, hroot, ?_⟩
  have hparent : ∀ j : Fin r, ∃ i : Fin (j.val + 1),
      G.Adj (σ j.succ) (σ ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩) := by
    intro j
    have hv : σ j.succ ≠ 0 := by
      intro h
      have hz : j.succ = 0 := σ.injective (h.trans hroot.symm)
      have := congrArg Fin.val hz
      simp at this
    obtain ⟨u, hadj, hdist⟩ := connected_exists_adj_dist_lt G hG 0 (σ j.succ) hv
    have hkeylt : key ⟨u⟩ < key (e j.succ) := by
      have hmul := Nat.mul_le_mul_right (r + 1) (Nat.succ_le_of_lt hdist)
      rw [Nat.succ_mul] at hmul
      dsimp [key]
      rw [← hσapply]
      have hu := u.isLt
      omega
    have hidx : σ.symm u < j.succ := by
      rw [hinv]
      have hlt : (⟨u⟩ : RootedOrderVertex r) < e j.succ := hkeylt
      simpa using e.symm.strictMono hlt
    let i : Fin (j.val + 1) := ⟨(σ.symm u).val, hidx⟩
    refine ⟨i, ?_⟩
    have heq : (⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ : Fin (r + 1)) =
        σ.symm u := by rfl
    rw [heq, σ.apply_symm_apply]
    exact hadj
  choose parent hparent using hparent
  exact ⟨parent, fun j => by simpa only [parentLabel] using hparent j⟩

def rootedParentEdge {r : ℕ} (σ : Equiv.Perm (Fin (r + 1)))
    (parent : EarlierParent r) (j : Fin r) : Sym2 (Fin (r + 1)) :=
  s(σ j.succ, σ (parentLabel parent j))

theorem rootedParentEdge_injective {r : ℕ} (σ : Equiv.Perm (Fin (r + 1)))
    (parent : EarlierParent r) : Function.Injective (rootedParentEdge σ parent) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with hstraight | hcross
  · exact Fin.succ_injective r (σ.injective hstraight.1)
  · have hi := congrArg Fin.val (σ.injective hcross.1)
    have hj := congrArg Fin.val (σ.injective hcross.2)
    have hpi := (parent i).isLt
    have hpj := (parent j).isLt
    simp only [Fin.val_succ, parentLabel] at hi hj
    omega

theorem rootedParentEdge_mem {r : ℕ} (G : SimpleGraph (Fin (r + 1)))
    (σ : Equiv.Perm (Fin (r + 1))) (parent : EarlierParent r)
    (hparent : ∀ j, G.Adj (σ j.succ) (σ (parentLabel parent j))) (j : Fin r) :
    rootedParentEdge σ parent j ∈ G.edgeSet :=
  (SimpleGraph.mem_edgeSet G).mpr (hparent j)

theorem rootedParentEdge_image_eq_edgeFinset {r : ℕ}
    (G : SimpleGraph (Fin (r + 1))) [Fintype G.edgeSet] (hG : G.IsTree)
    (σ : Equiv.Perm (Fin (r + 1))) (parent : EarlierParent r)
    (hparent : ∀ j, G.Adj (σ j.succ) (σ (parentLabel parent j))) :
    Finset.univ.image (rootedParentEdge σ parent) = G.edgeFinset := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (rootedParentEdge_mem G σ parent hparent j)
  · rw [Finset.card_image_of_injective _ (rootedParentEdge_injective σ parent),
      Finset.card_univ, Fintype.card_fin]
    have hcard := hG.card_edgeFinset
    simp only [Fintype.card_fin] at hcard
    omega

theorem exists_rooted_tree_order {r : ℕ} (G : SimpleGraph (Fin (r + 1)))
    [Fintype G.edgeSet] (hG : G.IsTree) :
    ∃ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 ∧
      ∃ parent : EarlierParent r,
        (∀ j, G.Adj (σ j.succ) (σ (parentLabel parent j))) ∧
        Function.Injective (rootedParentEdge σ parent) ∧
        Finset.univ.image (rootedParentEdge σ parent) = G.edgeFinset := by
  obtain ⟨σ, hroot, parent, hparent⟩ := exists_root_fixed_earlier_parent G hG.isConnected
  exact ⟨σ, hroot, parent, hparent, rootedParentEdge_injective σ parent,
    rootedParentEdge_image_eq_edgeFinset G hG σ parent hparent⟩

theorem rootedParentEdge_range_eq_edgeSet {r : ℕ}
    (G : SimpleGraph (Fin (r + 1))) (hG : G.IsTree)
    (σ : Equiv.Perm (Fin (r + 1))) (parent : EarlierParent r)
    (hparent : ∀ j, G.Adj (σ j.succ) (σ (parentLabel parent j))) :
    Set.range (rootedParentEdge σ parent) = G.edgeSet := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  have himage := rootedParentEdge_image_eq_edgeFinset G hG σ parent hparent
  ext e
  rw [← SimpleGraph.mem_edgeFinset, ← himage]
  simp

/-- A tree admits the root-fixed earlier-parent chart with an exact bijection
of its actual edges, without a finite-edge enumeration in the hypotheses. -/
theorem exists_rooted_tree_order_edgeSet {r : ℕ} (G : SimpleGraph (Fin (r + 1)))
    (hG : G.IsTree) :
    ∃ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 ∧
      ∃ parent : EarlierParent r,
        (∀ j, G.Adj (σ j.succ) (σ (parentLabel parent j))) ∧
        Function.Injective (rootedParentEdge σ parent) ∧
        Set.range (rootedParentEdge σ parent) = G.edgeSet := by
  obtain ⟨σ, hroot, parent, hparent⟩ := exists_root_fixed_earlier_parent G hG.isConnected
  exact ⟨σ, hroot, parent, hparent, rootedParentEdge_injective σ parent,
    rootedParentEdge_range_eq_edgeSet G hG σ parent hparent⟩

theorem prod_rootedParentEdge_eq {r : ℕ} {M : Type*} [CommMonoid M]
    (G : SimpleGraph (Fin (r + 1))) [Fintype G.edgeSet] (hG : G.IsTree)
    (σ : Equiv.Perm (Fin (r + 1))) (parent : EarlierParent r)
    (hparent : ∀ j, G.Adj (σ j.succ) (σ (parentLabel parent j)))
    (w : Sym2 (Fin (r + 1)) → M) :
    (∏ j : Fin r, w (rootedParentEdge σ parent j)) = ∏ e ∈ G.edgeFinset, w e := by
  classical
  rw [← rootedParentEdge_image_eq_edgeFinset G hG σ parent hparent]
  rw [Finset.prod_image]
  exact fun i _ j _ hij => rootedParentEdge_injective σ parent hij

end Antichain
