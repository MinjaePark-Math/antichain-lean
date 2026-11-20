import Antichain.SymmetricGaugePacking
import Antichain.RootedTreeOrder
import Mathlib.Data.Fin.Tuple.Sort

/-! Sorted-edge packing bounds for an actual minimum spanning tree in the
paper's symmetrized gauge norm. -/

noncomputable section

namespace Antichain

open SimpleGraph MeasureTheory Set Finset
open scoped ENNReal Topology

variable {d : ℕ} [NeZero d]
variable {V : Type*} [Fintype V] [DecidableEq V]

def symmetricGaugeEdgeWeight (p : V → FloorSpace (Fin d)) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => symmetricFloorGauge (p a - p b), fun a b => by
    change symmetricFloorGauge (p a - p b) = symmetricFloorGauge (p b - p a)
    rw [← neg_sub (p b) (p a), symmetricFloorGauge_neg]⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem symmetricGaugeEdgeWeight_mk (p : V → FloorSpace (Fin d)) (a b : V) :
    symmetricGaugeEdgeWeight p s(a, b) = symmetricFloorGauge (p a - p b) := rfl

omit [Fintype V] [DecidableEq V] in
theorem symmetricGaugeEdgeWeight_nonneg (p : V → FloorSpace (Fin d)) (e : Sym2 V) :
    0 ≤ symmetricGaugeEdgeWeight p e := by
  induction e using Sym2.ind with
  | _ a b => exact symmetricFloorGauge_nonneg _

theorem symmetricFloorGauge_le_sqrt_of_mem_reference {u : FloorSpace (Fin d)}
    (hu : u ∈ referenceSimplex d) : symmetricFloorGauge u ≤ Real.sqrt (d : ℝ) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i : Fin d => u.val i)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j : Fin d => u.val j)
  rw [symmetricFloorGauge_formula, hi, hj]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hu.2 i j) (Real.sqrt_nonneg (d : ℝ))

theorem symmetricFloorGauge_pair_le_two_sqrt {u v : FloorSpace (Fin d)}
    (hu : u ∈ referenceSimplex d) (hv : v ∈ referenceSimplex d) :
    symmetricFloorGauge (u - v) ≤ 2 * Real.sqrt (d : ℝ) := by
  have h := symmetricFloorGauge_add_le u (-v)
  rw [← sub_eq_add_neg, symmetricFloorGauge_neg] at h
  linarith [symmetricFloorGauge_le_sqrt_of_mem_reference hu,
    symmetricFloorGauge_le_sqrt_of_mem_reference hv]

theorem mst_component_packing (hd : 2 ≤ d) (p : V → FloorSpace (Fin d))
    {T : SimpleGraph V} (hT : IsMinimumSpanningTree (symmetricGaugeEdgeWeight p) T)
    {ell R : ℝ} (hell : 0 ≤ ell) (hR : 0 ≤ R) (hellR : ell ≤ R)
    (hp : ∀ a, symmetricFloorGauge (p a) ≤ R) :
    (Nat.card (treeBelow T (symmetricGaugeEdgeWeight p) ell).ConnectedComponent : ℝ) *
      (ell / 2) ^ (d - 1) ≤ (3 * R / 2) ^ (d - 1) := by
  classical
  let F := treeBelow T (symmetricGaugeEdgeWeight p) ell
  letI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  let q : F.ConnectedComponent → FloorSpace (Fin d) :=
    fun C => p (graphComponentRepresentative F C)
  have hsep := minimumSpanningTree_component_representatives_separated
    (symmetricGaugeEdgeWeight p) hT ell
  have h := symmetricGauge_packing_power_bound hd (Finset.univ : Finset F.ConnectedComponent)
    q hell hR hellR (fun C _ => hp _) (fun C _ D _ hCD => hsep hCD)
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using h

theorem exists_antitone_weight_enumeration {A : Type*} [Fintype A] (w : A → ℝ)
    {r : ℕ} (hr : Fintype.card A = r) :
    ∃ e : Fin r ≃ A, Antitone (fun j => w (e j)) := by
  classical
  let b : Fin r ≃ A := (Fintype.equivFinOfCardEq hr).symm
  let f : Fin r → OrderDual ℝ := fun j => w (b j)
  let s := Tuple.sort f
  exact ⟨s.trans b, Tuple.monotone_sort f⟩

theorem mst_sorted_edge_bound (hd : 2 ≤ d) (p : V → FloorSpace (Fin d))
    {T : SimpleGraph V} [Fintype T.edgeSet]
    (hT : IsMinimumSpanningTree (symmetricGaugeEdgeWeight p) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hp : ∀ a, symmetricFloorGauge (p a) ≤ R)
    (hpair : ∀ a b, symmetricGaugeEdgeWeight p s(a, b) ≤ R)
    {r : ℕ} (e : Fin r ≃ T.edgeSet)
    (he : Antitone (fun j => symmetricGaugeEdgeWeight p (e j).val)) (j : Fin r) :
    symmetricGaugeEdgeWeight p (e j).val ≤
      3 * R * (((j.val + 2 : ℕ) : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
  classical
  let ell := symmetricGaugeEdgeWeight p (e j).val
  have hell : 0 ≤ ell := symmetricGaugeEdgeWeight_nonneg p _
  have hellR : ell ≤ R := by
    have hall : ∀ f : Sym2 V, symmetricGaugeEdgeWeight p f ≤ R := by
      intro f
      induction f using Sym2.ind with
      | _ a b => exact hpair a b
    exact hall _
  have hlong : j.val + 1 ≤
      (T.edgeFinset.filter (fun f => ell ≤ symmetricGaugeEdgeWeight p f)).card := by
    let g : Fin r → Sym2 V := fun i => (e i).val
    have hg : Function.Injective g := Subtype.val_injective.comp e.injective
    have hsub : (Finset.Iic j).image g ⊆
        T.edgeFinset.filter (fun f => ell ≤ symmetricGaugeEdgeWeight p f) := by
      intro f hf
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
      exact Finset.mem_filter.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr (e i).property, he (Finset.mem_Iic.mp hi)⟩
    have hc := Finset.card_mono hsub
    rw [Finset.card_image_of_injective _ hg, Fin.card_Iic] at hc
    exact hc
  have hcomp := treeBelow_component_count T hT.1 (symmetricGaugeEdgeWeight p) ell
  have hcount : j.val + 2 ≤
      Nat.card (treeBelow T (symmetricGaugeEdgeWeight p) ell).ConnectedComponent := by omega
  have hcountR : ((j.val + 2 : ℕ) : ℝ) ≤
      (Nat.card (treeBelow T (symmetricGaugeEdgeWeight p) ell).ConnectedComponent : ℝ) := by
    exact_mod_cast hcount
  have hpack := mst_component_packing hd p hT hell hR hellR hp
  have hpoly : ((j.val + 2 : ℕ) : ℝ) * (ell / 2) ^ (d - 1) ≤
      (3 * R / 2) ^ (d - 1) :=
    (mul_le_mul_of_nonneg_right hcountR
      (pow_nonneg (div_nonneg hell (by norm_num : (0 : ℝ) ≤ 2)) _)).trans hpack
  have hbound := radius_bound_of_packing_power
    (by positivity : (0 : ℝ) < ((j.val + 2 : ℕ) : ℝ))
    (div_nonneg hell (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : (0 : ℝ) ≤ 3 * R / 2) (by omega : d - 1 ≠ 0) hpoly
  change ell ≤ _
  nlinarith

theorem prod_successive_rpow (r : ℕ) (a : ℝ) :
    (∏ j : Fin r, (((j.val + 2 : ℕ) : ℝ) ^ a)) = ((r + 1).factorial : ℝ) ^ a := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.prod_univ_castSucc]
    change (∏ j : Fin r, (((j.val + 2 : ℕ) : ℝ) ^ a)) *
      (((r + 2 : ℕ) : ℝ) ^ a) = ((r + 1 + 1).factorial : ℝ) ^ a
    have hfac : ((r + 1 + 1).factorial : ℝ) =
        ((r + 2 : ℕ) : ℝ) * ((r + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_succ (r + 1)
    rw [ih, ← Real.mul_rpow (by positivity) (by positivity), hfac]
    congr 1
    ring

theorem mst_edge_product_bound (hd : 2 ≤ d) (p : V → FloorSpace (Fin d))
    {T : SimpleGraph V} [Fintype T.edgeSet]
    (hT : IsMinimumSpanningTree (symmetricGaugeEdgeWeight p) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hp : ∀ a, symmetricFloorGauge (p a) ≤ R)
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
        (fun j _ => mst_sorted_edge_bound hd p hT hR hp hpair e he j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, prod_successive_rpow]

theorem parentEdgeWidth_eq_symmetric_weight {d r : ℕ} [NeZero d]
    (f : Fin (r + 1) → FloorSpace (Fin d))
    (σ : Equiv.Perm (Fin (r + 1))) (parent : EarlierParent r) (j : Fin r) :
    parentEdgeWidth (fun k => f (σ k)) parent j =
      symmetricGaugeEdgeWeight f (rootedParentEdge σ parent j) := by
  simp only [parentEdgeWidth, parentEdgeUpper, parentEdgeReverse,
    rootedParentEdge, symmetricGaugeEdgeWeight_mk, symmetricFloorGauge,
    Fintype.card_fin, Submodule.coe_sub, PiLp.sub_apply]
  congr 2
  funext i
  ring

end Antichain
