import Antichain.HeightCoordinates
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Lean.Elab.Tactic.Omega

/-!
Actual parent-difference coordinates on pinned heights. A parent is typed to
occur before its child, so the matrix is lower triangular with diagonal one.
Its measure law and the product-interval fiber bound are proved, not assumed.
-/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal

abbrev EarlierParent (r : ℕ) := (j : Fin r) → Fin (j.val + 1)

def parentLabel {r : ℕ} (parent : EarlierParent r) (j : Fin r) : Fin (r + 1) :=
  ⟨(parent j).val, by have hp := (parent j).isLt; have hj := j.isLt; omega⟩

theorem parentLabel_lt_child {r : ℕ} (parent : EarlierParent r) (j : Fin r) :
    parentLabel parent j < j.succ := (parent j).isLt

def zeroConsLinear (r : ℕ) : (Fin r → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun h := Fin.cons 0 h
  map_add' h k := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a h := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Free child height minus its earlier parent's pinned height. -/
def parentDifferenceMap {r : ℕ} (parent : EarlierParent r) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun h j := h j - zeroConsLinear r h (parentLabel parent j)
  map_add' h k := by
    funext j
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' a h := by
    funext j
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem parentDifferenceMap_apply {r : ℕ} (parent : EarlierParent r)
    (h : Fin r → ℝ) (j : Fin r) :
    parentDifferenceMap parent h j =
      h j - (Fin.cons (0 : ℝ) h : Fin (r + 1) → ℝ) (parentLabel parent j) := rfl

theorem zeroConsLinear_single_apply {r : ℕ} (k : Fin r) (i : Fin (r + 1)) :
    zeroConsLinear r (Pi.single k 1) i = if i = k.succ then 1 else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [zeroConsLinear, (Fin.succ_ne_zero k).symm]
  · simp [zeroConsLinear, Pi.single_apply, eq_comm]

def parentDifferenceMatrix {r : ℕ} (parent : EarlierParent r) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => (if j = k then 1 else 0) -
    (if parentLabel parent j = k.succ then 1 else 0)

theorem parentDifferenceMap_toMatrix {r : ℕ} (parent : EarlierParent r) :
    LinearMap.toMatrix' (parentDifferenceMap parent) = parentDifferenceMatrix parent := by
  ext j k
  rw [LinearMap.toMatrix'_apply]
  have hsingle : (fun j' : Fin r => if j' = k then (1 : ℝ) else 0) = Pi.single k 1 := by
    funext j'
    simp [Pi.single_apply, eq_comm]
  rw [hsingle]
  change (Pi.single k (1 : ℝ) : Fin r → ℝ) j -
    zeroConsLinear r (Pi.single k 1) (parentLabel parent j) = _
  rw [zeroConsLinear_single_apply]
  simp [parentDifferenceMatrix, Pi.single_apply]

theorem parentDifferenceMatrix_diagonal {r : ℕ} (parent : EarlierParent r) (j : Fin r) :
    parentDifferenceMatrix parent j j = 1 := by
  have hp : parentLabel parent j ≠ j.succ := (parentLabel_lt_child parent j).ne
  simp [parentDifferenceMatrix, hp]

theorem parentDifferenceMatrix_lowerTriangular {r : ℕ} (parent : EarlierParent r) :
    (parentDifferenceMatrix parent).BlockTriangular OrderDual.toDual := by
  intro j k hjk
  have hlt : j < k := hjk
  have hne : j ≠ k := hlt.ne
  have hp : parentLabel parent j ≠ k.succ := by
    have hpar := parentLabel_lt_child parent j
    intro heq
    have hv := congrArg Fin.val heq
    change (parent j).val = k.val + 1 at hv
    have hpj := (parent j).isLt
    have hjkval : j.val < k.val := hlt
    omega
  simp [parentDifferenceMatrix, hne, hp]

theorem parentDifferenceMap_det {r : ℕ} (parent : EarlierParent r) :
    LinearMap.det (parentDifferenceMap parent) = 1 := by
  rw [← LinearMap.det_toMatrix', parentDifferenceMap_toMatrix,
    Matrix.det_of_lowerTriangular _ (parentDifferenceMatrix_lowerTriangular parent)]
  simp only [parentDifferenceMatrix_diagonal, Finset.prod_const_one]

/-- The parent-edge change of free coordinates preserves actual Lebesgue
volume, by its proved determinant one. -/
theorem parentDifferenceMap_measurePreserving {r : ℕ} (parent : EarlierParent r) :
    MeasurePreserving (parentDifferenceMap parent)
      (volume : Measure (Fin r → ℝ)) volume := by
  refine ⟨(parentDifferenceMap parent).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_pi_eq_smul_addHaar
    (by rw [parentDifferenceMap_det]; exact one_ne_zero), parentDifferenceMap_det]
  simp

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def parentEdgeUpper {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) (j : Fin r) : ℝ :=
  heightGauge (Real.sqrt (Fintype.card ι : ℝ))
    (fun i => (f j.succ).val i - (f (parentLabel parent j)).val i)

def parentEdgeReverse {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) (j : Fin r) : ℝ :=
  heightGauge (Real.sqrt (Fintype.card ι : ℝ))
    (fun i => (f (parentLabel parent j)).val i - (f j.succ).val i)

def parentEdgeWidth {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) (j : Fin r) : ℝ :=
  parentEdgeUpper f parent j + parentEdgeReverse f parent j

def parentHeightBox {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) : Set (Fin r → ℝ) :=
  Set.univ.pi (fun j => Icc (-parentEdgeReverse f parent j) (parentEdgeUpper f parent j))

theorem measurableSet_parentHeightBox {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) : MeasurableSet (parentHeightBox f parent) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- Every actual pinned antichain obeys the ordered parent/child intervals. -/
theorem parentDifference_mem_box {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) {h : Fin r → ℝ} (hh : h ∈ pinnedHeightFiber f) :
    parentDifferenceMap parent h ∈ parentHeightBox f parent := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc := (isAntichain_iff_height_constraints _ (Real.sqrt_pos.mpr hcard)
    (fun k i => (f k).val i) (Fin.cons (0 : ℝ) h)).mp hh
  intro j _
  have hu := hc j.succ (parentLabel parent j)
  have hl := hc (parentLabel parent j) j.succ
  simp only [Fin.cons_succ] at hu hl
  constructor
  · change -parentEdgeReverse f parent j ≤ parentDifferenceMap parent h j
    change -(heightGauge _ _) ≤ h j - (Fin.cons (0 : ℝ) h : Fin (r + 1) → ℝ)
      (parentLabel parent j)
    linarith
  · exact hu

/-- The interval length is the sum of the two directed gauges. -/
theorem volume_parentHeightBox {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) :
    (volume : Measure (Fin r → ℝ)) (parentHeightBox f parent) =
      ∏ j, ENNReal.ofReal (parentEdgeWidth f parent j) := by
  change (Measure.pi (fun _ : Fin r => (volume : Measure ℝ)))
    (Set.univ.pi (fun j => Icc (-parentEdgeReverse f parent j) (parentEdgeUpper f parent j))) = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, parentEdgeWidth]

/-- Actual pinned-height volume is bounded by the product of its parent-edge
widths. The rooted ordering is typed data, not an assumed Jacobian theorem. -/
theorem pinnedHeightFiber_volume_le_parentWidth {r : ℕ}
    (f : Fin (r + 1) → FloorSpace ι) (parent : EarlierParent r) :
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) ≤
      ∏ j, ENNReal.ofReal (parentEdgeWidth f parent j) := by
  calc
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) ≤
        volume (parentDifferenceMap parent ⁻¹' parentHeightBox f parent) :=
      measure_mono (fun _ hh => parentDifference_mem_box f parent hh)
    _ = volume (parentHeightBox f parent) :=
      (parentDifferenceMap_measurePreserving parent).measure_preimage
        (measurableSet_parentHeightBox f parent).nullMeasurableSet
    _ = _ := volume_parentHeightBox f parent

theorem parentEdgeWidth_le_norm {r : ℕ} (hd : 2 ≤ Fintype.card ι)
    (f : Fin (r + 1) → FloorSpace ι) (parent : EarlierParent r) (j : Fin r) :
    parentEdgeWidth f parent j ≤
      2 * Real.sqrt ((Fintype.card ι : ℝ) - 1) *
        ‖f j.succ - f (parentLabel parent j)‖ := by
  have hzero (a b : Fin (r + 1)) : ∑ i, ((f a).val i - (f b).val i) = 0 := by
    have ha : ∑ i, (f a).val i = 0 := (f a).property
    have hb : ∑ i, (f b).val i = 0 := (f b).property
    rw [Finset.sum_sub_distrib, ha, hb, sub_self]
  have hu := (heightGauge_norm_bounds_euclidean hd
    (fun i => (f j.succ).val i - (f (parentLabel parent j)).val i)
    (hzero j.succ (parentLabel parent j))).2
  have hv := (heightGauge_norm_bounds_euclidean hd
    (fun i => (f (parentLabel parent j)).val i - (f j.succ).val i)
    (hzero (parentLabel parent j) j.succ)).2
  change parentEdgeUpper f parent j ≤
    Real.sqrt ((Fintype.card ι : ℝ) - 1) * ‖f j.succ - f (parentLabel parent j)‖ at hu
  change parentEdgeReverse f parent j ≤
    Real.sqrt ((Fintype.card ι : ℝ) - 1) * ‖f (parentLabel parent j) - f j.succ‖ at hv
  rw [norm_sub_rev] at hv
  unfold parentEdgeWidth
  linarith

/-- Euclidean edge-length form of the actual parent-coordinate volume bound. -/
theorem pinnedHeightFiber_volume_le_parentNorm {r : ℕ}
    (hd : 2 ≤ Fintype.card ι) (f : Fin (r + 1) → FloorSpace ι)
    (parent : EarlierParent r) :
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) ≤
      ∏ j, ENNReal.ofReal (2 * Real.sqrt ((Fintype.card ι : ℝ) - 1) *
        ‖f j.succ - f (parentLabel parent j)‖) := by
  exact (pinnedHeightFiber_volume_le_parentWidth f parent).trans
    (Finset.prod_le_prod' (fun j _ => ENNReal.ofReal_le_ofReal (parentEdgeWidth_le_norm hd f parent j)))

end Antichain
