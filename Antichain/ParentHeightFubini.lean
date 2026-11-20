import Antichain.ParentHeightCoordinates
import Mathlib.MeasureTheory.Integral.Prod

/-! Leaf-to-root integration of actual parent-height intervals. The product
of widths is obtained by Fubini, without a parent-difference Jacobian. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal

def earlierHeights {n : ℕ} (h : Fin n → ℝ) (j : Fin n) : Fin j.val → ℝ :=
  fun k => h ⟨k.val, k.isLt.trans j.isLt⟩

theorem measurable_earlierHeights {n : ℕ} (j : Fin n) :
    Measurable (fun h : Fin n → ℝ => earlierHeights h j) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

def sequentialIntervalRegion {n : ℕ}
    (a : (j : Fin n) → (Fin j.val → ℝ) → ℝ) (w : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {h | ∀ j, h j ∈ Icc (a j (earlierHeights h j)) (a j (earlierHeights h j) + w j)}

theorem measurableSet_sequentialIntervalRegion {n : ℕ}
    (a : (j : Fin n) → (Fin j.val → ℝ) → ℝ) (w : Fin n → ℝ)
    (ha : ∀ j, Measurable (a j)) : MeasurableSet (sequentialIntervalRegion a w) := by
  change MeasurableSet {h : Fin n → ℝ | ∀ j,
    a j (earlierHeights h j) ≤ h j ∧ h j ≤ a j (earlierHeights h j) + w j}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_le ((ha j).comp (measurable_earlierHeights j))
    (measurable_pi_apply j)).inter
    (measurableSet_le (measurable_pi_apply j)
      (((ha j).comp (measurable_earlierHeights j)).add_const (w j)))

@[simp] theorem earlierHeights_snoc_castSucc {n : ℕ} (h : Fin n → ℝ) (s : ℝ)
    (j : Fin n) : earlierHeights (Fin.snoc h s) j.castSucc = earlierHeights h j := by
  funext k
  change @Fin.snoc n (fun _ => ℝ) h s (Fin.castSucc ⟨k.val, k.isLt.trans j.isLt⟩) = _
  simp only [Fin.snoc_castSucc]
  rfl

@[simp] theorem earlierHeights_snoc_last {n : ℕ} (h : Fin n → ℝ) (s : ℝ) :
    earlierHeights (Fin.snoc h s) (Fin.last n) = h := by
  funext k
  change @Fin.snoc n (fun _ => ℝ) h s k.castSucc = h k
  simp only [Fin.snoc_castSucc]

theorem snoc_mem_sequentialIntervalRegion_iff {n : ℕ}
    (a : (j : Fin (n + 1)) → (Fin j.val → ℝ) → ℝ) (w : Fin (n + 1) → ℝ)
    (h : Fin n → ℝ) (s : ℝ) :
    Fin.snoc h s ∈ sequentialIntervalRegion a w ↔
      h ∈ sequentialIntervalRegion (fun j => a j.castSucc) (fun j => w j.castSucc) ∧
        s ∈ Icc (a (Fin.last n) h) (a (Fin.last n) h + w (Fin.last n)) := by
  simp only [sequentialIntervalRegion, Set.mem_setOf_eq, Fin.forall_fin_succ',
    earlierHeights_snoc_castSucc, earlierHeights_snoc_last, Fin.snoc_castSucc, Fin.snoc_last]

/-- Integrate the last leaf interval and repeat. Its location may depend
measurably on all earlier heights; its width is the fixed number w_j. -/
theorem volume_sequentialIntervalRegion {n : ℕ}
    (a : (j : Fin n) → (Fin j.val → ℝ) → ℝ) (w : Fin n → ℝ)
    (ha : ∀ j, Measurable (a j)) :
    (volume : Measure (Fin n → ℝ)) (sequentialIntervalRegion a w) =
      ∏ j, ENNReal.ofReal (w j) := by
  classical
  induction n with
  | zero =>
    have hset : sequentialIntervalRegion a w = Set.univ := by
      ext h
      simp [sequentialIntervalRegion]
    rw [hset]
    change (Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))) Set.univ = _
    rw [Measure.pi_empty_univ]
    simp
  | succ n ih =>
    let a₀ : (j : Fin n) → (Fin j.val → ℝ) → ℝ := fun j => a j.castSucc
    let w₀ : Fin n → ℝ := fun j => w j.castSucc
    let R := sequentialIntervalRegion a w
    let R₀ := sequentialIntervalRegion a₀ w₀
    have hR : MeasurableSet R := measurableSet_sequentialIntervalRegion a w ha
    have hR₀ : MeasurableSet R₀ :=
      measurableSet_sequentialIntervalRegion a₀ w₀ (fun j => ha j.castSucc)
    let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm
    have he : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm _
    have he_apply (s : ℝ) (h : Fin n → ℝ) : e (s, h) = Fin.snoc h s := by
      change @Fin.insertNth n (fun _ => ℝ) (Fin.last n) s h =
        @Fin.snoc n (fun _ => ℝ) h s
      exact @Fin.insertNth_last' n ℝ s h
    have hfiber (h : Fin n → ℝ) :
        (fun s : ℝ => (s, h)) ⁻¹' (e ⁻¹' R) =
          if h ∈ R₀ then Icc (a (Fin.last n) h) (a (Fin.last n) h + w (Fin.last n)) else ∅ := by
      ext s
      simp only [Set.mem_preimage, he_apply, R, snoc_mem_sequentialIntervalRegion_iff]
      change (h ∈ R₀ ∧ s ∈ _) ↔ _
      split_ifs <;> simp_all
    have hfiber_volume (h : Fin n → ℝ) :
        (volume : Measure ℝ) ((fun s : ℝ => (s, h)) ⁻¹' (e ⁻¹' R)) =
          R₀.indicator (fun _ => ENNReal.ofReal (w (Fin.last n))) h := by
      rw [hfiber]
      split_ifs with hh
      · rw [Real.volume_Icc, Set.indicator_of_mem hh]
        congr 1
        ring
      · simp [Set.indicator_of_notMem hh]
    calc
      (volume : Measure (Fin (n + 1) → ℝ)) R =
          (volume : Measure (ℝ × (Fin n → ℝ))) (e ⁻¹' R) :=
        (he.measure_preimage hR.nullMeasurableSet).symm
      _ = ∫⁻ h : Fin n → ℝ,
          (volume : Measure ℝ) ((fun s : ℝ => (s, h)) ⁻¹' (e ⁻¹' R)) := by
        rw [Measure.volume_eq_prod, Measure.prod_apply_symm (e.measurable hR)]
      _ = ENNReal.ofReal (w (Fin.last n)) * (volume : Measure (Fin n → ℝ)) R₀ := by
        simp_rw [hfiber_volume]
        exact lintegral_indicator_const hR₀ _
      _ = ∏ j, ENNReal.ofReal (w j) := by
        rw [ih a₀ w₀ (fun j => ha j.castSucc), Fin.prod_univ_castSucc]
        exact mul_comm _ _

theorem zeroCons_earlierHeights {n : ℕ} (h : Fin n → ℝ) (j : Fin n)
    (p : Fin (j.val + 1)) :
    (Fin.cons (0 : ℝ) (earlierHeights h j) : Fin (j.val + 1) → ℝ) p =
      (Fin.cons (0 : ℝ) h : Fin (n + 1) → ℝ) ⟨p.val, by omega⟩ := by
  refine Fin.cases ?_ (fun k => ?_) p
  · simp
  · simp only [Fin.cons_succ, earlierHeights]
    rfl

def parentIntervalLower {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (f : Fin (r + 1) → FloorSpace ι) (parent : EarlierParent r)
    (j : Fin r) (h : Fin j.val → ℝ) : ℝ :=
  (Fin.cons (0 : ℝ) h : Fin (j.val + 1) → ℝ) (parent j) - parentEdgeReverse f parent j

theorem measurable_parentIntervalLower {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (f : Fin (r + 1) → FloorSpace ι) (parent : EarlierParent r) (j : Fin r) :
    Measurable (parentIntervalLower f parent j) := by
  have hcons : Measurable (fun h : Fin j.val → ℝ =>
      (Fin.cons (0 : ℝ) h : Fin (j.val + 1) → ℝ)) := by
    apply measurable_pi_lambda
    intro p
    refine Fin.cases ?_ (fun k => ?_) p
    · exact measurable_const
    · exact measurable_pi_apply k
  exact ((measurable_pi_apply (parent j)).comp hcons).sub_const _

/-- Exactly the revised written leaf-to-root Fubini upper bound: after all
non-tree constraints are discarded, integrating each last leaf gives its
edge interval width. No determinant or height-difference change of variables
is used in this theorem. -/
theorem pinnedHeightFiber_volume_le_parentWidth_fubini
    {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (f : Fin (r + 1) → FloorSpace ι) (parent : EarlierParent r) :
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) ≤
      ∏ j, ENNReal.ofReal (parentEdgeWidth f parent j) := by
  have hsub : pinnedHeightFiber f ⊆
      sequentialIntervalRegion (parentIntervalLower f parent) (parentEdgeWidth f parent) := by
    intro h hh j
    have hj := parentDifference_mem_box f parent hh j (Set.mem_univ j)
    change -parentEdgeReverse f parent j ≤ parentDifferenceMap parent h j ∧
      parentDifferenceMap parent h j ≤ parentEdgeUpper f parent j at hj
    change parentIntervalLower f parent j (earlierHeights h j) ≤ h j ∧
      h j ≤ parentIntervalLower f parent j (earlierHeights h j) + parentEdgeWidth f parent j
    simp only [parentIntervalLower, zeroCons_earlierHeights, parentEdgeWidth]
    simp only [parentDifferenceMap_apply, parentLabel] at hj
    constructor <;> linarith
  calc
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) ≤
        volume (sequentialIntervalRegion (parentIntervalLower f parent)
          (parentEdgeWidth f parent)) := measure_mono hsub
    _ = _ := volume_sequentialIntervalRegion _ _ (measurable_parentIntervalLower f parent)

end Antichain
