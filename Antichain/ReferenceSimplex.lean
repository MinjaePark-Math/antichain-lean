import Antichain.FloorSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The actual closed reference alcove in the Euclidean zero-sum floor. -/

noncomputable section

namespace Antichain

open Finset MeasureTheory
open scoped Topology ENNReal

/-- The paper's reference simplex. Using every coordinate difference avoids
choosing a first or last coordinate when the dimension is zero. -/
def referenceSimplex (d : ℕ) : Set (FloorSpace (Fin d)) :=
  {x | Antitone (fun i : Fin d ↦ x.val i) ∧ ∀ i j : Fin d, x.val i - x.val j ≤ 1}

/-- A strict open core of the same simplex. -/
def referenceSimplexCore (d : ℕ) : Set (FloorSpace (Fin d)) :=
  {x | (∀ i j : Fin d, i < j → x.val j < x.val i) ∧
    ∀ i j : Fin d, x.val i - x.val j < 1}

theorem continuous_floor_coordinate {d : ℕ} (i : Fin d) :
    Continuous (fun x : FloorSpace (Fin d) ↦ x.val i) :=
  (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i).comp continuous_subtype_val

theorem isClosed_referenceSimplex (d : ℕ) : IsClosed (referenceSimplex d) := by
  classical
  unfold referenceSimplex Antitone
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
    isClosed_le (continuous_floor_coordinate j) (continuous_floor_coordinate i)).inter
      (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
        isClosed_le ((continuous_floor_coordinate i).sub (continuous_floor_coordinate j)) continuous_const)

theorem isOpen_referenceSimplexCore (d : ℕ) : IsOpen (referenceSimplexCore d) := by
  classical
  unfold referenceSimplexCore
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
    isOpen_lt (continuous_floor_coordinate j) (continuous_floor_coordinate i)).inter
      (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
        isOpen_lt ((continuous_floor_coordinate i).sub (continuous_floor_coordinate j)) continuous_const)

theorem referenceSimplexCore_subset (d : ℕ) : referenceSimplexCore d ⊆ referenceSimplex d := by
  rintro x ⟨hs, hd⟩
  refine ⟨fun i j hij ↦ ?_, fun i j ↦ (hd i j).le⟩
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact (hs i j hlt).le
  · rw [heq]

/-- The all-differences condition is exactly the first-minus-last condition in
the ordered chamber, including its boundary. -/
theorem referenceSimplex_iff_first_last {d : ℕ} (x : FloorSpace (Fin (d + 1))) :
    x ∈ referenceSimplex (d + 1) ↔
      Antitone (fun i : Fin (d + 1) ↦ x.val i) ∧ x.val 0 - x.val (Fin.last d) ≤ 1 := by
  constructor
  · rintro ⟨hs, hd⟩
    exact ⟨hs, hd 0 (Fin.last d)⟩
  · rintro ⟨hs, hd⟩
    refine ⟨hs, fun i j ↦ ?_⟩
    have hi := hs (Fin.zero_le i)
    have hj := hs (Fin.le_last j)
    linarith

/-- Every coordinate lies in [-1,1], using the actual zero-sum condition. -/
theorem referenceSimplex_coordinate_bounds {d : ℕ} (hd : 0 < d)
    {x : FloorSpace (Fin d)} (hx : x ∈ referenceSimplex d) (i : Fin d) :
    -1 ≤ x.val i ∧ x.val i ≤ 1 := by
  have hsum : ∑ j : Fin d, x.val j = 0 := x.property
  have hup := Finset.sum_le_sum (fun (j : Fin d) (_ : j ∈ Finset.univ) ↦ hx.2 i j)
  have hlo := Finset.sum_le_sum (fun (j : Fin d) (_ : j ∈ Finset.univ) ↦ hx.2 j i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hsum, sub_zero, zero_sub, mul_one] at hup hlo
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor <;> nlinarith

theorem norm_le_dimension_of_mem_referenceSimplex {d : ℕ} (hd : 2 ≤ d)
    {x : FloorSpace (Fin d)} (hx : x ∈ referenceSimplex d) : ‖x‖ ≤ (d : ℝ) := by
  have hb (i : Fin d) : (x.val i) ^ 2 ≤ 1 := by
    obtain ⟨hl, hu⟩ := referenceSimplex_coordinate_bounds (by omega) hx i
    nlinarith
  have hsum := Finset.sum_le_sum (fun (i : Fin d) (_ : i ∈ Finset.univ) ↦ hb i)
  have hnorm := EuclideanSpace.norm_sq_eq x.val
  simp only [Real.norm_eq_abs, sq_abs] at hnorm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  change ‖x.val‖ ≤ (d : ℝ)
  nlinarith [norm_nonneg x.val]

theorem isBounded_referenceSimplex {d : ℕ} (hd : 2 ≤ d) :
    Bornology.IsBounded (referenceSimplex d) :=
  (isBounded_iff_forall_norm_le).mpr ⟨(d : ℝ), fun _ hx ↦ norm_le_dimension_of_mem_referenceSimplex hd hx⟩

theorem isCompact_referenceSimplex {d : ℕ} (hd : 2 ≤ d) :
    IsCompact (referenceSimplex d) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_referenceSimplex d, isBounded_referenceSimplex hd⟩

/-- Center a strictly descending arithmetic progression of spread less than 1/2.
This point belongs to the actual Euclidean zero-sum floor by construction. -/
def referenceSimplexInteriorPoint (d : ℕ) [NeZero d] : FloorSpace (Fin d) :=
  centeredFloor (WithLp.toLp 2 (fun i : Fin d ↦ -(i.val : ℝ) / (2 * (d : ℝ))))

theorem referenceSimplexInteriorPoint_mem_core (d : ℕ) [NeZero d] :
    referenceSimplexInteriorPoint d ∈ referenceSimplexCore d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hden : (0 : ℝ) < 2 * (d : ℝ) := by positivity
  let μ : ℝ := (∑ j : Fin d, -(j.val : ℝ) / (2 * (d : ℝ))) / (d : ℝ)
  have hcoord (i : Fin d) : (referenceSimplexInteriorPoint d).val i =
      -(i.val : ℝ) / (2 * (d : ℝ)) - μ := by
    simp [referenceSimplexInteriorPoint, centeredFloor, μ]
  constructor
  · intro i j hij
    rw [hcoord j, hcoord i]
    simp only [neg_div]
    have hijR : (i.val : ℝ) < j.val := by exact_mod_cast hij
    have hdiv := div_lt_div_of_pos_right hijR hden
    linarith
  · intro i j
    rw [hcoord i, hcoord j]
    have heq : (-(i.val : ℝ) / (2 * (d : ℝ)) - μ) -
        (-(j.val : ℝ) / (2 * (d : ℝ)) - μ) =
          ((j.val : ℝ) - (i.val : ℝ)) / (2 * (d : ℝ)) := by ring
    rw [heq]
    apply (div_lt_iff₀ hden).mpr
    have hj : (j.val : ℝ) < d := by exact_mod_cast j.isLt
    have hi : (0 : ℝ) ≤ i.val := by positivity
    nlinarith

theorem referenceSimplexCore_nonempty {d : ℕ} (hd : 2 ≤ d) :
    (referenceSimplexCore d).Nonempty := by
  letI : NeZero d := ⟨by omega⟩
  exact ⟨referenceSimplexInteriorPoint d, referenceSimplexInteriorPoint_mem_core d⟩

/-- The reference simplex has nonempty interior in the native floor topology. -/
theorem referenceSimplex_interior_nonempty {d : ℕ} (hd : 2 ≤ d) :
    (interior (referenceSimplex d)).Nonempty :=
  (referenceSimplexCore_nonempty hd).mono
    ((isOpen_referenceSimplexCore d).subset_interior_iff.mpr (referenceSimplexCore_subset d))

theorem measurableSet_referenceSimplex (d : ℕ) : MeasurableSet (referenceSimplex d) :=
  (isClosed_referenceSimplex d).measurableSet

/-- The reference simplex has strictly positive actual induced Euclidean volume. -/
theorem floorVolume_referenceSimplex_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < floorVolume (referenceSimplex d) := by
  change 0 < (volume : Measure (FloorSpace (Fin d))) (referenceSimplex d)
  exact Measure.measure_pos_of_nonempty_interior volume (referenceSimplex_interior_nonempty hd)

/-- Compactness gives finiteness for the actual induced Euclidean measure. -/
theorem floorVolume_referenceSimplex_lt_top {d : ℕ} (hd : 2 ≤ d) :
    floorVolume (referenceSimplex d) < ⊤ := by
  change (volume : Measure (FloorSpace (Fin d))) (referenceSimplex d) < ⊤
  exact (isCompact_referenceSimplex hd).measure_lt_top

theorem floorVolume_referenceSimplex_toReal_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < (floorVolume (referenceSimplex d)).toReal :=
  ENNReal.toReal_pos (floorVolume_referenceSimplex_pos hd).ne'
    (floorVolume_referenceSimplex_lt_top hd).ne

end Antichain
