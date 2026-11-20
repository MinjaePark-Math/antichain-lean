import Antichain.BoundaryProfiles
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The symmetric gauge norm and the exact two-point height-interval width. -/

noncomputable section

namespace Antichain

open Finset Set MeasureTheory
open scoped Topology

theorem heightGauge_neg_eq_mul_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ℝ) (hs : 0 ≤ s) (u : ι → ℝ) :
    heightGauge s (fun i ↦ -u i) = s * Finset.univ.sup' Finset.univ_nonempty u := by
  apply le_antisymm
  · apply (heightGauge_le_iff _ _ _).mpr
    intro i
    have h := mul_le_mul_of_nonneg_left (Finset.le_sup' u (Finset.mem_univ i)) hs
    simpa only [neg_mul_neg] using h
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty u
    rw [hi]
    simpa only [neg_mul_neg] using neg_mul_le_heightGauge s (fun i ↦ -u i) i

variable {d : ℕ} [NeZero d]

def symmetricFloorGauge (u : FloorSpace (Fin d)) : ℝ :=
  heightGauge (Real.sqrt (d : ℝ)) (fun i ↦ u.val i) +
    heightGauge (Real.sqrt (d : ℝ)) (fun i ↦ -u.val i)

theorem symmetricFloorGauge_formula (u : FloorSpace (Fin d)) :
    symmetricFloorGauge u = Real.sqrt (d : ℝ) *
      (Finset.univ.sup' Finset.univ_nonempty (fun i ↦ u.val i) -
        Finset.univ.inf' Finset.univ_nonempty (fun i ↦ u.val i)) := by
  rw [symmetricFloorGauge, heightGauge_eq_neg_mul_min _ (Real.sqrt_nonneg _),
    heightGauge_neg_eq_mul_max _ (Real.sqrt_nonneg _)]
  ring

theorem symmetricFloorGauge_nonneg (u : FloorSpace (Fin d)) : 0 ≤ symmetricFloorGauge u := by
  have hu : ∑ i : Fin d, u.val i = 0 := u.property
  apply add_nonneg (heightGauge_nonneg _ _ hu)
  apply heightGauge_nonneg
  simp only [Finset.sum_neg_distrib, hu, neg_zero]

@[simp] theorem symmetricFloorGauge_zero : symmetricFloorGauge (0 : FloorSpace (Fin d)) = 0 := by
  simp [symmetricFloorGauge]

@[simp] theorem symmetricFloorGauge_neg (u : FloorSpace (Fin d)) :
    symmetricFloorGauge (-u) = symmetricFloorGauge u := by
  simp [symmetricFloorGauge, add_comm]

theorem symmetricFloorGauge_add_le (u v : FloorSpace (Fin d)) :
    symmetricFloorGauge (u + v) ≤ symmetricFloorGauge u + symmetricFloorGauge v := by
  have h1 := heightGauge_add_le (Real.sqrt (d : ℝ)) (fun i ↦ u.val i) (fun i ↦ v.val i)
  have h2 := heightGauge_add_le (Real.sqrt (d : ℝ)) (fun i ↦ -u.val i) (fun i ↦ -v.val i)
  have heq : (fun i ↦ -(u.val i + v.val i)) = (fun i ↦ -u.val i + -v.val i) := by
    funext i
    ring
  change heightGauge _ (fun i ↦ u.val i + v.val i) +
    heightGauge _ (fun i ↦ -(u.val i + v.val i)) ≤ _
  rw [heq]
  dsimp [symmetricFloorGauge]
  linarith

theorem symmetricFloorGauge_smul_nonneg (t : ℝ) (ht : 0 ≤ t) (u : FloorSpace (Fin d)) :
    symmetricFloorGauge (t • u) = t * symmetricFloorGauge u := by
  have heq : (fun i ↦ -(t * u.val i)) = (fun i ↦ t * -u.val i) := by
    funext i
    ring
  change heightGauge _ (fun i ↦ t * u.val i) +
    heightGauge _ (fun i ↦ -(t * u.val i)) = _
  rw [heq, heightGauge_smul _ t ht, heightGauge_smul _ t ht]
  dsimp [symmetricFloorGauge]
  ring

theorem symmetricFloorGauge_smul (t : ℝ) (u : FloorSpace (Fin d)) :
    symmetricFloorGauge (t • u) = |t| * symmetricFloorGauge u := by
  by_cases ht : 0 ≤ t
  · rw [symmetricFloorGauge_smul_nonneg t ht, abs_of_nonneg ht]
  · have ht' : 0 ≤ -t := by linarith
    have heq : t • u = -((-t) • u) := by simp
    rw [heq, symmetricFloorGauge_neg, symmetricFloorGauge_smul_nonneg (-t) ht',
      abs_of_neg (lt_of_not_ge ht)]

theorem symmetricFloorGauge_eq_zero_iff (hd : 2 ≤ d) (u : FloorSpace (Fin d)) :
    symmetricFloorGauge u = 0 ↔ u = 0 := by
  constructor
  · intro hzero
    have hu : ∑ i : Fin d, u.val i = 0 := u.property
    have hneg : 0 ≤ heightGauge (Real.sqrt (d : ℝ)) (fun i ↦ -u.val i) := by
      apply heightGauge_nonneg
      simp only [Finset.sum_neg_distrib, hu, neg_zero]
    have hlo := (heightGauge_norm_bounds_euclidean (ι := Fin d)
      (by simpa only [Fintype.card_fin] using hd) (fun i ↦ u.val i) u.property).1
    simp only [Fintype.card_fin] at hlo
    change ‖u‖ / Real.sqrt ((d : ℝ) - 1) ≤ _ at hlo
    have hdiv : ‖u‖ / Real.sqrt ((d : ℝ) - 1) ≤ 0 := by
      dsimp [symmetricFloorGauge] at hzero
      linarith
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
    have hn := (div_le_iff₀ hs).mp hdiv
    exact norm_eq_zero.mp (le_antisymm (by simpa using hn) (norm_nonneg u))
  · rintro rfl
    exact symmetricFloorGauge_zero

def symmetricFloorNorm (hd : 2 ≤ d) : AddGroupNorm (FloorSpace (Fin d)) where
  toFun := symmetricFloorGauge
  map_zero' := symmetricFloorGauge_zero
  add_le' := symmetricFloorGauge_add_le
  neg' := symmetricFloorGauge_neg
  eq_zero_of_map_eq_zero' := fun u hu ↦ (symmetricFloorGauge_eq_zero_iff hd u).mp hu

def allowedHeightDifference (u : FloorSpace (Fin d)) : Set ℝ :=
  {t | ¬ StrictBelow (fun i ↦ u.val i + t / Real.sqrt (d : ℝ)) (fun _ ↦ 0) ∧
    ¬ StrictBelow (fun _ ↦ 0) (fun i ↦ u.val i + t / Real.sqrt (d : ℝ))}

theorem allowedHeightDifference_eq_interval (u : FloorSpace (Fin d)) :
    allowedHeightDifference u =
      Icc (-heightGauge (Real.sqrt (d : ℝ)) (fun i ↦ -u.val i))
        (heightGauge (Real.sqrt (d : ℝ)) (fun i ↦ u.val i)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hs := Real.sqrt_pos.mpr hdR
  ext t
  have h1 := all_coordinates_lt_iff_heightGauge_lt (Real.sqrt (d : ℝ)) hs
    (fun _ : Fin d ↦ 0) (fun i ↦ u.val i) 0 t
  have h2 := all_coordinates_lt_iff_heightGauge_lt (Real.sqrt (d : ℝ)) hs
    (fun i ↦ u.val i) (fun _ : Fin d ↦ 0) t 0
  simp only [zero_div, zero_add, zero_sub, sub_zero] at h1 h2
  change (¬ (∀ i, u.val i + t / Real.sqrt (d : ℝ) < 0) ∧
    ¬ (∀ i, 0 < u.val i + t / Real.sqrt (d : ℝ))) ↔ _
  rw [h1, h2]
  simp only [not_lt, Set.mem_Icc]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

/-- The width is literal one-dimensional Lebesgue length, including a collapsed interval. -/
theorem allowedHeightDifference_volume (u : FloorSpace (Fin d)) :
    volume (allowedHeightDifference u) = ENNReal.ofReal (symmetricFloorGauge u) := by
  rw [allowedHeightDifference_eq_interval, Real.volume_Icc]
  congr 1
  dsimp [symmetricFloorGauge]
  ring

theorem symmetric_gauge_source (hd : 2 ≤ d) :
    (∀ u : FloorSpace (Fin d), symmetricFloorNorm hd u =
      heightGauge (Real.sqrt (d : ℝ)) (fun i ↦ u.val i) +
        heightGauge (Real.sqrt (d : ℝ)) (fun i ↦ -u.val i)) ∧
    (∀ t u, symmetricFloorNorm hd (t • u) = |t| * symmetricFloorNorm hd u) ∧
    (∀ u : FloorSpace (Fin d), symmetricFloorNorm hd u = Real.sqrt (d : ℝ) *
      (Finset.univ.sup' Finset.univ_nonempty (fun i ↦ u.val i) -
        Finset.univ.inf' Finset.univ_nonempty (fun i ↦ u.val i))) ∧
    ∀ u : FloorSpace (Fin d), volume (allowedHeightDifference u) =
      ENNReal.ofReal (symmetricFloorNorm hd u) :=
  ⟨fun _ ↦ rfl, symmetricFloorGauge_smul, symmetricFloorGauge_formula, allowedHeightDifference_volume⟩

end Antichain
