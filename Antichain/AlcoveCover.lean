import Antichain.AffineAlcoveGroup
import Antichain.AlcoveDiscreteness
import Antichain.AlcoveTiling
import Mathlib.Order.Fin.Basic

/-! Direct folding into the actual reference alcove, without a Coxeter input. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset Metric
open scoped RealInnerProductSpace

variable {d : ℕ} [NeZero d]

def alcoveRootDirection (a b : Fin d) : FloorSpace (Fin d) :=
  ⟨EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1, by simp [coordinateSum]⟩

omit [NeZero d] in
theorem alcoveRootDirection_inner (a b : Fin d) (x : FloorSpace (Fin d)) :
    inner ℝ x (alcoveRootDirection a b) = x.val a - x.val b := by
  change inner ℝ x.val (EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1) = _
  rw [inner_sub_right, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right]
  simp

omit [NeZero d] in
theorem alcoveRootDirection_norm_sq (a b : Fin d) (hab : a ≠ b) :
    ‖alcoveRootDirection a b‖ ^ 2 = (2 : ℝ) := by
  change ‖EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1‖ ^ 2 = _
  rw [norm_sub_sq_real]
  simp [EuclideanSpace.norm_single, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, hab]
  norm_num

def affineCoordinateReflection (a b : Fin d) (t : ℝ) (x : FloorSpace (Fin d)) :
    FloorSpace (Fin d) := x + (t + x.val b - x.val a) • alcoveRootDirection a b

omit [NeZero d] in
theorem affineCoordinateReflection_dist_sq (a b : Fin d) (hab : a ≠ b)
    (t : ℝ) (x c : FloorSpace (Fin d)) :
    dist (affineCoordinateReflection a b t x) c ^ 2 = dist x c ^ 2 +
      2 * (x.val a - x.val b - t) * (c.val a - c.val b - t) := by
  rw [dist_eq_norm, dist_eq_norm]
  have heq : affineCoordinateReflection a b t x - c =
      (x - c) + (t + x.val b - x.val a) • alcoveRootDirection a b := by
    dsimp [affineCoordinateReflection]
    abel
  rw [heq, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, alcoveRootDirection_norm_sq a b hab, inner_smul_right,
    alcoveRootDirection_inner]
  simp only [Submodule.coe_sub, PiLp.sub_apply]
  ring

theorem sideReflection_eq_affine_zero (hd : 2 ≤ d) (x : FloorSpace (Fin d)) :
    sideReflection d 0 x = affineCoordinateReflection 0 (lastCoordinate d) 1 x := by
  classical
  have hlast : (0 : Fin d) ≠ lastCoordinate d := by
    intro h
    have hh := congrArg Fin.val h
    simp only [lastCoordinate, Fin.val_zero] at hh
    omega
  apply Subtype.ext
  ext j
  rw [sideReflection_zero_apply]
  change _ = x.val j + (1 + x.val (lastCoordinate d) - x.val 0) *
    ((EuclideanSpace.single 0 (1 : ℝ) - EuclideanSpace.single (lastCoordinate d) 1 :
      EuclideanSpace ℝ (Fin d)) j)
  simp only [Equiv.swap_apply_def]
  by_cases hj0 : j = 0
  · subst j
    simp_all [EuclideanSpace.single_apply]
    ring
  · by_cases hjlast : j = lastCoordinate d
    · subst j
      simp_all [EuclideanSpace.single_apply, apply_ite]
      ring
    · simp_all [EuclideanSpace.single_apply, apply_ite]

theorem previousCoordinate_lt (i : Fin d) (hi : i ≠ 0) : previousCoordinate d i < i := by
  have hpos : 0 < i.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hi
    apply Fin.ext
    simpa only [Fin.val_zero] using hz
  change i.val - 1 < i.val
  omega

theorem sideReflection_eq_affine_nonzero (i : Fin d) (hi : i ≠ 0)
    (x : FloorSpace (Fin d)) :
    sideReflection d i x = affineCoordinateReflection (previousCoordinate d i) i 0 x := by
  classical
  have hab := (previousCoordinate_lt i hi).ne
  apply Subtype.ext
  ext j
  rw [sideReflection_nonzero_apply d i hi]
  change _ = x.val j + (0 + x.val i - x.val (previousCoordinate d i)) *
    ((EuclideanSpace.single (previousCoordinate d i) (1 : ℝ) - EuclideanSpace.single i 1 :
      EuclideanSpace ℝ (Fin d)) j)
  simp only [Equiv.swap_apply_def]
  by_cases hja : j = previousCoordinate d i
  · subst j
    simp_all [EuclideanSpace.single_apply, apply_ite]
  · by_cases hjb : j = i
    · subst j
      simp_all [EuclideanSpace.single_apply, apply_ite]
    · simp_all [EuclideanSpace.single_apply, apply_ite]

theorem referenceSimplex_mem_of_side_constraints (y : FloorSpace (Fin d))
    (hadj : ∀ i : Fin d, i ≠ 0 → y.val i ≤ y.val (previousCoordinate d i))
    (hspan : y.val 0 - y.val (lastCoordinate d) ≤ 1) : y ∈ referenceSimplex d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hanti : Antitone (fun i : Fin (k + 1) => y.val i) := by
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have hi : i.succ ≠ (0 : Fin (k + 1)) := Fin.succ_ne_zero i
    have hprev : previousCoordinate (k + 1) i.succ = i.castSucc := by
      apply Fin.ext
      simp [previousCoordinate]
    simpa only [hprev] using hadj i.succ hi
  apply (referenceSimplex_iff_first_last y).mpr
  refine ⟨hanti, ?_⟩
  have hlast : lastCoordinate (k + 1) = Fin.last k := by
    apply Fin.ext
    simp [lastCoordinate]
  simpa only [hlast] using hspan

theorem closest_word_mem_referenceSimplex (hd : 2 ≤ d) (x : FloorSpace (Fin d))
    (word : List (Fin d))
    (hmin : ∀ v : List (Fin d),
      dist (reflectionWordMap d word x) (referenceSimplexInteriorPoint d) ≤
        dist (reflectionWordMap d v x) (referenceSimplexInteriorPoint d)) :
    reflectionWordMap d word x ∈ referenceSimplex d := by
  let y := reflectionWordMap d word x
  let c := referenceSimplexInteriorPoint d
  have hcore : c ∈ referenceSimplexCore d := referenceSimplexInteriorPoint_mem_core d
  have hminside (i : Fin d) : dist y c ≤ dist (sideReflection d i y) c := by
    exact hmin (i :: word)
  apply referenceSimplex_mem_of_side_constraints
  · intro i hi
    by_contra hbad
    have hy : y.val (previousCoordinate d i) - y.val i < 0 := by linarith
    have hc : 0 < c.val (previousCoordinate d i) - c.val i :=
      sub_pos.mpr (hcore.1 _ _ (previousCoordinate_lt i hi))
    have hprod := mul_neg_of_neg_of_pos hy hc
    have hs : dist y c ^ 2 ≤ dist (sideReflection d i y) c ^ 2 :=
      pow_le_pow_left₀ (dist_nonneg) (hminside i) 2
    rw [sideReflection_eq_affine_nonzero i hi,
      affineCoordinateReflection_dist_sq _ _ (previousCoordinate_lt i hi).ne] at hs
    simp only [sub_zero] at hs
    nlinarith
  · by_contra hbad
    have hy : 0 < y.val 0 - y.val (lastCoordinate d) - 1 := by linarith
    have hc : c.val 0 - c.val (lastCoordinate d) - 1 < 0 := by
      have hh := hcore.2 0 (lastCoordinate d)
      linarith
    have hprod := mul_neg_of_pos_of_neg hy hc
    have hs : dist y c ^ 2 ≤ dist (sideReflection d 0 y) c ^ 2 :=
      pow_le_pow_left₀ (dist_nonneg) (hminside 0) 2
    have hlast : (0 : Fin d) ≠ lastCoordinate d := by
      intro h
      have hh := congrArg Fin.val h
      simp only [lastCoordinate, Fin.val_zero] at hh
      omega
    rw [sideReflection_eq_affine_zero hd,
      affineCoordinateReflection_dist_sq _ _ hlast] at hs
    nlinarith

/-- Every actual floor point is in an actual side-reflection image of Δ. -/
theorem alcoveTile_covers_direct (hd : 2 ≤ d) :
    (⋃ t : AlcoveTile d, (t : Set (FloorSpace (Fin d)))) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨word, hmin⟩ := reflectionWordOrbit_has_dist_minimizer d x (referenceSimplexInteriorPoint d)
  have hy := closest_word_mem_referenceSimplex hd x word hmin
  apply Set.mem_iUnion.mpr
  refine ⟨wordAlcove d word.reverse, ?_⟩
  change x ∈ reflectionWordMap d word.reverse '' referenceSimplex d
  exact ⟨reflectionWordMap d word x, hy, reflectionWordMap_reverse_left d word x⟩

end Antichain
