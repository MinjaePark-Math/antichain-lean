import Antichain.TileSymmetries

/-! Integer affine normal forms and inverses of the actual alcove reflection words.
This development does not assume any Coxeter-group or tiling input. -/

noncomputable section

namespace Antichain

open Finset

variable (d : ℕ) [NeZero d]

/-- The actual word translation has integer coordinates. -/
theorem wordTranslation_integer (word : List (Fin d)) (j : Fin d) :
    ∃ z : ℤ, (wordTranslation d word).val j = (z : ℝ) := by
  classical
  induction word generalizing j with
  | nil => exact ⟨0, by simp [wordTranslation]⟩
  | cons i w ih =>
      obtain ⟨z, hz⟩ := ih (sidePermutation d i j)
      by_cases hi : i = 0
      · subst i
        refine ⟨(if j = 0 then 1 else 0) -
          (if j = lastCoordinate d then 1 else 0) + z, ?_⟩
        change (EuclideanSpace.single 0 (1 : ℝ)) j -
          (EuclideanSpace.single (lastCoordinate d) (1 : ℝ)) j +
          (wordTranslation d w).val (sidePermutation d 0 j) = _
        rw [hz]
        simp [EuclideanSpace.single_apply]
      · refine ⟨z, ?_⟩
        simpa [wordTranslation, sideTranslation, hi] using hz

/-- A source-facing integer-coordinate normal form, including the root-lattice sum constraint. -/
theorem reflectionWordMap_integer_normal_form (word : List (Fin d)) :
    ∃ z : Fin d → ℤ, (∑ i, z i) = 0 ∧
      ∀ (x : FloorSpace (Fin d)) (i : Fin d),
        (reflectionWordMap d word x).val i =
          (z i : ℝ) + x.val (wordPermutation d word i) := by
  classical
  choose z hz using wordTranslation_integer d word
  refine ⟨z, ?_, ?_⟩
  · have hsum : (∑ i, (z i : ℝ)) = 0 := by
      simp_rw [← hz]
      exact (wordTranslation d word).property
    exact_mod_cast hsum
  · intro x i
    rw [reflectionWordMap_eq_affine]
    change (wordTranslation d word).val i + x.val (wordPermutation d word i) = _
    rw [hz]

@[simp] theorem reflectionWordMap_nil (x : FloorSpace (Fin d)) :
    reflectionWordMap d [] x = x := rfl

@[simp] theorem reflectionWordMap_cons (i : Fin d) (word : List (Fin d))
    (x : FloorSpace (Fin d)) :
    reflectionWordMap d (i :: word) x = sideReflection d i (reflectionWordMap d word x) := rfl

theorem reflectionWordMap_append (w v : List (Fin d)) (x : FloorSpace (Fin d)) :
    reflectionWordMap d (w ++ v) x = reflectionWordMap d w (reflectionWordMap d v x) := by
  simp [reflectionWordMap, List.foldr_append]

theorem sidePermutation_self (i : Fin d) :
    (sidePermutation d i).trans (sidePermutation d i) = Equiv.refl _ := by
  classical
  unfold sidePermutation
  split <;> ext j <;> simp

theorem floorPermutation_sidePermutation_sideTranslation (i : Fin d) :
    floorPermutation (sidePermutation d i) (sideTranslation d i) = -sideTranslation d i := by
  classical
  by_cases hi : i = 0
  · subst i
    apply Subtype.ext
    ext j
    simp only [sidePermutation, sideTranslation, floorPermutation_apply,
      Submodule.coe_neg, PiLp.neg_apply]
    by_cases hj0 : j = 0
    · subst j
      simp [Equiv.swap_apply_left, eq_comm]
    · by_cases hjlast : j = lastCoordinate d
      · subst j
        simp [Equiv.swap_apply_right, eq_comm]
      · simp [Equiv.swap_apply_of_ne_of_ne hj0 hjlast, hj0, hjlast]
  · simp [sideTranslation, hi]

theorem sideReflection_involutive (i : Fin d) : Function.Involutive (sideReflection d i) := by
  intro x
  unfold sideReflection
  rw [map_add, floorPermutation_sidePermutation_sideTranslation, floorPermutation_trans,
    sidePermutation_self]
  have hrefl : floorPermutation (Equiv.refl (Fin d)) x = x := by
    apply Subtype.ext
    ext j
    rfl
  rw [hrefl]
  simp

@[simp] theorem reflectionWordMap_reverse_left (word : List (Fin d)) (x : FloorSpace (Fin d)) :
    reflectionWordMap d word.reverse (reflectionWordMap d word x) = x := by
  induction word generalizing x with
  | nil => rfl
  | cons i w ih =>
      rw [List.reverse_cons, reflectionWordMap_append]
      simp only [reflectionWordMap_cons, reflectionWordMap_nil]
      rw [sideReflection_involutive d i]
      exact ih x

@[simp] theorem reflectionWordMap_reverse_right (word : List (Fin d)) (x : FloorSpace (Fin d)) :
    reflectionWordMap d word (reflectionWordMap d word.reverse x) = x := by
  simpa only [List.reverse_reverse] using reflectionWordMap_reverse_left d word.reverse x

theorem reflectionWordMap_bijective (word : List (Fin d)) :
    Function.Bijective (reflectionWordMap d word) :=
  ⟨Function.LeftInverse.injective (reflectionWordMap_reverse_left d word),
    Function.RightInverse.surjective (reflectionWordMap_reverse_right d word)⟩

end Antichain
