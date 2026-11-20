import Antichain.PinnedVolume
import Antichain.ReferenceSimplex

/-! The actual side-reflection words defining the paper's tiles.
The volume identity uses their literal affine-coordinate formulas and does not
assume the Coxeter tiling theorem. -/

noncomputable section

namespace Antichain

open MeasureTheory
open scoped Pointwise ENNReal

variable (d : ℕ) [NeZero d]

def lastCoordinate : Fin d := ⟨d - 1, Nat.sub_lt (NeZero.pos d) zero_lt_one⟩

def previousCoordinate (i : Fin d) : Fin d :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- Linear coordinate permutation in each of the d side reflections. -/
def sidePermutation (i : Fin d) : Fin d ≃ Fin d :=
  if i = 0 then Equiv.swap 0 (lastCoordinate d) else Equiv.swap (previousCoordinate d i) i

/-- The affine wall contributes +1 in the first and -1 in the last coordinate. -/
def sideTranslation (i : Fin d) : FloorSpace (Fin d) :=
  if i = 0 then ⟨EuclideanSpace.single 0 (1 : ℝ) -
    EuclideanSpace.single (lastCoordinate d) 1, by simp [coordinateSum]⟩ else 0

/-- These are precisely the explicit side maps in Section 3.2. -/
def sideReflection (i : Fin d) (x : FloorSpace (Fin d)) : FloorSpace (Fin d) :=
  sideTranslation d i + floorPermutation (sidePermutation d i) x

theorem sideReflection_zero_apply (x : FloorSpace (Fin d)) (j : Fin d) :
    (sideReflection d 0 x).val j =
      x.val ((Equiv.swap 0 (lastCoordinate d)) j) +
        (if j = 0 then 1 else 0) - (if j = lastCoordinate d then 1 else 0) := by
  simp [sideReflection, sideTranslation, sidePermutation, EuclideanSpace.single_apply,
    sub_add_eq_add_sub, add_comm]

theorem sideReflection_nonzero_apply (i : Fin d) (hi : i ≠ 0)
    (x : FloorSpace (Fin d)) (j : Fin d) :
    (sideReflection d i x).val j = x.val ((Equiv.swap (previousCoordinate d i) i) j) := by
  simp [sideReflection, sideTranslation, sidePermutation, hi]

/-- Products act from right to left, as in the manuscript's reflection words. -/
def reflectionWordMap (word : List (Fin d)) (x : FloorSpace (Fin d)) : FloorSpace (Fin d) :=
  word.foldr (fun i y => sideReflection d i y) x

def wordPermutation : List (Fin d) → (Fin d ≃ Fin d)
  | [] => Equiv.refl _
  | i :: w => (sidePermutation d i).trans (wordPermutation w)

def wordTranslation : List (Fin d) → FloorSpace (Fin d)
  | [] => 0
  | i :: w => sideTranslation d i + floorPermutation (sidePermutation d i) (wordTranslation w)

omit [NeZero d] in
theorem floorPermutation_trans (e f : Fin d ≃ Fin d) (x : FloorSpace (Fin d)) :
    floorPermutation e (floorPermutation f x) = floorPermutation (e.trans f) x := by
  apply Subtype.ext
  ext i
  rfl

/-- Every word is actually a translation of a coordinate permutation. -/
theorem reflectionWordMap_eq_affine (word : List (Fin d)) (x : FloorSpace (Fin d)) :
    reflectionWordMap d word x = wordTranslation d word + floorPermutation (wordPermutation d word) x := by
  induction word with
  | nil =>
      apply Subtype.ext
      ext i
      simp [reflectionWordMap, wordTranslation, wordPermutation]
  | cons i w ih =>
      simp only [reflectionWordMap, List.foldr_cons, sideReflection,
        wordTranslation, wordPermutation] at *
      simp only [ih, map_add, floorPermutation_trans, add_assoc]

/-- Literal definition of a reflected copy of the reference simplex. -/
def reflectionTile (word : List (Fin d)) : Set (FloorSpace (Fin d)) :=
  reflectionWordMap d word '' referenceSimplex d

theorem reflectionTile_eq_affine (word : List (Fin d)) :
    reflectionTile d word =
      (fun x => wordTranslation d word + floorPermutation (wordPermutation d word) x) '' referenceSimplex d := by
  simp only [reflectionTile, reflectionWordMap_eq_affine]

/-- Equality of the actual pinned volumes on every reflected tile and the reference tile. -/
theorem pinnedMass_reflectionTile (word : List (Fin d)) (r : ℕ) :
    pinnedMass (reflectionTile d word) r = pinnedMass (referenceSimplex d) r := by
  rw [reflectionTile_eq_affine]
  exact pinnedMass_affinePermutation _ _ (isClosed_referenceSimplex d).measurableSet r

/-- Lemma 3.5 for the literal source reflection-word family. -/
theorem pinnedVolume_reflectionTile_scale (word : List (Fin d)) (r : ℕ)
    (s : ℝ) (hs : 0 < s) :
    pinnedVolume (s • reflectionTile d word) r =
      s ^ (d * (r + 1) - 1) * pinnedVolume (reflectionTile d word) r ∧
    pinnedVolume (s • reflectionTile d word) r =
      s ^ (d * (r + 1) - 1) * pinnedVolume (referenceSimplex d) r := by
  have hscale := pinnedVolume_smul s hs (reflectionTile d word) r
  simp only [Fintype.card_fin] at hscale
  refine ⟨hscale, ?_⟩
  rw [hscale, pinnedVolume, pinnedMass_reflectionTile]
  rfl

end Antichain
