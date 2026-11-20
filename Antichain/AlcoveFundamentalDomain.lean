import Antichain.AffineAlcoveGroup
import Antichain.AlcoveTiling
import Antichain.ConfigurationContraction
import Mathlib.Data.List.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Direct type-A closed-alcove orbit uniqueness, without a Coxeter input. -/

noncomputable section

namespace Antichain

open Finset Set
open scoped Topology

set_option maxHeartbeats 800000

/-- Inside two coordinate arrays of spread at most one, a zero-sum integer
shift can only exchange equally many bottom and top endpoints. Consequently
it preserves every finite sum of a test function. -/
theorem integer_shift_preserves_sums {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (e : Equiv.Perm ι) (k : ι → ℤ)
    (hu : ∀ i j, u i - u j ≤ 1) (hv : ∀ i j, v i - v j ≤ 1)
    (hk : ∑ i, k i = 0) (hcoords : ∀ i, u i = v (e i) + (k i : ℝ))
    (φ : ℝ → ℝ) : ∑ i, φ (u i) = ∑ i, φ (v i) := by
  classical
  by_cases hz : ∀ i, k i = 0
  · have heq : u = fun i ↦ v (e i) := by
      funext i
      simpa only [hz i, Int.cast_zero, add_zero] using hcoords i
    rw [heq]
    exact Equiv.sum_comp e (fun i ↦ φ (v i))
  · have hnonzero : ∃ i ∈ (Finset.univ : Finset ι), k i ≠ 0 := by
      simpa only [Finset.mem_univ, true_and, not_forall] using hz
    obtain ⟨p, _, hp⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero k hk hnonzero
    have hkneg : ∑ i, -k i = 0 := by rw [Finset.sum_neg_distrib, hk, neg_zero]
    have hnonzeroNeg : ∃ i ∈ (Finset.univ : Finset ι), -k i ≠ 0 := by
      simpa only [neg_ne_zero] using hnonzero
    obtain ⟨n, _, hn⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero (fun i ↦ -k i)
      hkneg hnonzeroNeg
    have hpR : (1 : ℝ) ≤ (k p : ℝ) := by exact_mod_cast hp
    have hnR : (k n : ℝ) ≤ -1 := by
      have hz : k n ≤ -1 := by omega
      exact_mod_cast hz
    have hpone : k p = 1 := by
      have hup := hu p n
      rw [hcoords p, hcoords n] at hup
      have hvpn := hv (e n) (e p)
      have hkle : (k p : ℝ) ≤ 1 := by linarith
      have hkleZ : k p ≤ 1 := by exact_mod_cast hkle
      omega
    have hnneg : k n = -1 := by
      have hup := hu p n
      rw [hcoords p, hcoords n] at hup
      have hvpn := hv (e n) (e p)
      have hkle : (-1 : ℝ) ≤ (k n : ℝ) := by linarith
      have hkleZ : -1 ≤ k n := by exact_mod_cast hkle
      omega
    have hgap : v (e n) - v (e p) = 1 := by
      have hup := hu p n
      rw [hcoords p, hcoords n, hpone, hnneg] at hup
      norm_num at hup
      linarith [hv (e n) (e p)]
    have hpositive (i : ι) (hi : 0 < k i) : k i = 1 ∧ v (e i) = v (e p) := by
      have hiR : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hi
      have hui := hu i n
      rw [hcoords i, hcoords n, hnneg] at hui
      norm_num at hui
      have hvni := hv (e n) (e i)
      have hki : (k i : ℝ) ≤ 1 := by linarith
      have hkiZ : k i ≤ 1 := by exact_mod_cast hki
      have heq : k i = 1 := by omega
      refine ⟨heq, ?_⟩
      rw [heq] at hui
      norm_num at hui
      linarith
    have hnegative (i : ι) (hi : k i < 0) : k i = -1 ∧ v (e i) = v (e n) := by
      have hiR : (k i : ℝ) ≤ -1 := by
        have hz : k i ≤ -1 := by omega
        exact_mod_cast hz
      have hui := hu p i
      rw [hcoords p, hcoords i, hpone] at hui
      norm_num at hui
      have hvip := hv (e i) (e p)
      have hki : (-1 : ℝ) ≤ (k i : ℝ) := by linarith
      have hkiZ : -1 ≤ k i := by exact_mod_cast hki
      have heq : k i = -1 := by omega
      refine ⟨heq, ?_⟩
      rw [heq] at hui
      norm_num at hui
      linarith
    have hdiff (i : ι) : φ (u i) - φ (v (e i)) =
        (k i : ℝ) * (φ (v (e n)) - φ (v (e p))) := by
      by_cases hi : 0 < k i
      · obtain ⟨hki, hvi⟩ := hpositive i hi
        have hui : u i = v (e n) := by rw [hcoords i, hki, hvi]; norm_num; linarith
        rw [hui, hvi, hki]
        norm_num
      · by_cases hi' : k i < 0
        · obtain ⟨hki, hvi⟩ := hnegative i hi'
          have hui : u i = v (e p) := by rw [hcoords i, hki, hvi]; norm_num; linarith
          rw [hui, hvi, hki]
          norm_num
        · have hki : k i = 0 := by omega
          rw [hcoords i, hki]
          simp
    have hkR : ∑ i, (k i : ℝ) = 0 := by exact_mod_cast hk
    have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ hdiff i)
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hkR, zero_mul] at hsum
    have he := Equiv.sum_comp e (fun i ↦ φ (v i))
    linarith

theorem ofFn_count_real {d : ℕ} (f : Fin d → ℝ) (a : ℝ) :
    (List.count a (List.ofFn f) : ℝ) = ∑ i : Fin d, if f i = a then 1 else 0 := by
  classical
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    by_cases h : f 0 = a
    · simp [h, ih, add_comm]
    · simp [h, ih]

theorem antitone_eq_of_test_sums {d : ℕ} (u v : Fin d → ℝ)
    (hu : Antitone u) (hv : Antitone v)
    (hsums : ∀ φ : ℝ → ℝ, ∑ i, φ (u i) = ∑ i, φ (v i)) : u = v := by
  classical
  have hp : List.Perm (List.ofFn u) (List.ofFn v) := by
    apply List.perm_iff_count.mpr
    intro a
    have h := hsums (fun t ↦ if t = a then 1 else 0)
    rw [← ofFn_count_real u a, ← ofFn_count_real v a] at h
    exact_mod_cast h
  have heq := List.eq_of_perm_of_sorted hp hu.ofFn_sorted hv.ofFn_sorted
  exact List.ofFn_injective heq

/-- Direct closed fundamental-alcove uniqueness for the actual integer-root
lattice affine permutation action. No Coxeter theorem is an assumption. -/
theorem alcove_integer_shift_unique {d : ℕ} (_hd : 2 ≤ d)
    {u v : FloorSpace (Fin d)} (hu : u ∈ referenceSimplex d) (hv : v ∈ referenceSimplex d)
    (e : Equiv.Perm (Fin d)) (k : Fin d → ℤ) (hk : ∑ i, k i = 0)
    (hcoords : ∀ i, u.val i = v.val (e i) + (k i : ℝ)) : u = v := by
  have heq : (fun i ↦ u.val i) = (fun i ↦ v.val i) :=
    antitone_eq_of_test_sums _ _ hu.1 hv.1
      (integer_shift_preserves_sums _ _ e k hu.2 hv.2 hk hcoords)
  apply Subtype.ext
  exact PiLp.ext (congrFun heq)

variable {d : ℕ} [NeZero d]

theorem closed_alcove_representative_unique_direct (hd : 2 ≤ d)
    (w v : List (Fin d)) (x y : FloorSpace (Fin d))
    (hx : x ∈ referenceSimplex d) (hy : y ∈ referenceSimplex d)
    (heq : reflectionWordMap d w x = reflectionWordMap d v y) : x = y := by
  let r := w.reverse ++ v
  have hxy : x = reflectionWordMap d r y := by
    dsimp [r]
    rw [reflectionWordMap_append, ← heq, reflectionWordMap_reverse_left]
  obtain ⟨k, hk, hnormal⟩ := reflectionWordMap_integer_normal_form d r
  apply alcove_integer_shift_unique hd hx hy (wordPermutation d r) k hk
  intro i
  rw [hxy, hnormal]
  ring

/-- A nontrivial integer-affine coordinate permutation cannot fix a point of
the strict core: every coordinate difference there lies strictly between -1 and 1. -/
theorem reflectionWordMap_eq_id_of_fixes_core (w : List (Fin d))
    (x : FloorSpace (Fin d)) (hx : x ∈ referenceSimplexCore d)
    (hfix : reflectionWordMap d w x = x) : reflectionWordMap d w = id := by
  obtain ⟨k, _, hnormal⟩ := reflectionWordMap_integer_normal_form d w
  have hcoord (i : Fin d) : (k i : ℝ) + x.val (wordPermutation d w i) = x.val i := by
    rw [← hnormal]
    exact congrArg (fun u : FloorSpace (Fin d) ↦ u.val i) hfix
  have hkzero (i : Fin d) : k i = 0 := by
    have hlow : (-1 : ℝ) < (k i : ℝ) := by
      have h := hx.2 (wordPermutation d w i) i
      linarith [hcoord i]
    have hhigh : (k i : ℝ) < 1 := by
      have h := hx.2 i (wordPermutation d w i)
      linarith [hcoord i]
    have hlZ : (-1 : ℤ) < k i := by exact_mod_cast hlow
    have hhZ : k i < 1 := by exact_mod_cast hhigh
    omega
  have hxinj : Function.Injective (fun i : Fin d ↦ x.val i) :=
    (show StrictAnti (fun i : Fin d ↦ x.val i) from hx.1).injective
  have hp (i : Fin d) : wordPermutation d w i = i := by
    apply hxinj
    simpa only [hkzero i, Int.cast_zero, zero_add] using hcoord i
  funext u
  apply Subtype.ext
  apply PiLp.ext
  intro i
  rw [hnormal, hkzero, Int.cast_zero, zero_add, hp]
  rfl

theorem reflectionWordMap_eq_of_agree_core (w v : List (Fin d))
    (x : FloorSpace (Fin d)) (hx : x ∈ referenceSimplexCore d)
    (heq : reflectionWordMap d w x = reflectionWordMap d v x) :
    reflectionWordMap d w = reflectionWordMap d v := by
  have hrfix : reflectionWordMap d (w.reverse ++ v) x = x := by
    rw [reflectionWordMap_append, ← heq, reflectionWordMap_reverse_left]
  have hr := reflectionWordMap_eq_id_of_fixes_core (w.reverse ++ v) x hx hrfix
  funext y
  have hy := congrFun hr y
  rw [reflectionWordMap_append] at hy
  have hwy := congrArg (reflectionWordMap d w) hy
  rw [reflectionWordMap_reverse_right] at hwy
  exact hwy.symm

theorem same_tile_map_unique_direct (hd : 2 ≤ d) (w v : List (Fin d))
    (htile : reflectionTile d w = reflectionTile d v) :
    reflectionWordMap d w = reflectionWordMap d v := by
  let x := referenceSimplexInteriorPoint d
  have hx : x ∈ referenceSimplexCore d := referenceSimplexInteriorPoint_mem_core d
  have hmem : reflectionWordMap d w x ∈ reflectionTile d v := by
    rw [← htile]
    exact ⟨x, referenceSimplexCore_subset d hx, rfl⟩
  obtain ⟨y, hy, hmap⟩ := hmem
  have hxy := closed_alcove_representative_unique_direct hd w v x y
    (referenceSimplexCore_subset d hx) hy hmap.symm
  apply reflectionWordMap_eq_of_agree_core w v x hx
  simpa only [← hxy] using hmap.symm

def floorCoordinateDifference (i j : Fin d) : FloorSpace (Fin d) →ₗ[ℝ] ℝ where
  toFun u := u.val i - u.val j
  map_add' u v := by change (u.val i + v.val i) - (u.val j + v.val j) = _; ring
  map_smul' a u := by change a * u.val i - a * u.val j = a * (u.val i - u.val j); ring

omit [NeZero d] in
theorem floorCoordinateDifference_surjective (i j : Fin d) (hij : i ≠ j) :
    Function.Surjective (floorCoordinateDifference i j) := by
  intro t
  let u : FloorSpace (Fin d) :=
    ⟨EuclideanSpace.single i (t / 2) - EuclideanSpace.single j (t / 2), by simp [coordinateSum]⟩
  refine ⟨u, ?_⟩
  change (EuclideanSpace.single i (t / 2) - EuclideanSpace.single j (t / 2)) i -
    (EuclideanSpace.single i (t / 2) - EuclideanSpace.single j (t / 2)) j = t
  simp [EuclideanSpace.single_apply, hij, hij.symm]

omit [NeZero d] in
theorem interior_difference_strict {B : Set (FloorSpace (Fin d))}
    {x : FloorSpace (Fin d)} (hx : x ∈ interior B) (i j : Fin d) (hij : i ≠ j)
    (c : ℝ) (hbound : ∀ y ∈ B, y.val i - y.val j ≤ c) : x.val i - x.val j < c := by
  have hopen : IsOpenMap (floorCoordinateDifference i j) :=
    (floorCoordinateDifference i j).isOpenMap_of_finiteDimensional
      (floorCoordinateDifference_surjective i j hij)
  have hi : x ∈ interior ((floorCoordinateDifference i j) ⁻¹' Iic c) :=
    interior_mono (fun y hy ↦ hbound y hy) hx
  have hp := hopen.interior_preimage_subset_preimage_interior hi
  simpa only [interior_Iic, Set.mem_preimage, Set.mem_Iio, floorCoordinateDifference] using hp

omit [NeZero d] in
theorem interior_referenceSimplex_eq_core_direct :
    interior (referenceSimplex d) = referenceSimplexCore d := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · intro i j hij
      have h := interior_difference_strict hx j i hij.ne' 0
        (fun y hy ↦ sub_nonpos.mpr (hy.1 hij.le))
      linarith
    · intro i j
      by_cases hij : i = j
      · subst j
        simp
      · exact interior_difference_strict hx i j hij 1 (fun y hy ↦ hy.2 i j)
  · exact (isOpen_referenceSimplexCore d).subset_interior_iff.mpr (referenceSimplexCore_subset d)

theorem reflectionTile_interior_eq (w : List (Fin d)) :
    interior (reflectionTile d w) = reflectionWordMap d w '' interior (referenceSimplex d) := by
  have hfun : (reflectionWordHomeomorph d w : FloorSpace (Fin d) → FloorSpace (Fin d)) =
      reflectionWordMap d w := funext (reflectionWordHomeomorph_apply d w)
  simpa only [hfun, reflectionTile] using
    ((reflectionWordHomeomorph d w).image_interior (referenceSimplex d)).symm

theorem alcoveTile_disjoint_interiors_direct (hd : 2 ≤ d) :
    Pairwise (fun t u : AlcoveTile d ↦ Disjoint (interior (t : Set (FloorSpace (Fin d))))
      (interior (u : Set (FloorSpace (Fin d))))) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  intro z hzt hzu
  obtain ⟨w, hw⟩ := t.property
  obtain ⟨v, hv⟩ := u.property
  change z ∈ interior t.val at hzt
  change z ∈ interior u.val at hzu
  rw [← hw, reflectionTile_interior_eq] at hzt
  rw [← hv, reflectionTile_interior_eq] at hzu
  obtain ⟨x, hx, hxz⟩ := hzt
  obtain ⟨y, hy, hyz⟩ := hzu
  have hxy := closed_alcove_representative_unique_direct hd w v x y
    (interior_subset hx) (interior_subset hy) (hxz.trans hyz.symm)
  have hxcore : x ∈ referenceSimplexCore d := (interior_referenceSimplex_eq_core_direct (d := d)) ▸ hx
  have hmaps := reflectionWordMap_eq_of_agree_core w v x hxcore
    (by simpa only [← hxy] using hxz.trans hyz.symm)
  have htiles : reflectionTile d w = reflectionTile d v := by
    unfold reflectionTile
    rw [hmaps]
  apply htu
  apply Subtype.ext
  exact hw.symm.trans (htiles.trans hv)

end Antichain
