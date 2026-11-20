import Antichain.SimplicialCubeInterpolation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Combination

/-! Exact coordinate reconstruction by the actual affine Kuhn weights. -/

noncomputable section

namespace Antichain

open Finset

theorem kuhnLowerAffine_zero {d N : ℕ} (b : Fin d → Fin N)
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) :
    kuhnLowerAffine b sigma 0 z = 0 := by
  simp [kuhnLowerAffine]

theorem kuhnUpperAffine_last {d N : ℕ} (b : Fin d → Fin N)
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) :
    kuhnUpperAffine b sigma (Fin.last d) z = 1 := by
  simp [kuhnUpperAffine]

theorem kuhnLowerAffine_succ {d N : ℕ} (b : Fin d → Fin N)
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) (j : Fin d) :
    kuhnLowerAffine b sigma j.succ z = kuhnUpperAffine b sigma j.castSucc z := by
  simp [kuhnLowerAffine, kuhnUpperAffine, j.isLt]

theorem kuhnGridVertex_last {d N : ℕ} (b : Fin d → Fin N)
    (sigma : Equiv.Perm (Fin d)) (i : Fin d) :
    (kuhnGridVertex b sigma (Fin.last d) i : ℝ) = (b i : ℝ) + 1 := by
  rw [kuhnGridVertex_apply]
  simp only [Fin.val_last, (sigma.symm i).isLt, ↓reduceIte]

theorem kuhnGridVertex_step {d N : ℕ} (b : Fin d → Fin N)
    (sigma : Equiv.Perm (Fin d)) (i j : Fin d) :
    (kuhnGridVertex b sigma j.castSucc i : ℝ) -
      (kuhnGridVertex b sigma j.succ i : ℝ) =
        if j = sigma.symm i then -1 else 0 := by
  simp only [kuhnGridVertex_apply, Fin.coe_castSucc, Fin.val_succ]
  by_cases heq : j = sigma.symm i
  · subst j
    simp
  · have hne : j.val ≠ (sigma.symm i).val := fun h => heq (Fin.ext h)
    by_cases hlt : (sigma.symm i).val < j.val
    · have hlt' : (sigma.symm i).val < j.val + 1 := by omega
      simp [heq, hlt, hlt']
    · have hlt' : ¬(sigma.symm i).val < j.val + 1 := by omega
      simp [heq, hlt, hlt']

/-- The weights reproduce every coordinate, so they are genuine barycentric
coordinates of the explicitly listed chain vertices. The identity is affine
and holds even off the simplex; nonnegativity on the simplex is separate. -/
theorem kuhnWeightAffine_barycenter {d N : ℕ} (b : Fin d → Fin N)
    (sigma : Equiv.Perm (Fin d)) (z : Fin d → ℝ) (i : Fin d) :
    (∑ j : Fin (d + 1), kuhnWeightAffine b sigma j z *
      (kuhnGridVertex b sigma j i : ℝ)) = z i := by
  classical
  have hsplit : (∑ j : Fin (d + 1), kuhnWeightAffine b sigma j z *
      (kuhnGridVertex b sigma j i : ℝ)) =
      (∑ j : Fin d, kuhnUpperAffine b sigma j.castSucc z *
        ((kuhnGridVertex b sigma j.castSucc i : ℝ) -
          (kuhnGridVertex b sigma j.succ i : ℝ))) + ((b i : ℝ) + 1) := by
    change (∑ j : Fin (d + 1),
      (kuhnUpperAffine b sigma j z - kuhnLowerAffine b sigma j z) *
        (kuhnGridVertex b sigma j i : ℝ)) = _
    simp_rw [sub_mul]
    rw [sum_sub_distrib, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp_rw [kuhnLowerAffine_zero, kuhnLowerAffine_succ,
      kuhnUpperAffine_last, kuhnGridVertex_last]
    simp only [zero_mul, one_mul, zero_add]
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    ring
  rw [hsplit]
  simp_rw [kuhnGridVertex_step]
  have hsum : (∑ j : Fin d, kuhnUpperAffine b sigma j.castSucc z *
      (if j = sigma.symm i then (-1 : ℝ) else 0)) =
        -kuhnUpperAffine b sigma (sigma.symm i).castSucc z := by
    simp
  rw [hsum]
  have hu : kuhnUpperAffine b sigma (sigma.symm i).castSucc z =
      1 + (b i : ℝ) - z i := by
    rw [kuhnUpperAffine]
    simp only [Fin.coe_castSucc]
    rw [dif_pos (sigma.symm i).isLt]
    change 1 + (b (sigma (sigma.symm i)) : ℝ) - z (sigma (sigma.symm i)) = _
    simp
  rw [hu]
  ring

/-- Each actual ordered cell point is a convex combination of its chain
vertices, with the actual nonnegative affine weights. -/
theorem kuhnGridSimplex_mem_convexHull {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (sigma : Equiv.Perm (Fin d))
    {z : Fin d → ℝ} (hz : z ∈ kuhnGridSimplex b sigma) :
    z ∈ convexHull ℝ (Set.range (fun j : Fin (d + 1) =>
      fun i => (kuhnGridVertex b sigma j i : ℝ))) := by
  classical
  have hsum : (∑ j : Fin (d + 1), kuhnWeightAffine b sigma j z •
      (fun i => (kuhnGridVertex b sigma j i : ℝ))) = z := by
    funext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      kuhnWeightAffine_barycenter b sigma z i
  rw [← hsum]
  exact (convex_convexHull ℝ _).sum_mem
    (fun j _ => kuhnWeightAffine_nonneg b sigma hz j)
    (sum_kuhnWeightAffine b sigma hz)
    (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))

end Antichain
