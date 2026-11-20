import Antichain.ReferenceSimplex
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Quantitative finite grid balls inside the actual Euclidean floor simplex. -/

noncomputable section

namespace Antichain

open Finset MeasureTheory
open scoped Topology ENNReal

/-- Choose the number of subdivisions at the correct inverse-dimensional rate. -/
theorem exists_grid_subdivision {m N : ℕ} (hm : 0 < m) (hN : 0 < N) :
    ∃ M : ℕ, 0 < M ∧ N ≤ M ^ m ∧
      (M : ℝ) ≤ 2 * (N : ℝ) ^ ((m : ℝ)⁻¹) := by
  let x : ℝ := (N : ℝ) ^ ((m : ℝ)⁻¹)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hx : 1 ≤ x := by
    dsimp [x]
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hNR
      (inv_nonneg.mpr (Nat.cast_nonneg m))
  let M : ℕ := Nat.ceil x
  have hM : 0 < M := Nat.one_le_ceil_iff.mpr (by linarith)
  have hNM : N ≤ M ^ m := by
    have hp : x ^ m ≤ (M : ℝ) ^ m := pow_le_pow_left₀ (by linarith : 0 ≤ x) (Nat.le_ceil x) m
    rw [show x ^ m = (N : ℝ) by exact Real.rpow_inv_natCast_pow (by positivity) hm.ne'] at hp
    exact_mod_cast hp
  refine ⟨M, hM, hNM, ?_⟩
  have hceil := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  dsimp [M]
  linarith

/-- A finite coordinate grid in Euclidean space. -/
def euclideanGridPoint {m M : ℕ} (η : ℝ) (k : Fin m → Fin M) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i ↦ η * (k i).val / (M : ℝ))

theorem euclideanGridPoint_coordinate_bounds {m M : ℕ} (η : ℝ) (hη : 0 ≤ η)
    (hM : 0 < M) (k : Fin m → Fin M) (i : Fin m) :
    0 ≤ euclideanGridPoint η k i ∧ euclideanGridPoint η k i ≤ η := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hki : ((k i).val : ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (k i).isLt)
  constructor
  · exact div_nonneg (mul_nonneg hη (by positivity)) hMR.le
  · apply (div_le_iff₀ hMR).mpr
    exact mul_le_mul_of_nonneg_left hki hη

theorem norm_euclideanGridPoint_le {m M : ℕ} (hm : 0 < m) (hM : 0 < M)
    (η : ℝ) (hη : 0 ≤ η) (k : Fin m → Fin M) :
    ‖euclideanGridPoint η k‖ ≤ (m : ℝ) * η := by
  have hsq (i : Fin m) : (euclideanGridPoint η k i) ^ 2 ≤ η ^ 2 := by
    obtain ⟨hl, hu⟩ := euclideanGridPoint_coordinate_bounds η hη hM k i
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) ↦ hsq i)
  have hn := EuclideanSpace.norm_sq_eq (euclideanGridPoint η k)
  simp only [Real.norm_eq_abs, sq_abs] at hn
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hmη : (m : ℝ) * η ^ 2 ≤ ((m : ℝ) * η) ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) by nlinarith) hηsq]
  nlinarith [norm_nonneg (euclideanGridPoint η k), mul_nonneg (by positivity : (0 : ℝ) ≤ m) hη]

/-- Distinct grid addresses are separated by one mesh interval in Euclidean norm. -/
theorem euclideanGridPoint_separated {m M : ℕ} (hM : 0 < M) (η : ℝ) (hη : 0 ≤ η)
    {k l : Fin m → Fin M} (hkl : k ≠ l) :
    η / (M : ℝ) ≤ dist (euclideanGridPoint η k) (euclideanGridPoint η l) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin m, k i ≠ l i := by
    by_contra h
    push_neg at h
    exact hkl (funext h)
  have hval : (k i).val ≠ (l i).val := fun h ↦ hi (Fin.ext h)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : η / (M : ℝ) ≤
      |euclideanGridPoint η k i - euclideanGridPoint η l i| := by
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hreal : ((k i).val : ℝ) + 1 ≤ (l i).val := by exact_mod_cast hlt
      have hmul := mul_le_mul_of_nonneg_left hreal (div_nonneg hη hMR.le)
      have hdiff : η / (M : ℝ) ≤ euclideanGridPoint η l i - euclideanGridPoint η k i := by
        dsimp [euclideanGridPoint]
        simp only [div_eq_mul_inv] at hmul ⊢
        nlinarith
      exact hdiff.trans (le_abs_self _ |>.trans_eq (abs_sub_comm _ _))
    · have hreal : ((l i).val : ℝ) + 1 ≤ (k i).val := by exact_mod_cast hgt
      have hmul := mul_le_mul_of_nonneg_left hreal (div_nonneg hη hMR.le)
      have hdiff : η / (M : ℝ) ≤ euclideanGridPoint η k i - euclideanGridPoint η l i := by
        dsimp [euclideanGridPoint]
        simp only [div_eq_mul_inv] at hmul ⊢
        nlinarith
      exact hdiff.trans (le_abs_self _)
  have hn := PiLp.norm_apply_le (euclideanGridPoint η k - euclideanGridPoint η l) i
  rw [Real.norm_eq_abs] at hn
  exact hc.trans (by simpa only [dist_eq_norm, PiLp.sub_apply] using hn)

/-- Every sample size admits N quantitatively separated floor balls inside the
actual reference simplex, with radius c_d N^(-1/(d-1)). The constant is fixed
once from an actual interior ball; no packing hypothesis is supplied. -/
theorem exists_referenceSimplex_grid_balls {d : ℕ} (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
      ∃ z : Fin N → FloorSpace (Fin d),
        (∀ i, Metric.ball (z i) (c * (N : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) ⊆ referenceSimplex d) ∧
        Pairwise (fun i j ↦ 8 * (c * (N : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) ≤ dist (z i) (z j)) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  let E := FloorSpace (Fin d)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm : 0 < d - 1 := by omega
  have hdim : Module.finrank ℝ E = d - 1 := by
    simpa only [Fintype.card_fin] using (finrank_floorSpace (ι := Fin d))
  let b : OrthonormalBasis (Fin (d - 1)) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  obtain ⟨w, hw⟩ := referenceSimplex_interior_nonempty hd
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hw)
  let η : ℝ := R / (4 * (d : ℝ))
  have hη : 0 < η := div_pos hR (by positivity)
  let c : ℝ := η / 16
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, fun N hN ↦ ?_⟩
  obtain ⟨M, hM, hNM, hMbound⟩ := exists_grid_subdivision hm hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let x : ℝ := (N : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)
  have hx : 0 < x := Real.rpow_pos_of_pos hNR _
  have hx1 : 1 ≤ x := by
    dsimp [x]
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one
      (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))
      (inv_nonneg.mpr (Nat.cast_nonneg (d - 1)))
  let radius : ℝ := c * (N : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)
  have hradius : radius = η / (16 * x) := by
    dsimp [radius, c, x]
    rw [Real.rpow_neg hNR.le]
    ring
  have hrpos : 0 < radius := by rw [hradius]; positivity
  obtain ⟨e⟩ : Nonempty (Fin N ↪ (Fin (d - 1) → Fin M)) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin, Fintype.card_fun] using hNM)
  let z : Fin N → E := fun i ↦ w + b.repr.symm (euclideanGridPoint η (e i))
  have hoffset (i : Fin N) : ‖b.repr.symm (euclideanGridPoint η (e i))‖ ≤ (d : ℝ) * η := by
    rw [b.repr.symm.norm_map]
    exact (norm_euclideanGridPoint_le hm hM η hη.le (e i)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le d 1) hη.le)
  have hrR : radius + (d : ℝ) * η ≤ R := by
    rw [hradius]
    have hsmall : η / (16 * x) ≤ η / 16 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * x) (by norm_num : (0 : ℝ) < 16)).mpr
      nlinarith
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    dsimp [η] at hsmall ⊢
    field_simp at hsmall ⊢
    nlinarith
  have hcentsep : Pairwise (fun i j : Fin N ↦ 8 * radius ≤ dist (z i) (z j)) := by
    intro i j hij
    have hmesh := euclideanGridPoint_separated hM η hη.le (fun h ↦ hij (e.injective h))
    have hdists : dist (z i) (z j) = dist (euclideanGridPoint η (e i)) (euclideanGridPoint η (e j)) := by
      dsimp [z]
      rw [dist_add_left]
      exact b.repr.symm.isometry.dist_eq _ _
    rw [hdists]
    apply le_trans ?_ hmesh
    rw [hradius]
    have hMbound' : (M : ℝ) ≤ 2 * x := hMbound
    apply (le_div_iff₀ hMR).mpr
    field_simp
    nlinarith
  refine ⟨z, fun i ↦ ?_, hcentsep⟩
  apply Set.Subset.trans ?_ hball
  apply Metric.ball_subset_ball'
  have hdist : dist (z i) w ≤ (d : ℝ) * η := by
    simpa only [z, dist_eq_norm, add_sub_cancel_left] using hoffset i
  linarith

end Antichain
