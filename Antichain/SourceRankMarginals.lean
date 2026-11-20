import Antichain.FinalIntervalApplication

/-! Exact source midpoint-grid marginals and deterministic coordinate averages. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The actual uniform midpoint grid, with the empirical-measure convention at n=0. -/
def midpointGridLaw (n : ℕ) : Measure ℝ :=
  if n = 0 then Measure.dirac 0 else (n : ℝ≥0∞)⁻¹ • ∑ j : Fin n, Measure.dirac (rankMidpoint n j)

instance midpointGridLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (midpointGridLaw n) := by
  classical
  by_cases hn : n = 0
  · simp only [midpointGridLaw, if_pos hn]
    infer_instance
  · constructor
    simp only [midpointGridLaw, if_neg hn, Measure.smul_apply, Measure.finset_sum_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top _)

theorem rankCenterEmpirical_coordinate_map (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (i : Fin d) :
    (empiricalCubeProbability n d (rankCenterCloud n d r) : Measure (CubePoint d)).map (fun x ↦ x i) =
      midpointGridLaw n := by
  change (empiricalCubeMeasure n d (rankCenterCloud n d r)).map (fun x ↦ x i) = _
  by_cases hn : n = 0
  · simp only [empiricalCubeMeasure, midpointGridLaw, if_pos hn]
    exact Measure.map_dirac (measurable_pi_apply i) 0
  · rw [empiricalCubeMeasure, if_neg hn, midpointGridLaw, if_neg hn, Measure.map_smul,
      ← Measure.sum_fintype, Measure.map_sum (measurable_pi_apply i).aemeasurable, Measure.sum_fintype]
    simp_rw [Measure.map_dirac (measurable_pi_apply i)]
    exact congrArg (fun μ : Measure ℝ ↦ (n : ℝ≥0∞)⁻¹ • μ)
      (Equiv.sum_comp (r i) (fun j ↦ Measure.dirac (rankMidpoint n j)))

theorem rankEmpiricalProbability_coordinate_map (n d : ℕ) (x : CubeSample n d) (i : Fin d) :
    (rankEmpiricalProbability n d x : Measure (CubePoint d)).map (fun y ↦ y i) = midpointGridLaw n :=
  rankCenterEmpirical_coordinate_map n d (coordinateRankPermutations n d x) i

theorem permutationRankEmpiricalProbability_coordinate_map (n m : ℕ)
    (π : Fin m → Equiv.Perm (Fin n)) (i : Fin (m + 1)) :
    (permutationRankEmpiricalProbability n m π : Measure (CubePoint (m + 1))).map (fun y ↦ y i) =
      midpointGridLaw n :=
  rankCenterEmpirical_coordinate_map n (m + 1) (Fin.cons (Equiv.refl _) π) i

theorem sum_rankMidpoint (n : ℕ) : (∑ j : Fin n, rankMidpoint n j) = (n : ℝ) / 2 := by
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun j ↦ rankMidpoint n j)
  simp only [Fin.revPerm_apply, rankMidpoint_rev, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  linarith

theorem rankCenterCloud_coordinate_average (n d : ℕ) (hn : 0 < n)
    (r : Fin d → Equiv.Perm (Fin n)) (i : Fin d) :
    (∑ j, rankCenterCloud n d r j i) / (n : ℝ) = 1 / 2 := by
  change (∑ j, rankMidpoint n (r i j)) / (n : ℝ) = _
  rw [Equiv.sum_comp (r i), sum_rankMidpoint]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

theorem empiricalCubeMeasure_coordinate_integral (n d : ℕ) (hn : 0 < n) (x : CubeSample n d) (i : Fin d) :
    (∫ y, y i ∂empiricalCubeMeasure n d x) = (∑ j, x j i) / (n : ℝ) := by
  rw [empiricalCubeMeasure, if_neg hn.ne', integral_smul_measure,
    integral_finset_sum_measure (fun j _ ↦ integrable_dirac (by simp : ‖x j i‖ₑ < ⊤))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _

theorem rankCenterEmpirical_coordinate_mean (n d : ℕ) (hn : 0 < n)
    (r : Fin d → Equiv.Perm (Fin n)) (i : Fin d) :
    (∫ y, y i ∂(empiricalCubeProbability n d (rankCenterCloud n d r) : Measure (CubePoint d))) = 1 / 2 := by
  rw [show (empiricalCubeProbability n d (rankCenterCloud n d r) : Measure (CubePoint d)) =
      empiricalCubeMeasure n d (rankCenterCloud n d r) from rfl,
    empiricalCubeMeasure_coordinate_integral n d hn, rankCenterCloud_coordinate_average n d hn]

theorem rankEmpiricalProbability_coordinate_average (n d : ℕ) (hn : 0 < n)
    (x : CubeSample n d) (i : Fin d) : (∑ j, cubeRankCloud n d x j i) / (n : ℝ) = 1 / 2 :=
  rankCenterCloud_coordinate_average n d hn (coordinateRankPermutations n d x) i

theorem permutationRankCloud_coordinate_average (n m : ℕ) (hn : 0 < n)
    (π : Fin m → Equiv.Perm (Fin n)) (i : Fin (m + 1)) :
    (∑ j, permutationRankCloud n m π j i) / (n : ℝ) = 1 / 2 :=
  rankCenterCloud_coordinate_average n (m + 1) hn (Fin.cons (Equiv.refl _) π) i

end Antichain
