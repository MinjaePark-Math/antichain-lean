import Antichain.SimplicialGridWeights
import Antichain.SimplicialInterpolationRegularity
import Mathlib.Topology.Instances.RealVectorSpace

/-! Uniform approximation by the actual finite grid-hat interpolant.
Partition unity and the actual support diameter are proved in GridWeights;
no approximation or triangulation conclusion is a hypothesis here. -/

noncomputable section

namespace Antichain

open Set Finset Metric
open scoped Topology BoundedContinuousFunction

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem exists_simplicialInterpolant_uniform_approximation
    (g : (ι → ℝ) →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : ι → ℝ, (∀ i, x i ∈ Icc (0 : ℝ) 1) →
      |g x - simplicialInterpolantBCF N g x| < epsilon := by
  classical
  let C : Set (ι → ℝ) := Set.univ.pi (fun _ => Icc (0 : ℝ) 1)
  have hcompact : IsCompact C := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨delta, hdelta, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous g.continuous.continuousOn)
      (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 : ℝ) / delta)
  have hNpos : 0 < N := by exact_mod_cast (lt_trans (by positivity : (0 : ℝ) < 1 / delta) hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmesh : (1 : ℝ) / N < delta := by
    have hh := (div_lt_iff₀ hdelta).mp hN
    apply (div_lt_iff₀ hNR).mpr
    nlinarith
  refine ⟨N, hNpos, ?_⟩
  intro x hx
  have hsum := sum_scaledSimplicialGridHat N x hx
  have hidentity : g x - simplicialInterpolantBCF N g x =
      ∑ v : SimplicialGridVertex ι N,
        (g x - g (simplicialGridPoint v)) * scaledSimplicialGridHat N x v := by
    rw [simplicialInterpolantBCF_apply]
    simp_rw [sub_mul]
    rw [sum_sub_distrib, ← mul_sum, hsum, mul_one]
  rw [hidentity]
  have hbound : (∑ v : SimplicialGridVertex ι N,
      |(g x - g (simplicialGridPoint v)) * scaledSimplicialGridHat N x v|) ≤
      epsilon / 2 := by
    calc
      _ ≤ ∑ v : SimplicialGridVertex ι N, (epsilon / 2) * scaledSimplicialGridHat N x v := by
        apply sum_le_sum
        intro v _
        have hw : 0 ≤ scaledSimplicialGridHat N x v := simplicialGridHat_nonneg _ _
        rw [abs_mul, abs_of_nonneg hw]
        by_cases hwpos : 0 < scaledSimplicialGridHat N x v
        · have hdist := (scaledSimplicialGridHat_support_dist hNpos x v hwpos).trans_lt hmesh
          have herr := huc x (fun i _ => hx i) (simplicialGridPoint v)
            (fun i _ => simplicialGridPoint_mem_cube hNpos v i) hdist
          rw [Real.dist_eq] at herr
          exact mul_le_mul_of_nonneg_right herr.le hw
        · have hz : scaledSimplicialGridHat N x v = 0 := le_antisymm (le_of_not_gt hwpos) hw
          simp only [hz, mul_zero, le_refl]
      _ = epsilon / 2 := by rw [← mul_sum, hsum, mul_one]
  exact lt_of_le_of_lt ((abs_sum_le_sum_abs _ _).trans hbound) (half_lt_self hepsilon)

end Antichain
