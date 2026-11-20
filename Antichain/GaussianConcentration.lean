import Antichain.ConditionalMoments
import Antichain.ExponentialTail
import Antichain.EmpiricalTopology

/-! Actual conditional height and floor-test exponential concentration. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

theorem gaussian_height_exponential_tail (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      (gaussianAntichainLaw n d).real {g | delta * (n : ℝ) ≤ totalSquaredHeight n g} ≤
        Real.exp (-alpha * (n : ℝ)) := by
  letI (n : ℕ) : IsProbabilityMeasure (gaussianAntichainLaw n d) :=
    gaussianAntichainLaw_isProbabilityMeasure n d hd
  apply exponential_tail_of_log_moment_gap (fun n => gaussianAntichainLaw n d)
    (fun n g => totalSquaredHeight n g) (theta := 1 / 4) (L := 0) (by norm_num)
  · intro n
    have hi := conditional_gaussianWeight_integrable n (0 : FloorSpace (Fin d) →ᵇ ℝ) (1 / 4)
      (by norm_num) hd
    have heq : gaussianWeight n (0 : FloorSpace (Fin d) →ᵇ ℝ) (1 / 4) =
        (fun g : CubeSample n d => Real.exp ((1 / 4) * totalSquaredHeight n g)) :=
      funext (gaussianWeight_zero_eq_height_exp n (1 / 4))
    rwa [heq] at hi
  · exact conditional_height_exp_log_limit hd H (1 / 4) (by norm_num)
  · positivity

theorem gaussian_floor_centered_upper_tail (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (f : FloorSpace (Fin d) →ᵇ ℝ) (hmean : (∫ u, f u ∂limitingFloorLaw d) = 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      (gaussianAntichainLaw n d).real
        {g | delta * (n : ℝ) ≤ ∑ j, f (actualFloor (g j))} ≤
          Real.exp (-alpha * (n : ℝ)) := by
  letI (n : ℕ) : IsProbabilityMeasure (gaussianAntichainLaw n d) :=
    gaussianAntichainLaw_isProbabilityMeasure n d hd
  let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < p := by dsimp [p]; exact div_pos (by linarith) (by linarith)
  obtain ⟨theta, htheta, htilt⟩ := boundedTest_exists_negative_tilt
    (limitingFloorLaw d) f hmean hp hdelta
  let L : ℝ := (1 / p) * cgf (f : FloorSpace (Fin d) → ℝ) (limitingFloorLaw d) (p * theta)
  have hexp (n : ℕ) (g : CubeSample n d) :
      gaussianWeight n (theta • f) 0 g = Real.exp (theta * ∑ j, f (actualFloor (g j))) := by
    unfold gaussianWeight gaussianWeightExponent
    simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul,
      zero_mul, add_zero, Finset.mul_sum]
  have hI (n : ℕ) : Integrable (fun g : CubeSample n d =>
      Real.exp (theta * ∑ j, f (actualFloor (g j)))) (gaussianAntichainLaw n d) := by
    have hi := conditional_gaussianWeight_integrable n (theta • f) 0 (by norm_num) hd
    have heq : gaussianWeight n (theta • f) 0 =
        (fun g : CubeSample n d => Real.exp (theta * ∑ j, f (actualFloor (g j)))) := funext (hexp n)
    rwa [heq] at hi
  have hrecip : 1 / p = (d : ℝ) / ((d : ℝ) - 1) := by dsimp [p]; field_simp
  have hmgf : mgf ((theta • f : FloorSpace (Fin d) →ᵇ ℝ) : FloorSpace (Fin d) → ℝ)
      (limitingFloorLaw d) p = mgf (f : FloorSpace (Fin d) → ℝ) (limitingFloorLaw d) (p * theta) := by
    change mgf (theta • (f : FloorSpace (Fin d) → ℝ)) (limitingFloorLaw d) p = _
    rw [mgf_smul_left, mul_comm theta p]
  have hLimit : Tendsto (fun n : ℕ => Real.log
      (∫ g : CubeSample n d, Real.exp (theta * ∑ j, f (actualFloor (g j)))
        ∂gaussianAntichainLaw n d) / (n : ℝ)) atTop (𝓝 L) := by
    have h := conditional_gaussianWeight_log_limit hd H (theta • f) 0 (by norm_num)
    change Tendsto _ atTop (𝓝 ((d : ℝ) / ((d : ℝ) - 1) *
      Real.log (mgf ((theta • f : FloorSpace (Fin d) →ᵇ ℝ) : FloorSpace (Fin d) → ℝ)
        (limitingFloorLaw d) p))) at h
    rw [hmgf] at h
    simpa only [hexp, L, cgf, hrecip] using h
  have hgap : L < theta * delta := by
    change -theta * delta + L < -theta * delta / 2 at htilt
    nlinarith [mul_pos htheta hdelta]
  exact exponential_tail_of_log_moment_gap (fun n => gaussianAntichainLaw n d)
    (fun n g => ∑ j, f (actualFloor (g j))) htheta hI hLimit hgap

def centeredFloorTest (f : FloorSpace (Fin d) →ᵇ ℝ) : FloorSpace (Fin d) →ᵇ ℝ :=
  f - BoundedContinuousFunction.const _ (∫ u, f u ∂limitingFloorLaw d)

theorem centeredFloorTest_integral (f : FloorSpace (Fin d) →ᵇ ℝ) :
    (∫ u, centeredFloorTest f u ∂limitingFloorLaw d) = 0 := by
  change (∫ u, f u - (∫ v, f v ∂limitingFloorLaw d) ∂limitingFloorLaw d) = 0
  rw [integral_sub (f.integrable (μ := limitingFloorLaw d))
    (integrable_const (μ := limitingFloorLaw d) _)]
  simp

theorem centeredFloorTest_average (f : FloorSpace (Fin d) →ᵇ ℝ) (n : ℕ) (hn : 0 < n)
    (g : CubeSample n d) :
    (∑ j, centeredFloorTest f (actualFloor (g j))) / (n : ℝ) =
      (∑ j, f (actualFloor (g j))) / (n : ℝ) - ∫ u, f u ∂limitingFloorLaw d := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (∑ j, (f (actualFloor (g j)) - ∫ u, f u ∂limitingFloorLaw d)) / (n : ℝ) = _
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem gaussian_floor_test_exponential_tail (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (f : FloorSpace (Fin d) →ᵇ ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      gaussianAntichainLaw n d {g | delta ≤
        |(∑ j, f (actualFloor (g j))) / (n : ℝ) - ∫ u, f u ∂limitingFloorLaw d|} ≤
          ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  letI (n : ℕ) : IsProbabilityMeasure (gaussianAntichainLaw n d) :=
    gaussianAntichainLaw_isProbabilityMeasure n d hd
  let F := centeredFloorTest f
  have hF : (∫ u, F u ∂limitingFloorLaw d) = 0 := centeredFloorTest_integral f
  have hnegF : (∫ u, (-F) u ∂limitingFloorLaw d) = 0 := by
    change (∫ u, -(F u) ∂limitingFloorLaw d) = 0
    rw [integral_neg, hF, neg_zero]
  have hTail (b : Bool) :
      ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
        gaussianAntichainLaw n d {g | delta * (n : ℝ) ≤
          ∑ j, (if b then F else -F) (actualFloor (g j))} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    have hcenter : (∫ u, (if b then F else -F) u ∂limitingFloorLaw d) = 0 := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hF, hnegF]
    obtain ⟨alpha, ha, htail⟩ := gaussian_floor_centered_upper_tail hd H
      (if b then F else -F) hcenter hdelta
    refine ⟨alpha, ha, htail.mono ?_⟩
    intro n hn
    rw [← ENNReal.ofReal_toReal (measure_ne_top (gaussianAntichainLaw n d) _)]
    exact ENNReal.ofReal_le_ofReal hn
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail
    (I := Bool) (Ω := fun n => CubeSample n d) (fun n => gaussianAntichainLaw n d)
    (fun (b : Bool) (n : ℕ) => {g : CubeSample n d |
      delta * (n : ℝ) ≤ ∑ j, (if b then F else -F) (actualFloor (g j))}) hTail
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply le_trans (measure_mono ?_) hn
  intro g hg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  change delta ≤ |(∑ j, f (actualFloor (g j))) / (n : ℝ) - ∫ u, f u ∂limitingFloorLaw d| at hg
  rw [← centeredFloorTest_average f n hnpos g, abs_div, abs_of_pos hnR] at hg
  have hh := (le_div_iff₀ hnR).mp hg
  rcases le_abs.mp hh with hpos | hneg
  · exact Set.mem_iUnion.mpr ⟨true, by exact hpos⟩
  · exact Set.mem_iUnion.mpr ⟨false, by
      change delta * (n : ℝ) ≤ ∑ j, -(F (actualFloor (g j)))
      rw [Finset.sum_neg_distrib]
      exact hneg⟩

end Antichain
