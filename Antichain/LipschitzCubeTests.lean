import Antichain.GaussianConcentration
import Antichain.CubeTestFloorError
import Mathlib.Topology.MetricSpace.Lipschitz
import Antichain.LipschitzStoneWeierstrass

/-! Uniform Lipschitz approximation and the manuscript's height-square-root
transfer for continuous empirical tests. -/
noncomputable section
namespace Antichain
open MeasureTheory Set Finset Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal

theorem mean_abs_le_sqrt_mean_sq {n : ℕ} (hn : 0 < n) (h : Fin n → ℝ) :
    (∑ j, |h j|) / (n : ℝ) ≤ Real.sqrt ((∑ j, h j ^ 2) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 ≤ ∑ j, h j ^ 2 := sum_nonneg (fun j _ => sq_nonneg _)
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := fun j => |h j|)
  simp only [card_univ, Fintype.card_fin, sq_abs] at hc
  have hsq : ((∑ j, |h j|) / (n : ℝ)) ^ 2 ≤ (∑ j, h j ^ 2) / (n : ℝ) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hnR 2) hnR).mpr
    nlinarith
  exact (sq_le_sq₀ (div_nonneg (sum_nonneg (fun _ _ => abs_nonneg _)) hnR.le)
    (Real.sqrt_nonneg _)).mp (hsq.trans_eq (Real.sq_sqrt (div_nonneg hS hnR.le)).symm)

variable {d : ℕ} [NeZero d]

/-- The exact Lipschitz/Cauchy--Schwarz height transfer written in Theorem 2.1. -/
theorem lipschitz_cubeTest_empirical_floor_error (f : CubePoint d →ᵇ ℝ)
    {K : ℝ≥0} (hf : LipschitzWith K f) (n : ℕ) (hn : 0 < n) (G : CubeSample n d) :
    |(∑ j, f (gaussianToCubePoint d (G j))) / n -
      (∑ j, cubeTestOnFloor f (actualFloor (G j))) / n| ≤
        ((K * normalCDFLipschitzConstant : ℝ≥0) : ℝ) *
          Real.sqrt ((∑ j, actualHeight (G j) ^ 2) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = |∑ j, (f (gaussianToCubePoint d (G j)) - cubeTestOnFloor f (actualFloor (G j)))| / n := by
      rw [sum_sub_distrib, ← sub_div, abs_div, abs_of_pos hnR]
    _ ≤ (∑ j, |f (gaussianToCubePoint d (G j)) - cubeTestOnFloor f (actualFloor (G j))|) / n :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ (∑ j, (K : ℝ) * ((normalCDFLipschitzConstant : ℝ) * |actualHeight (G j)|)) / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply sum_le_sum
      intro j _
      exact (hf.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (gaussianToCubePoint_dist_floor_le_height (G j)) K.coe_nonneg)
    _ = ((K * normalCDFLipschitzConstant : ℝ≥0) : ℝ) * ((∑ j, |actualHeight (G j)|) / n) := by
      simp only [NNReal.coe_mul, ← mul_assoc, ← mul_sum, mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mean_abs_le_sqrt_mean_sq hn _) (by positivity)

theorem cubeTest_uniform_approximation_error (g f : CubePoint d →ᵇ ℝ)
    {ε : ℝ} (hgf : ∀ x ∈ cubePointSet d, |g x - f x| ≤ ε)
    (n : ℕ) (hn : 0 < n) (G : CubeSample n d) :
    |(∑ j, g (gaussianToCubePoint d (G j))) / n -
      (∑ j, f (gaussianToCubePoint d (G j))) / n| ≤ ε ∧
    |(∫ x, g x ∂limitingAntichainMeasure (Fin d)) -
      (∫ x, f x ∂limitingAntichainMeasure (Fin d))| ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · calc
      _ = |∑ j, (g (gaussianToCubePoint d (G j)) - f (gaussianToCubePoint d (G j)))| / n := by
        rw [sum_sub_distrib, ← sub_div, abs_div, abs_of_pos hnR]
      _ ≤ (∑ j, |g (gaussianToCubePoint d (G j)) - f (gaussianToCubePoint d (G j))|) / n :=
        div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hnR.le
      _ ≤ (∑ _ : Fin n, ε) / n := div_le_div_of_nonneg_right
        (sum_le_sum (fun j _ => hgf _ (gaussianToCubePoint_mem_cube (G j)))) hnR.le
      _ = ε := by simp [hnR.ne']
  · rw [← cubeTestOnFloor_integral g, ← cubeTestOnFloor_integral f,
      ← integral_sub ((cubeTestOnFloor g).integrable (μ := limitingFloorLaw d))
        ((cubeTestOnFloor f).integrable (μ := limitingFloorLaw d))]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ _ : FloorSpace (Fin d), ε ∂limitingFloorLaw d := integral_mono
        ((((cubeTestOnFloor g).integrable (μ := limitingFloorLaw d)).sub
          ((cubeTestOnFloor f).integrable (μ := limitingFloorLaw d))).abs)
        (integrable_const ε) (fun u => hgf _ (normalCDFFloorMap_mem_cube u))
      _ = ε := by simp

theorem cubeTest_approximation_sqrt_transfer (g : CubePoint d →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : CubePoint d →ᵇ ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, 0 < n →
      ∀ G : CubeSample n d,
      |(∑ j, g (gaussianToCubePoint d (G j))) / n -
        ∫ x, g x ∂limitingAntichainMeasure (Fin d)| ≤
        2 * ε + L * Real.sqrt ((∑ j, actualHeight (G j) ^ 2) / n) +
        |(∑ j, cubeTestOnFloor f (actualFloor (G j))) / n -
          ∫ u, cubeTestOnFloor f u ∂limitingFloorLaw d| := by
  classical
  obtain ⟨f, K, hf, happrox⟩ := cube_lipschitz_approximation_stoneWeierstrass d g hε
  have happ : ∀ x ∈ cubePointSet d, |g x - f x| ≤ ε := by
    intro x hx
    exact (happrox x hx).le
  refine ⟨f, ((K * normalCDFLipschitzConstant : ℝ≥0) : ℝ), by positivity, ?_⟩
  intro n hn G
  obtain ⟨ha, hi⟩ := cubeTest_uniform_approximation_error g f happ n hn G
  have he := lipschitz_cubeTest_empirical_floor_error f hf n hn G
  have htri := abs_sub_le ((∑ j, g (gaussianToCubePoint d (G j))) / n)
    ((∑ j, f (gaussianToCubePoint d (G j))) / n)
    (∫ x, g x ∂limitingAntichainMeasure (Fin d))
  have htri₂ := abs_sub_le ((∑ j, f (gaussianToCubePoint d (G j))) / n)
    ((∑ j, cubeTestOnFloor f (actualFloor (G j))) / n)
    (∫ x, g x ∂limitingAntichainMeasure (Fin d))
  have htri₃ := abs_sub_le ((∑ j, cubeTestOnFloor f (actualFloor (G j))) / n)
    (∫ x, f x ∂limitingAntichainMeasure (Fin d))
    (∫ x, g x ∂limitingAntichainMeasure (Fin d))
  rw [abs_sub_comm] at hi
  rw [← cubeTestOnFloor_integral f] at htri₃ hi
  linarith

theorem gaussian_cube_test_exponential_tail_lipschitz (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      gaussianAntichainLaw n d {G | epsilon ≤
        |(∑ j, g (gaussianToCubePoint d (G j))) / (n : ℝ) -
          ∫ x, g x ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  letI (n : ℕ) : IsProbabilityMeasure (gaussianAntichainLaw n d) :=
    gaussianAntichainLaw_isProbabilityMeasure n d hd
  obtain ⟨f, L, hL, herr⟩ := cubeTest_approximation_sqrt_transfer g
    (show 0 < epsilon / 8 by positivity)
  let eta : ℝ := epsilon / (4 * (L + 1))
  let delta : ℝ := eta ^ 2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hdelta : 0 < delta := sq_pos_of_pos heta
  have hLeta : L * eta ≤ epsilon / 4 := by
    dsimp [eta]
    calc
      _ = epsilon / 4 * (L / (L + 1)) := by field_simp
      _ ≤ epsilon / 4 := mul_le_of_le_one_right (by positivity)
        ((div_le_one (by positivity : 0 < L + 1)).mpr (by linarith))
  obtain ⟨ah, hah, hheight⟩ := gaussian_height_exponential_tail hd H hdelta
  have hheightE : ∀ᶠ n : ℕ in atTop,
      gaussianAntichainLaw n d {G | delta * (n : ℝ) ≤ totalSquaredHeight n G} ≤
        ENNReal.ofReal (Real.exp (-ah * (n : ℝ))) := by
    filter_upwards [hheight] with n hn
    rw [← ENNReal.ofReal_toReal (measure_ne_top (gaussianAntichainLaw n d) _)]
    exact ENNReal.ofReal_le_ofReal hn
  obtain ⟨af, haf, hfloor⟩ := gaussian_floor_test_exponential_tail hd H (cubeTestOnFloor f)
    (show 0 < epsilon / 4 by positivity)
  let A : Bool → ∀ n : ℕ, Set (CubeSample n d) := fun b n =>
    if b then {G | delta * (n : ℝ) ≤ totalSquaredHeight n G}
    else {G | epsilon / 4 ≤
      |(∑ j, cubeTestOnFloor f (actualFloor (G j))) / (n : ℝ) -
        ∫ u, cubeTestOnFloor f u ∂limitingFloorLaw d|}
  have hA (b : Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      gaussianAntichainLaw n d (A b n) ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    cases b
    · exact ⟨af, haf, hfloor⟩
    · exact ⟨ah, hah, hheightE⟩
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail
    (I := Bool) (Ω := fun n => CubeSample n d) (fun n => gaussianAntichainLaw n d) A hA
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  apply le_trans (measure_mono ?_) hn
  intro G hG
  change epsilon ≤ |(∑ j, g (gaussianToCubePoint d (G j))) / (n : ℝ) -
    ∫ x, g x ∂limitingAntichainMeasure (Fin d)| at hG
  by_contra hnot
  have hheightSmall : totalSquaredHeight n G < delta * (n : ℝ) :=
    lt_of_not_ge (fun h => hnot (Set.mem_iUnion.mpr ⟨true, h⟩))
  have hfloorSmall :
      |(∑ j, cubeTestOnFloor f (actualFloor (G j))) / (n : ℝ) -
        ∫ u, cubeTestOnFloor f u ∂limitingFloorLaw d| < epsilon / 4 :=
    lt_of_not_ge (fun h => hnot (Set.mem_iUnion.mpr ⟨false, h⟩))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hheightAvg : (∑ j, actualHeight (G j) ^ 2) / (n : ℝ) < eta ^ 2 :=
    (div_lt_iff₀ hnR).mpr hheightSmall
  have hsqrt := (Real.sqrt_lt' heta).mpr hheightAvg
  have hm := mul_le_mul_of_nonneg_left hsqrt.le hL
  have he := herr n hnpos G
  linarith

end Antichain
