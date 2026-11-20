import Antichain.LipschitzCubeTests

/-! Exponential test concentration for the actual conditional uniform cube sample. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

theorem gaussian_cube_test_exponential_tail (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      gaussianAntichainLaw n d {G | epsilon ≤
        |(∑ j, g (gaussianToCubePoint d (G j))) / (n : ℝ) -
          ∫ x, g x ∂limitingAntichainMeasure (Fin d)|} ≤
            ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) :=
  gaussian_cube_test_exponential_tail_lipschitz hd H g hepsilon


theorem cube_test_exponential_tail (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | epsilon ≤ |(∑ j, g (x j)) / (n : ℝ) -
        ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} ≤
          ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := gaussian_cube_test_exponential_tail hd H g hepsilon
  refine ⟨alpha, ha, htail.mono ?_⟩
  intro n hn
  have hcontinuous : Continuous (fun x : CubeSample n d =>
      |(∑ j, g (x j)) / (n : ℝ) - ∫ u, g u ∂limitingAntichainMeasure (Fin d)|) := by fun_prop
  have hE : MeasurableSet {x : CubeSample n d | epsilon ≤
      |(∑ j, g (x j)) / (n : ℝ) - ∫ u, g u ∂limitingAntichainMeasure (Fin d)|} :=
    (isClosed_le continuous_const hcontinuous).measurableSet
  rw [← gaussianToCubeSample_conditional_map_eq n d,
    Measure.map_apply (continuous_gaussianToCubeSample n d).measurable hE]
  exact hn

end Antichain
