import Antichain.CubeProbabilitySpace

/-! Literal convergence-in-probability consequences of the proved exponential
empirical bounds, including relative continuity sets in the actual closed cube. -/

noncomputable section

namespace Antichain

open Filter MeasureTheory Set
open scoped Topology ENNReal

theorem exponential_tail_tendsto_zero (p : ℕ → ℝ≥0∞) {α : ℝ} (hα : 0 < α)
    (hp : ∀ᶠ n : ℕ in atTop, p n ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ)))) :
    Tendsto p atTop (𝓝 0) := by
  have hmul : Tendsto (fun n : ℕ => α * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hα tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun n : ℕ => -α * (n : ℝ)) atTop atBot := by
    simpa only [neg_mul] using tendsto_neg_atTop_atBot.comp hmul
  have he := ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp hneg)
  simp only [ENNReal.ofReal_zero] at he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) he
    (Eventually.of_forall (fun n => bot_le)) hp

theorem empirical_continuity_set_in_probability {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) {B : Set (CubePoint d)}
    (hB : limitingAntichainMeasure (Fin d) (frontier B) = 0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => cubeAntichainLaw n d {x | ε ≤
      |empiricalSetFrequency n d B x - (limitingAntichainMeasure (Fin d) B).toReal|})
      atTop (𝓝 0) := by
  obtain ⟨α, hα, htail⟩ := empirical_continuity_set_concentration hd H hB hε
  exact exponential_tail_tendsto_zero _ hα htail

/-- The printed Borel continuity-set consequence, on the literal closed cube,
with its relative frontier, actual sample law and literal count fraction. -/
theorem closed_cube_continuity_set_in_probability {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) {B : Set (ClosedCubePoint d)}
    (hB : MeasurableSet B)
    (hfrontier : (closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) (frontier B) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => closedCubeAntichainLaw n d {x | ε ≤ |empiricalClosedSetFrequency n d B x -
      ((closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) B).toReal|})
      atTop (𝓝 0) := by
  obtain ⟨α, hα, htail⟩ := closed_cube_continuity_set_concentration hd H hB hfrontier hε
  exact exponential_tail_tendsto_zero _ hα htail

end Antichain
