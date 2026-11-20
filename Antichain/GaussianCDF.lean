import Antichain.Support
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! The actual standard-normal cumulative distribution function. -/

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology ENNReal NNReal

/-- The standard Gaussian CDF `Φ`, using Mathlib's probability measure. -/
noncomputable def normalCDF : ℝ → ℝ := cdf (gaussianReal 0 1)

/-- This probability-law CDF is exactly the integral of the paper's printed
standard-normal density over `(-∞, x]`. -/
theorem normalCDF_eq_integral (x : ℝ) :
    normalCDF x = ∫ t in Iic x,
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
  rw [normalCDF, cdf_eq_real, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun t => gaussianPDFReal_nonneg 0 1 t))]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]

theorem normalCDF_tendsto_atBot : Tendsto normalCDF atBot (𝓝 0) :=
  tendsto_cdf_atBot _

theorem normalCDF_tendsto_atTop : Tendsto normalCDF atTop (𝓝 1) :=
  tendsto_cdf_atTop _

/-- Positive Gaussian density gives strictly positive mass to every nonempty interval. -/
theorem gaussianReal_Ioc_pos {a b : ℝ} (hab : a < b) :
    0 < gaussianReal 0 1 (Ioc a b) := by
  by_contra! hzero
  have hz : gaussianReal 0 1 (Ioc a b) = 0 := le_antisymm hzero bot_le
  have hv := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero hz
  have hvol : 0 < (volume : Measure ℝ) (Ioc a b) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact (ne_of_gt hvol) hv

theorem normalCDF_strictMono : StrictMono normalCDF := by
  intro a b hab
  have hp := gaussianReal_Ioc_pos hab
  rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc] at hp
  have := ENNReal.ofReal_pos.mp hp
  change cdf (gaussianReal 0 1) a < cdf (gaussianReal 0 1) b
  linarith

theorem normalCDF_continuous : Continuous normalCDF := by
  let μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)
  letI : NoAtoms μ := noAtoms_gaussianReal one_ne_zero
  have hc : Continuous (cdf μ : ℝ → ℝ) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
    have hzero : ENNReal.ofReal (cdf μ x - leftLim (cdf μ) x) = 0 := by
      rw [← StieltjesFunction.measure_singleton, measure_cdf μ]
      exact measure_singleton x
    have hle := ENNReal.ofReal_eq_zero.mp hzero
    have hleft : leftLim (cdf μ) x = cdf μ x := by
      apply le_antisymm ((monotone_cdf μ).leftLim_le le_rfl)
      linarith
    rw [hleft, (cdf μ).rightLim_eq]
  exact hc

theorem normalCDF_mem_Ioo (x : ℝ) : normalCDF x ∈ Ioo 0 1 := by
  have hlo := normalCDF_strictMono (show x - 1 < x by linarith)
  have hhi := normalCDF_strictMono (show x < x + 1 by linarith)
  have hn : 0 ≤ normalCDF (x - 1) := cdf_nonneg _ _
  have ho : normalCDF (x + 1) ≤ 1 := cdf_le_one _ _
  exact ⟨lt_of_le_of_lt hn hlo, lt_of_lt_of_le hhi ho⟩

theorem normalCDF_surjOn_Ioo : SurjOn normalCDF univ (Ioo 0 1) := by
  intro y hy
  obtain ⟨a, ha⟩ := (normalCDF_tendsto_atBot.eventually (eventually_lt_nhds hy.1)).exists
  obtain ⟨b, hb⟩ := (normalCDF_tendsto_atTop.eventually (eventually_gt_nhds hy.2)).exists
  obtain ⟨x, hx⟩ := intermediate_value_univ a b normalCDF_continuous ⟨ha.le, hb.le⟩
  exact ⟨x, mem_univ x, hx⟩

theorem normalCDF_onto_Ioo (y : ℝ) (hy : y ∈ Ioo 0 1) :
    ∃ x, normalCDF x = y := by
  obtain ⟨x, _, hx⟩ := normalCDF_surjOn_Ioo hy
  exact ⟨x, hx⟩

theorem normalCDF_range : range normalCDF = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact normalCDF_mem_Ioo x
  · exact normalCDF_onto_Ioo y

/-- The paper's deterministic comparison conclusion, now for the actual `Φ`. -/
theorem normalCDF_cube_outside_candidate_exists_comparable
    {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hout : x ∉ candidateClosedSurface normalCDF) :
    ∃ y ∈ coordinateImageSurface normalCDF, StrictBelow x y ∨ StrictBelow y x := by
  exact cube_outside_candidateClosedSurface_exists_comparable normalCDF normalCDF_strictMono
    normalCDF_mem_Ioo normalCDF_onto_Ioo x hx hout

end Antichain
