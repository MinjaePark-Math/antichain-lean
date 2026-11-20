import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.UniformOn

/-! Conditioning an actual finite uniform law gives the actual uniform law on the event. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {K : Type*} [Fintype K] [Nonempty K] [MeasurableSpace K]
  [MeasurableSingletonClass K]

theorem finite_uniform_toMeasure_eq_uniformOn_univ :
    (PMF.uniformOfFintype K).toMeasure = uniformOn (univ : Set K) := by
  apply Measure.ext_of_singleton
  intro k
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), uniformOn_univ]
  simp

/-- No positivity premise is needed for this equality: empty events give zero on both sides. -/
theorem finite_uniform_restrict_normalize_eq_uniformOn (C : Set K) :
    ((PMF.uniformOfFintype K).toMeasure C)⁻¹ •
      (PMF.uniformOfFintype K).toMeasure.restrict C = uniformOn C := by
  have hC : MeasurableSet C := C.toFinite.measurableSet
  change ProbabilityTheory.cond (PMF.uniformOfFintype K).toMeasure C = uniformOn C
  rw [finite_uniform_toMeasure_eq_uniformOn_univ]
  change ProbabilityTheory.cond (ProbabilityTheory.cond (Measure.count : Measure K) univ) C =
    ProbabilityTheory.cond Measure.count C
  simpa only [univ_inter] using cond_cond_eq_cond_inter MeasurableSet.univ hC (Measure.count : Measure K)

theorem finite_uniform_restrict_normalize_isProbabilityMeasure {C : Set K} (hC : C.Nonempty) :
    IsProbabilityMeasure (((PMF.uniformOfFintype K).toMeasure C)⁻¹ •
      (PMF.uniformOfFintype K).toMeasure.restrict C) := by
  rw [finite_uniform_restrict_normalize_eq_uniformOn]
  exact uniformOn_isProbabilityMeasure C.toFinite hC

end Antichain
