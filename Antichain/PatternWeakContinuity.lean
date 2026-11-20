import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Finite independent sampling and continuity-set probabilities in the actual
weak topology. Pattern chambers and their null boundaries are supplied by the
concrete pattern module; no pattern-continuity conclusion is an input here. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]

/-- Taking a fixed finite number of independent samples is weakly continuous. -/
theorem iidProbability_continuous (q : ℕ) :
    Continuous (fun ν : ProbabilityMeasure E =>
      ProbabilityMeasure.pi (fun _ : Fin q => ν)) :=
  ProbabilityMeasure.continuous_pi.comp (continuous_pi fun _ => continuous_id)

/-- Portmanteau for an actual event under a fixed finite independent sample. -/
theorem iidEventProbability_continuousAt (q : ℕ) (μ : ProbabilityMeasure E)
    {A : Set (Fin q → E)}
    (hA : (Measure.pi (fun _ : Fin q => (μ : Measure E))) (frontier A) = 0) :
    ContinuousAt (fun ν : ProbabilityMeasure E =>
      ((Measure.pi (fun _ : Fin q => (ν : Measure E))) A).toReal) μ := by
  have hpi := (iidProbability_continuous (E := E) q).continuousAt (x := μ)
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hpi hA
  exact (ENNReal.tendsto_toReal (measure_ne_top
    (Measure.pi (fun _ : Fin q => (μ : Measure E))) A)).comp hm

/-- A concrete continuity event gives one fixed weak neighborhood. -/
theorem iidEventProbability_weak_neighborhood (q : ℕ) (μ : ProbabilityMeasure E)
    {A : Set (Fin q → E)}
    (hA : (Measure.pi (fun _ : Fin q => (μ : Measure E))) (frontier A) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (ProbabilityMeasure E), U ∈ 𝓝 μ ∧
      ∀ ν ∈ U,
        |((Measure.pi (fun _ : Fin q => (ν : Measure E))) A).toReal -
          ((Measure.pi (fun _ : Fin q => (μ : Measure E))) A).toReal| < ε := by
  refine ⟨{ν | |((Measure.pi (fun _ : Fin q => (ν : Measure E))) A).toReal -
    ((Measure.pi (fun _ : Fin q => (μ : Measure E))) A).toReal| < ε}, ?_, fun _ h => h⟩
  exact (iidEventProbability_continuousAt q μ hA).eventually
    (by simpa only [Metric.mem_ball, Real.dist_eq] using
      Metric.ball_mem_nhds (((Measure.pi (fun _ : Fin q => (μ : Measure E))) A).toReal) hε)

end Antichain
