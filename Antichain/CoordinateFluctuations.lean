import Antichain.RankCDF
import Antichain.CubeProbabilitySpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The actual empirical coordinate average keeps its iid uniform law after
conditioning on the antichain event, because it depends only on sorted values. -/

noncomputable section
namespace Antichain
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction

def scalarCoordinateFluctuation (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * ((∑ j, x j) / (n : ℝ) - 1 / 2)

theorem scalarCoordinateFluctuation_continuous (n : ℕ) :
    Continuous (scalarCoordinateFluctuation n) := by
  unfold scalarCoordinateFluctuation
  fun_prop

theorem scalarCoordinateFluctuation_sort (n : ℕ) (x : Fin n → ℝ) :
    scalarCoordinateFluctuation n (sampleSortedValues x) = scalarCoordinateFluctuation n x := by
  unfold scalarCoordinateFluctuation sampleSortedValues
  rw [(sampleSortPermutation x).sum_comp]
  simp

def coordinateFluctuationLaw (n d : ℕ) (hd : 2 ≤ d) (i : Fin d) : ProbabilityMeasure ℝ :=
  letI : IsProbabilityMeasure (cubeAntichainLaw n d) := cubeAntichainLaw_isProbabilityMeasure n d hd
  ⟨(cubeAntichainLaw n d).map (fun x => scalarCoordinateFluctuation n (fun j => x j i)),
    Measure.isProbabilityMeasure_map ((scalarCoordinateFluctuation_continuous n).measurable.comp
      (measurable_pi_iff.mpr fun j => (measurable_pi_apply i).comp (measurable_pi_apply j))).aemeasurable⟩

def iidUniformFluctuationLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(Measure.pi (fun _ : Fin n => cubeCoordinateLaw)).map (scalarCoordinateFluctuation n),
    Measure.isProbabilityMeasure_map (scalarCoordinateFluctuation_continuous n).measurable.aemeasurable⟩

/-- Exact law equality for every sample size, including before taking a limit. -/
theorem coordinateFluctuationLaw_eq_iidUniform (n d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    coordinateFluctuationLaw n d hd i = iidUniformFluctuationLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  let f := scalarCoordinateFluctuation n
  have hf := (scalarCoordinateFluctuation_continuous n).measurable
  have hs : Measurable (fun x : CubeSample n d => coordinateSortedValues n d x i) :=
    (measurable_pi_apply i).comp (coordinateSortedValues_measurable n d)
  change (cubeAntichainLaw n d).map (fun x => f (fun j => x j i)) =
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)).map f
  calc
    _ = (cubeAntichainLaw n d).map (f ∘ fun x => coordinateSortedValues n d x i) := by
      congr 1
      funext x
      exact (scalarCoordinateFluctuation_sort n (fun j => x j i)).symm
    _ = (scalarSortedLaw n).map f := by
      rw [← Measure.map_map hf hs, cubeAntichain_sortedCoordinate_law n d hd i]
    _ = _ := by
      rw [scalarSortedLaw, Measure.map_map hf (sampleSortedValues_measurable n)]
      congr 1
      funext x
      exact scalarCoordinateFluctuation_sort n x

/-- The named Gaussian law in the manuscript has mean zero and variance 1/12. -/
def centeredGaussianProbability (v : NNReal) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 v, inferInstance⟩

def coordinateFluctuationGaussian : ProbabilityMeasure ℝ := centeredGaussianProbability (1 / 12)

/-- Mean and variance of the actual restricted Lebesgue coordinate law. -/
theorem cubeCoordinateLaw_mean : (∫ x, x ∂cubeCoordinateLaw) = 1 / 2 := by
  rw [cubeCoordinateLaw, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
  norm_num

theorem cubeCoordinateLaw_centered_square : (∫ x, (x - 1 / 2)^2 ∂cubeCoordinateLaw) = 1 / 12 := by
  rw [cubeCoordinateLaw, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp_rw [show ∀ x : ℝ, (x - 1 / 2)^2 = x ^ 2 - x + 1 / 4 by intro x; ring]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_pow,
    integral_id, intervalIntegral.integral_const]
  norm_num

/-- Finite-product law of the centered and rescaled average. -/
def iidCenteredAverageLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) (n : ℕ) :
    ProbabilityMeasure ℝ := by
  let f : (Fin n → ℝ) → ℝ := fun x => Real.sqrt (n : ℝ) * ((∑ j, x j) / (n : ℝ) - m)
  have hf : Measurable f := by dsimp [f]; fun_prop
  exact ⟨(Measure.pi (fun _ : Fin n => μ)).map f,
    Measure.isProbabilityMeasure_map hf.aemeasurable⟩

/-- The usual real iid central limit theorem for finite second moment laws. -/
def IIDFiniteVarianceCLT : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) (v : NNReal),
    Integrable (fun x => (x - m)^2) μ → (∫ x, x ∂μ) = m →
      (∫ x, (x - m)^2 ∂μ) = (v : ℝ) →
      Tendsto (iidCenteredAverageLaw μ m) atTop (𝓝 (centeredGaussianProbability v))

/-- The manuscript's CLT, with only the general iid CLT as an external result. -/
theorem coordinateFluctuation_clt_of_iid (h : IIDFiniteVarianceCLT)
    (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Tendsto (fun n => coordinateFluctuationLaw n d hd i) atTop
      (𝓝 coordinateFluctuationGaussian) := by
  simp_rw [coordinateFluctuationLaw_eq_iidUniform]
  refine @h cubeCoordinateLaw inferInstance (1 / 2) (1 / 12) ?_ cubeCoordinateLaw_mean ?_
  · exact Continuous.integrableOn_Icc (by fun_prop)
  · simpa using cubeCoordinateLaw_centered_square

/-- The statistic under the finite law is precisely the manuscript's empirical integral. -/
theorem scalarCoordinateFluctuation_eq_empiricalIntegral (n d : ℕ) (hn : 0 < n)
    (x : ClosedCubeSample n d) (i : Fin d) :
    scalarCoordinateFluctuation n (fun j => (x j).val i) = Real.sqrt (n : ℝ) *
      ((∫ u, u.val i ∂(empiricalClosedCubeProbability n d x : Measure (ClosedCubePoint d))) - 1 / 2) := by
  let g : ClosedCubePoint d →ᵇ ℝ :=
    ⟨⟨fun u => u.val i, (continuous_apply i).comp continuous_subtype_val⟩, 1, fun u v => by
      have hu := u.property i (Set.mem_univ i)
      have hv := v.property i (Set.mem_univ i)
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩⟩
  change _ = Real.sqrt (n : ℝ) *
    ((∫ u, g u ∂(empiricalClosedCubeProbability n d x : Measure (ClosedCubePoint d))) - 1 / 2)
  rw [empiricalClosedCubeProbability_integral n d hn]
  rfl

/-- The measure in the convergence assertion is the actual pushforward of the
conditional closed-cube law by the rescaled empirical coordinate integral. -/
theorem coordinateFluctuationLaw_eq_closed_empirical (n d : ℕ) (hn : 0 < n)
    (hd : 2 ≤ d) (i : Fin d) :
    (coordinateFluctuationLaw n d hd i : Measure ℝ) =
      (closedCubeAntichainLaw n d).map (fun x => Real.sqrt (n : ℝ) *
        ((∫ u, u.val i ∂(empiricalClosedCubeProbability n d x : Measure (ClosedCubePoint d))) - 1 / 2)) := by
  let f : CubeSample n d → ℝ := fun x => scalarCoordinateFluctuation n (fun j => x j i)
  have hf : Measurable f := (scalarCoordinateFluctuation_continuous n).measurable.comp
    (measurable_pi_iff.mpr fun j => (measurable_pi_apply i).comp (measurable_pi_apply j))
  change (cubeAntichainLaw n d).map f = _
  rw [← closedCubeAntichainLaw_include_map_eq n d, Measure.map_map hf
    (includeClosedCubeSample_continuous n d).measurable]
  congr 1
  funext x
  exact scalarCoordinateFluctuation_eq_empiricalIntegral n d hn x i

end Antichain
