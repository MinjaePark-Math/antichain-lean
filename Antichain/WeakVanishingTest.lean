import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Weak-neighborhood control of bounded tests continuous off a closed null set. -/

noncomputable section

namespace Antichain

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

def closedBoundaryApprox (F : Set X) (n : ℕ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x : ℝ),
      NNReal.continuous_coe.comp (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F).continuous⟩
    1 (by
      intro x y
      have hx := thickenedIndicator_le_one (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x
      have hy := thickenedIndicator_le_one (by positivity : 0 < 1 / ((n : ℝ) + 1)) F y
      have hx' : (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x : ℝ) ≤ 1 := by exact_mod_cast hx
      have hy' : (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F y : ℝ) ≤ 1 := by exact_mod_cast hy
      have hx0 : (0 : ℝ) ≤ (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x : ℝ) := NNReal.coe_nonneg _
      have hy0 : (0 : ℝ) ≤ (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F y : ℝ) := NNReal.coe_nonneg _
      rw [Real.dist_eq]
      dsimp only [ContinuousMap.coe_mk]
      exact abs_le.mpr ⟨by linarith, by linarith⟩)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem closedBoundaryApprox_bounds (F : Set X) (n : ℕ) (x : X) :
    0 ≤ closedBoundaryApprox F n x ∧ closedBoundaryApprox F n x ≤ 1 := by
  change (0 : ℝ) ≤ (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x : ℝ) ∧
    (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x : ℝ) ≤ 1
  constructor
  · exact NNReal.coe_nonneg _
  · exact_mod_cast thickenedIndicator_le_one (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem closedBoundaryApprox_eq_one (F : Set X) (n : ℕ) {x : X} (hx : x ∈ F) :
    closedBoundaryApprox F n x = 1 := by
  change (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) F x : ℝ) = 1
  rw [thickenedIndicator_one _ _ hx]
  rfl

theorem closedBoundaryApprox_integral_tendsto (mu : ProbabilityMeasure X)
    {F : Set X} (hF : IsClosed F) (hnull : (mu : Measure X) F = 0) :
    Tendsto (fun n => ∫ x, closedBoundaryApprox F n x ∂(mu : Measure X)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have h := (ENNReal.tendsto_toReal (measure_ne_top (mu : Measure X) F)).comp
    (tendsto_lintegral_thickenedIndicator_of_isClosed (mu : Measure X) hF
      (fun n => by positivity : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1)) hr)
  rw [hnull, ENNReal.toReal_zero] at h
  apply h.congr
  intro n
  symm
  simpa only [closedBoundaryApprox, BoundedContinuousFunction.mkOfBound_coe,
    ContinuousMap.coe_mk, ENNReal.ofReal_coe_nnreal] using
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => (closedBoundaryApprox_bounds F n x).1))
      (closedBoundaryApprox F n).continuous.aestronglyMeasurable

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem continuous_boundary_damped_test {F : Set X} (hF : IsClosed F)
    (b : X → ℝ) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, b x ≤ 1)
    (hcont : ContinuousOn b Fᶜ) (n : ℕ) :
    Continuous (fun x => (1 - closedBoundaryApprox F n x) * b x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ F
  · have hrx : closedBoundaryApprox F n x = 1 := closedBoundaryApprox_eq_one F n hx
    have hcut : Tendsto (fun y => 1 - closedBoundaryApprox F n y) (𝓝 x) (𝓝 0) := by
      have hrAt : Tendsto (fun y => closedBoundaryApprox F n y) (𝓝 x)
          (𝓝 (closedBoundaryApprox F n x)) := (closedBoundaryApprox F n).continuous.continuousAt
      simpa only [hrx, sub_self] using hrAt.const_sub 1
    change Tendsto (fun y => (1 - closedBoundaryApprox F n y) * b y) (𝓝 x)
      (𝓝 ((1 - closedBoundaryApprox F n x) * b x))
    rw [hrx, sub_self, zero_mul]
    exact squeeze_zero
      (fun y => mul_nonneg (sub_nonneg.mpr (closedBoundaryApprox_bounds F n y).2) (hb0 y))
      (fun y => mul_le_of_le_one_right
        (sub_nonneg.mpr (closedBoundaryApprox_bounds F n y).2) (hb1 y)) hcut
  · exact (continuous_const.sub (closedBoundaryApprox F n).continuous).continuousAt.mul
      (hcont.continuousAt (hF.isOpen_compl.mem_nhds hx))

/-- A bounded measurable test vanishing almost surely, continuous away from a
closed null set, is small throughout a genuine weak neighborhood. The proof
constructs continuous damping near the exceptional set; no unverified
portmanteau theorem for discontinuous tests is assumed. -/
theorem weak_neighborhood_for_vanishing_test (mu : ProbabilityMeasure X)
    {F : Set X} (hF : IsClosed F) (hnull : (mu : Measure X) F = 0)
    (b : X → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, b x ≤ 1)
    (hcont : ContinuousOn b Fᶜ) (hzero : ∀ᵐ x ∂(mu : Measure X), b x = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ U : Set (ProbabilityMeasure X), U ∈ 𝓝 mu ∧
      ∀ nu ∈ U, (∫ x, b x ∂(nu : Measure X)) < epsilon := by
  obtain ⟨n, hn⟩ := ((closedBoundaryApprox_integral_tendsto mu hF hnull).eventually
    (Iio_mem_nhds (show 0 < epsilon / 4 by positivity))).exists
  let r := closedBoundaryApprox F n
  let f : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => (1 - r x) * b x, continuous_boundary_damped_test hF b hb0 hb1 hcont n⟩ 1 (by
      intro x y
      have hx0 : 0 ≤ (1 - r x) * b x :=
        mul_nonneg (sub_nonneg.mpr (closedBoundaryApprox_bounds F n x).2) (hb0 x)
      have hy0 : 0 ≤ (1 - r y) * b y :=
        mul_nonneg (sub_nonneg.mpr (closedBoundaryApprox_bounds F n y).2) (hb0 y)
      have hx1 : (1 - r x) * b x ≤ 1 :=
        (mul_le_of_le_one_right (sub_nonneg.mpr (closedBoundaryApprox_bounds F n x).2)
          (hb1 x)).trans (by linarith [(closedBoundaryApprox_bounds F n x).1])
      have hy1 : (1 - r y) * b y ≤ 1 :=
        (mul_le_of_le_one_right (sub_nonneg.mpr (closedBoundaryApprox_bounds F n y).2)
          (hb1 y)).trans (by linarith [(closedBoundaryApprox_bounds F n y).1])
      rw [Real.dist_eq]
      dsimp only [ContinuousMap.coe_mk]
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have hfzero : (∫ x, f x ∂(mu : Measure X)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with x hx
    change (1 - r x) * b x = 0
    rw [hx, mul_zero]
  have hcf := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have hcr := ProbabilityMeasure.continuous_integral_boundedContinuousFunction r
  have hef : ∀ᶠ nu : ProbabilityMeasure X in 𝓝 mu,
      (∫ x, f x ∂(nu : Measure X)) < epsilon / 2 :=
    hcf.continuousAt.tendsto.eventually (Iio_mem_nhds (by rw [hfzero]; positivity))
  have her : ∀ᶠ nu : ProbabilityMeasure X in 𝓝 mu,
      (∫ x, r x ∂(nu : Measure X)) < epsilon / 2 :=
    hcr.continuousAt.tendsto.eventually (Iio_mem_nhds (by change (∫ x, closedBoundaryApprox F n x ∂(mu : Measure X)) < _; linarith))
  refine ⟨{nu | (∫ x, f x ∂(nu : Measure X)) < epsilon / 2 ∧
    (∫ x, r x ∂(nu : Measure X)) < epsilon / 2}, hef.and her, ?_⟩
  intro nu hnu
  have hIb : Integrable b (nu : Measure X) := by
    apply (integrable_const (1 : ℝ)).mono' hb.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hb0 x)]; exact hb1 x)
  have hp (x : X) : b x ≤ f x + r x := by
    change b x ≤ (1 - r x) * b x + r x
    nlinarith [mul_nonneg (sub_nonneg.mpr (hb1 x)) (closedBoundaryApprox_bounds F n x).1]
  have hi := integral_mono hIb ((f.integrable (μ := (nu : Measure X))).add
    (r.integrable (μ := (nu : Measure X)))) hp
  change (∫ x, b x ∂(nu : Measure X)) ≤ ∫ x, f x + r x ∂(nu : Measure X) at hi
  rw [integral_add (f.integrable (μ := (nu : Measure X))) (r.integrable (μ := (nu : Measure X)))] at hi
  linarith [hnu.1, hnu.2]

end Antichain
