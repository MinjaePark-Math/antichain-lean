import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The genuine small exponential-tilt estimate for bounded centered tests. -/

namespace Antichain

open MeasureTheory ProbabilityTheory Filter Set Asymptotics
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (mu : Measure X) [IsProbabilityMeasure mu]

theorem boundedTest_exp_integrable (f : X →ᵇ ℝ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * f x)) mu := by
  apply (integrable_const (Real.exp (|t| * ‖f‖))).mono'
    (Real.continuous_exp.comp (continuous_const.mul f.continuous)).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  dsimp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  calc
    t * f x ≤ |t * f x| := le_abs_self _
    _ = |t| * |f x| := abs_mul _ _
    _ ≤ |t| * ‖f‖ := mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm f x)
      (abs_nonneg _)

theorem boundedTest_integrableExpSet (f : X →ᵇ ℝ) :
    integrableExpSet (f : X → ℝ) mu = Set.univ := by
  ext t
  exact iff_true_intro (boundedTest_exp_integrable mu f t)

theorem boundedTest_cgf_quadratic_bigO (f : X →ᵇ ℝ) (hmean : (∫ x, f x ∂mu) = 0) :
    (fun t : ℝ => cgf (f : X → ℝ) mu t) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet (f : X → ℝ) mu) := by
    rw [boundedTest_integrableExpSet, interior_univ]
    trivial
  have han : AnalyticOnNhd ℝ (cgf (f : X → ℝ) mu) univ := by
    simpa only [boundedTest_integrableExpSet, interior_univ] using
      (analyticOnNhd_cgf (X := (f : X → ℝ)) (μ := mu))
  have hcd : ContDiffOn ℝ 2 (cgf (f : X → ℝ) mu) univ :=
    han.contDiffOn_of_completeSpace
  have htaylor := taylor_isLittleO convex_univ (mem_univ (0 : ℝ)) hcd
  have hd : deriv (cgf (f : X → ℝ) mu) 0 = 0 := by
    rw [deriv_cgf_zero hmem, hmean, zero_div]
  have heval (t : ℝ) : taylorWithinEval (cgf (f : X → ℝ) mu) 2 univ 0 t =
      (iteratedDeriv 2 (cgf (f : X → ℝ) mu) 0 / 2) * t ^ 2 := by
    simp only [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_univ, iteratedDeriv_one,
      cgf_zero, hd, sub_zero, zero_add, smul_eq_mul,
      Nat.factorial_one, Nat.cast_one]
    ring
  simp only [nhdsWithin_univ, sub_zero, heval] at htaylor
  have hpoly : (fun t : ℝ =>
      (iteratedDeriv 2 (cgf (f : X → ℝ) mu) 0 / 2) * t ^ 2) =O[𝓝 0]
        (fun t : ℝ => t ^ 2) :=
    (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0)).const_mul_left _
  simpa only [sub_add_cancel] using htaylor.isBigO.add hpoly

theorem boundedTest_cgf_slope_zero (f : X →ᵇ ℝ) (hmean : (∫ x, f x ∂mu) = 0) :
    Tendsto (fun t : ℝ => cgf (f : X → ℝ) mu t / t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (boundedTest_cgf_quadratic_bigO mu f hmean).trans_isLittleO
    (isLittleO_pow_id (𝕜 := ℝ) (show 1 < 2 by norm_num))
  exact h.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds

theorem boundedTest_mgf_quadratic_bigO (f : X →ᵇ ℝ) (hmean : (∫ x, f x ∂mu) = 0) :
    (fun t : ℝ => mgf (f : X → ℝ) mu t - 1) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet (f : X → ℝ) mu) := by
    rw [boundedTest_integrableExpSet, interior_univ]
    trivial
  have han : AnalyticOnNhd ℝ (mgf (f : X → ℝ) mu) univ := by
    simpa only [boundedTest_integrableExpSet, interior_univ] using
      (analyticOnNhd_mgf (X := (f : X → ℝ)) (μ := mu))
  have hcd : ContDiffOn ℝ 2 (mgf (f : X → ℝ) mu) univ :=
    han.contDiffOn_of_completeSpace
  have htaylor := taylor_isLittleO convex_univ (mem_univ (0 : ℝ)) hcd
  have hd : deriv (mgf (f : X → ℝ) mu) 0 = 0 := by
    rw [deriv_mgf_zero hmem, hmean]
  have hd' : iteratedDeriv 1 (mgf (f : X → ℝ) mu) 0 = 0 := by
    rw [iteratedDeriv_one, hd]
  have heval (t : ℝ) : taylorWithinEval (mgf (f : X → ℝ) mu) 2 univ 0 t =
      1 + (iteratedDeriv 2 (mgf (f : X → ℝ) mu) 0 / 2) * t ^ 2 := by
    simp only [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_univ,
      mgf_zero, sub_zero, smul_eq_mul, Nat.factorial_one, Nat.cast_one]
    norm_num only [Nat.factorial_zero, Nat.cast_one]
    rw [hd']
    ring
  simp only [nhdsWithin_univ, sub_zero, heval] at htaylor
  have hpoly : (fun t : ℝ =>
      (iteratedDeriv 2 (mgf (f : X → ℝ) mu) 0 / 2) * t ^ 2) =O[𝓝 0]
        (fun t : ℝ => t ^ 2) :=
    (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0)).const_mul_left _
  convert htaylor.isBigO.add hpoly using 1
  ext t
  ring

/-- A strictly negative Chernoff exponent is obtained from actual boundedness
and centering by the proved quadratic Taylor bound. -/
theorem boundedTest_exists_negative_tilt (f : X →ᵇ ℝ) (hmean : (∫ x, f x ∂mu) = 0)
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) :
    ∃ theta : ℝ, 0 < theta ∧
      -theta * δ + (1 / p) * cgf (f : X → ℝ) mu (p * theta) < -theta * δ / 2 := by
  have hs := (boundedTest_cgf_slope_zero mu f hmean).eventually
    (Iio_mem_nhds (half_pos hδ))
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      0 < t ∧ cgf (f : X → ℝ) mu t / t < δ / 2 := by
    filter_upwards [self_mem_nhdsWithin, hs] with t ht hsmall
    exact ⟨ht, hsmall⟩
  obtain ⟨t, ht, hsmall⟩ := hevent.exists
  refine ⟨t / p, div_pos ht hp, ?_⟩
  rw [mul_div_cancel₀ _ hp.ne']
  have hmul := (div_lt_iff₀ ht).mp hsmall
  have hscaled := div_lt_div_of_pos_right hmul hp
  calc
    _ < -(t / p) * δ + (δ / 2 * t) / p := by
      simpa only [one_div_mul_eq_div] using add_lt_add_left hscaled (-(t / p) * δ)
    _ = _ := by ring

end Antichain
