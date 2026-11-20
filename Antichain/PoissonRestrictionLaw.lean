import Antichain.PoissonRestrictions
import Antichain.PoissonRestrictionSeries

/-! Actual product laws and spatial independence of complementary Poisson
restrictions, derived from the sampled count and independent marks. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

theorem configurationSeriesMeasure_apply_slice (t : ℝ≥0∞) (mu : Measure X)
    {A : Set (FiniteConfiguration X)} (hA : MeasurableSet A) :
    configurationSeriesMeasure t mu A =
      ∑' n : ℕ, t ^ n / (n.factorial : ℝ≥0∞) * configurationSliceMass mu A n := by
  rw [configurationSeriesMeasure, Measure.sum_apply_of_countable]
  apply tsum_congr
  intro n
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_configurationMk n) hA]
  rfl

theorem configurationSeriesMeasure_restriction_rectangle (t : ℝ≥0∞)
    (mu : Measure X) [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U)
    {A B : Set (FiniteConfiguration X)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    configurationSeriesMeasure t mu
      ((configurationRestriction U ⁻¹' A) ∩ (configurationRestriction Uᶜ ⁻¹' B)) =
      configurationSeriesMeasure t (mu.restrict U) A *
        configurationSeriesMeasure t (mu.restrict Uᶜ) B := by
  rw [configurationSeriesMeasure_apply_slice t mu
      (((measurable_configurationRestriction hU) hA).inter
        ((measurable_configurationRestriction hU.compl) hB)),
    configurationSeriesMeasure_apply_slice t (mu.restrict U) hA,
    configurationSeriesMeasure_apply_slice t (mu.restrict Uᶜ) hB]
  simp_rw [pi_configurationRestriction_rectangle mu hU hA hB]
  exact poisson_restriction_series_factorization t _ _

theorem poisson_normalizer_restrict_mul (t : ℝ≥0) (mu : Measure X) [IsFiniteMeasure mu]
    {U : Set X} (hU : MeasurableSet U) :
    ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) =
      ENNReal.ofReal (Real.exp ((t : ℝ) * ((mu.restrict U) Set.univ).toReal)) *
        ENNReal.ofReal (Real.exp ((t : ℝ) * ((mu.restrict Uᶜ) Set.univ).toReal)) := by
  have hm : ((mu.restrict U) Set.univ).toReal +
      ((mu.restrict Uᶜ) Set.univ).toReal = (mu Set.univ).toReal := by
    simp only [Measure.restrict_apply_univ]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hU]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← mul_add, hm]

theorem finiteIntensityPoissonLaw_restriction_rectangle (t : ℝ≥0)
    (mu : Measure X) [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U)
    {A B : Set (FiniteConfiguration X)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    finiteIntensityPoissonLaw t mu
      ((configurationRestriction U ⁻¹' A) ∩ (configurationRestriction Uᶜ ⁻¹' B)) =
      finiteIntensityPoissonLaw t (mu.restrict U) A *
        finiteIntensityPoissonLaw t (mu.restrict Uᶜ) B := by
  have h := configurationSeriesMeasure_restriction_rectangle (t : ℝ≥0∞) mu hU hA hB
  rw [configurationSeriesMeasure_eq_exp_smul_poisson_all,
    configurationSeriesMeasure_eq_exp_smul_poisson_all,
    configurationSeriesMeasure_eq_exp_smul_poisson_all] at h
  simp only [Measure.smul_apply, smul_eq_mul] at h
  have h0 : ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) ≠ 0 := by positivity
  have ht : ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) ≠ ∞ := by simp
  apply (ENNReal.mul_right_inj h0 ht).mp
  calc
    _ = _ := h
    _ = _ := by rw [poisson_normalizer_restrict_mul t mu hU]; ac_rfl

theorem finiteIntensityPoissonLaw_restriction (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U) :
    (finiteIntensityPoissonLaw t mu).map (configurationRestriction U) =
      finiteIntensityPoissonLaw t (mu.restrict U) := by
  letI := finiteIntensityPoissonLaw_probability_all t (mu.restrict Uᶜ)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_configurationRestriction hU) hA]
  have h := finiteIntensityPoissonLaw_restriction_rectangle t mu hU hA MeasurableSet.univ
  simpa only [Set.preimage_univ, Set.inter_univ, measure_univ, mul_one] using h

theorem finiteIntensityPoissonLaw_restriction_joint (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U) :
    (finiteIntensityPoissonLaw t mu).map
      (fun z => (configurationRestriction U z, configurationRestriction Uᶜ z)) =
      (finiteIntensityPoissonLaw t (mu.restrict U)).prod
        (finiteIntensityPoissonLaw t (mu.restrict Uᶜ)) := by
  letI := finiteIntensityPoissonLaw_probability_all t mu
  letI := finiteIntensityPoissonLaw_probability_all t (mu.restrict U)
  letI := finiteIntensityPoissonLaw_probability_all t (mu.restrict Uᶜ)
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply
      ((measurable_configurationRestriction hU).prodMk
        (measurable_configurationRestriction hU.compl)) (hA.prod hB), Measure.prod_prod]
  exact finiteIntensityPoissonLaw_restriction_rectangle t mu hU hA hB

theorem finiteIntensityPoissonLaw_restrictions_independent (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U) :
    IndepFun (configurationRestriction U) (configurationRestriction Uᶜ)
      (finiteIntensityPoissonLaw t mu) := by
  letI := finiteIntensityPoissonLaw_probability_all t mu
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (measurable_configurationRestriction hU).aemeasurable
      (measurable_configurationRestriction hU.compl).aemeasurable,
    finiteIntensityPoissonLaw_restriction t mu hU,
    finiteIntensityPoissonLaw_restriction t mu hU.compl]
  exact finiteIntensityPoissonLaw_restriction_joint t mu hU

end Antichain
