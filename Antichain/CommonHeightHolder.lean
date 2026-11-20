import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! The common-height estimate by the multiple-function Hölder argument
written in Lemma 4.1. -/
noncomputable section
namespace Antichain
open MeasureTheory Finset
open scoped ENNReal
variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- Equal-exponent Hölder followed by translation invariance. -/
theorem lintegral_translated_product_holder (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (h : κ → ℝ) :
    (∫⁻ s : ℝ, ∏ j, g (s + h j)) ≤ ∫⁻ s : ℝ, g s ^ Fintype.card κ := by
  classical
  have hn : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  have hnR : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast hn
  have H := ENNReal.lintegral_prod_norm_pow_le (μ := volume)
    (Finset.univ : Finset κ)
    (f := fun j s => g (s + h j) ^ Fintype.card κ)
    (p := fun _ => (Fintype.card κ : ℝ)⁻¹)
    (fun j _ => ((hg.comp (measurable_id.add_const (h j))).pow_const _).aemeasurable)
    (by simp [hnR] : ∑ j ∈ (Finset.univ : Finset κ), (Fintype.card κ : ℝ)⁻¹ = 1)
    (fun _ _ => by positivity)
  simp only [ENNReal.pow_rpow_inv_natCast hn] at H
  have hshift (j : κ) :
      (∫⁻ s : ℝ, g (s + h j) ^ Fintype.card κ) = ∫⁻ s : ℝ, g s ^ Fintype.card κ :=
    (measurePreserving_add_right volume (h j)).lintegral_comp (hg.pow_const _)
  simp_rw [hshift] at H
  simpa only [Finset.prod_const, Finset.card_univ, ENNReal.rpow_inv_natCast_pow hn] using H

/-- Gaussian specialization of precisely the written Hölder argument. -/
theorem lintegral_translated_gaussian_holder (h : κ → ℝ) (a : ℝ) (ha : 0 < a) :
    (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-a * ∑ j, (s + h j) ^ 2))) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (a * (Fintype.card κ : ℝ)))) := by
  have hg : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-a * s ^ 2))) := by
    fun_prop
  have H := lintegral_translated_product_holder _ hg h
  have hprod (s : ℝ) :
      (∏ j, ENNReal.ofReal (Real.exp (-a * (s + h j) ^ 2))) =
        ENNReal.ofReal (Real.exp (-a * ∑ j, (s + h j) ^ 2)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    exact (Finset.mul_sum Finset.univ (fun j => (s + h j) ^ 2) (-a)).symm
  have hpow (s : ℝ) :
      ENNReal.ofReal (Real.exp (-a * s ^ 2)) ^ Fintype.card κ =
        ENNReal.ofReal (Real.exp (-(a * (Fintype.card κ : ℝ)) * s ^ 2)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    ring
  simp_rw [hprod, hpow] at H
  have hn : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos (α := κ)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq (mul_pos ha hn))
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)), integral_gaussian] at H
  exact H

/-- Integrability is itself obtained from the finite Hölder bound. -/
theorem translated_gaussian_integrable_holder (h : κ → ℝ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun s : ℝ => Real.exp (-a * ∑ j, (s + h j) ^ 2)) := by
  refine ⟨(by fun_prop : Continuous (fun s : ℝ =>
    Real.exp (-a * ∑ j, (s + h j) ^ 2))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact (lintegral_translated_gaussian_holder h a ha).trans_lt ENNReal.ofReal_lt_top

theorem integral_translated_gaussian_holder (h : κ → ℝ) (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ, Real.exp (-a * ∑ j, (s + h j) ^ 2)) ≤
      Real.sqrt (Real.pi / (a * (Fintype.card κ : ℝ))) := by
  have H := lintegral_translated_gaussian_holder h a ha
  rw [← ofReal_integral_eq_lintegral_ofReal (translated_gaussian_integrable_holder h a ha)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))] at H
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp H

end Antichain
