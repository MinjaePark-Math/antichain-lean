import Antichain.Basic
import Antichain.CommonHeightHolder
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! Exact common-height Gaussian integration used in Lemma 4.1.
The common-height integral follows the manuscript’s multiple-function Hölder
argument and translation invariance. Square-completion identities below are
retained as supplementary pointwise estimates. -/

noncomputable section

namespace Antichain

open MeasureTheory Finset

variable {κ : Type*} [Fintype κ] [Nonempty κ]

theorem translated_sum_sq_identity (h : κ → ℝ) (s : ℝ) :
    (∑ j, (s + h j) ^ 2) =
      (Fintype.card κ : ℝ) * (s + (∑ j, h j) / (Fintype.card κ : ℝ)) ^ 2 +
        ∑ j, (h j - (∑ k, h k) / (Fintype.card κ : ℝ)) ^ 2 := by
  have hz := sum_sub_mean_eq_zero h
  have hi := sum_sq_add_of_sum_zero
    (fun j => h j - (∑ k, h k) / (Fintype.card κ : ℝ))
    (s + (∑ k, h k) / (Fintype.card κ : ℝ)) hz
  have heq (j : κ) : s + (∑ k, h k) / (Fintype.card κ : ℝ) +
      (h j - (∑ k, h k) / (Fintype.card κ : ℝ)) = s + h j := by ring
  simp_rw [heq] at hi
  exact hi

theorem translated_sum_sq_lower_bound (h : κ → ℝ) (s : ℝ) :
    (Fintype.card κ : ℝ) * (s + (∑ j, h j) / (Fintype.card κ : ℝ)) ^ 2 ≤
      ∑ j, (s + h j) ^ 2 := by
  rw [translated_sum_sq_identity]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem shifted_gaussian_integrable (b : ℝ) (hb : 0 < b) (a : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-b * (s + a) ^ 2)) :=
  (measurePreserving_add_right volume a).integrable_comp_of_integrable
    (integrable_exp_neg_mul_sq hb)

theorem integral_shifted_gaussian (b a : ℝ) :
    (∫ s : ℝ, Real.exp (-b * (s + a) ^ 2)) = Real.sqrt (Real.pi / b) := by
  rw [integral_add_right_eq_self (fun s : ℝ => Real.exp (-b * s ^ 2)) a]
  exact integral_gaussian b

theorem translated_gaussian_product_le (h : κ → ℝ) (a : ℝ) (ha : 0 ≤ a) (s : ℝ) :
    Real.exp (-a * ∑ j, (s + h j) ^ 2) ≤
      Real.exp (-(a * (Fintype.card κ : ℝ)) *
        (s + (∑ j, h j) / (Fintype.card κ : ℝ)) ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hi := mul_le_mul_of_nonneg_left (translated_sum_sq_lower_bound h s) ha
  nlinarith

theorem translated_gaussian_product_integrable (h : κ → ℝ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun s : ℝ => Real.exp (-a * ∑ j, (s + h j) ^ 2)) :=
  translated_gaussian_integrable_holder h a ha

/-- The actual integrated common-height penalty, by equal-exponent Hölder
and translation invariance exactly as in Lemma 4.1. -/
theorem integral_translated_gaussian_product_le (h : κ → ℝ) (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ, Real.exp (-a * ∑ j, (s + h j) ^ 2)) ≤
      Real.sqrt (Real.pi / (a * (Fintype.card κ : ℝ))) :=
  integral_translated_gaussian_holder h a ha

/-- The exact coefficient in equation (4.4), including its Gaussian normalization. -/
def commonHeightGaussianCoefficient (n : ℕ) (c : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-((n : ℝ) - 1) / 2) / Real.sqrt ((n : ℝ) * (1 - 2 * c))

theorem gaussian_coefficient_identity (n : ℕ) (hn : 0 < n) (c : ℝ) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) *
      Real.sqrt (Real.pi / (((1 / 2 : ℝ) - c) * n)) =
      commonHeightGaussianCoefficient n c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : 0 < 2 * Real.pi := by positivity
  have hratio : Real.pi / (((1 / 2 : ℝ) - c) * n) =
      (2 * Real.pi) / ((n : ℝ) * (1 - 2 * c)) := by
    field_simp
  rw [hratio, Real.sqrt_div (le_of_lt hbase)]
  unfold commonHeightGaussianCoefficient
  rw [← mul_div_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add hbase]
  congr 2
  ring

/-- The normalized translated Gaussian height integral is bounded by exactly
the paper's coefficient, for every relative height configuration. -/
theorem normalized_common_height_integral_le (h : κ → ℝ) (c : ℝ) (hc : c < 1 / 2) :
    (∫ s : ℝ, (2 * Real.pi) ^ (-(Fintype.card κ : ℝ) / 2) *
      Real.exp (-((1 / 2 : ℝ) - c) * ∑ j, (s + h j) ^ 2)) ≤
        commonHeightGaussianCoefficient (Fintype.card κ) c := by
  rw [integral_const_mul]
  have hb : (0 : ℝ) ≤ (2 * Real.pi) ^ (-(Fintype.card κ : ℝ) / 2) := by positivity
  exact (mul_le_mul_of_nonneg_left
    (integral_translated_gaussian_product_le h ((1 / 2 : ℝ) - c) (by linarith)) hb).trans_eq
      (gaussian_coefficient_identity _ Fintype.card_pos c)

theorem normalized_common_height_lintegral_le (h : κ → ℝ) (c : ℝ) (hc : c < 1 / 2) :
    (∫⁻ s : ℝ, ENNReal.ofReal ((2 * Real.pi) ^ (-(Fintype.card κ : ℝ) / 2) *
      Real.exp (-((1 / 2 : ℝ) - c) * ∑ j, (s + h j) ^ 2))) ≤
        ENNReal.ofReal (commonHeightGaussianCoefficient (Fintype.card κ) c) := by
  have hi := (translated_gaussian_product_integrable h ((1 / 2 : ℝ) - c)
    (by linarith)).const_mul ((2 * Real.pi) ^ (-(Fintype.card κ : ℝ) / 2))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun s => by positivity))]
  exact ENNReal.ofReal_le_ofReal (normalized_common_height_integral_le h c hc)

end Antichain
