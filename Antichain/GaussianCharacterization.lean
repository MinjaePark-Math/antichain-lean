import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! The converse location/arrangement separation stated in the introduction.
Two-point centered configurations already force the potential to be quadratic. -/

noncomputable section

namespace Antichain

open Set MeasureTheory

/-- Separation for all two-point centered configurations. It is implied by the
paper's separation for every centered finite configuration. -/
def LocationArrangementSeparation (V : ℝ → ℝ) : Prop :=
  ∃ A B : ℝ → ℝ, ∀ m u : ℝ, V (m + u) + V (m - u) = A m + B u

theorem locationArrangementSeparation_centered_identity {V : ℝ → ℝ}
    (hsep : LocationArrangementSeparation V) (m u : ℝ) :
    V (m + u) + V (m - u) = 2 * V m + V u + V (-u) - 2 * V 0 := by
  obtain ⟨A, B, h⟩ := hsep
  have hmu := h m u
  have hm0 := h m 0
  have h0u := h 0 u
  have h00 := h 0 0
  simp only [add_zero, sub_zero, zero_add, zero_sub] at hm0 h0u h00
  linarith

/-- A smooth separated potential is literally quadratic, including its affine
part; this conclusion is proved rather than supplied as a model premise. -/
theorem separated_potential_quadratic {V : ℝ → ℝ}
    (hV : ContDiff ℝ 2 V) (hsep : LocationArrangementSeparation V) :
    ∀ x : ℝ, V x = deriv (deriv V) 0 / 2 * x ^ 2 + deriv V 0 * x + V 0 := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hDd : Differentiable ℝ (deriv V) := hV.differentiable_deriv_two
  have hfirst (m u : ℝ) : deriv V (m + u) - deriv V (m - u) =
      deriv V u - deriv V (-u) := by
    have hl := ((hVd (m + u)).hasDerivAt.comp u ((hasDerivAt_id u).const_add m)).add
      ((hVd (m - u)).hasDerivAt.comp u ((hasDerivAt_id u).const_sub m))
    have hr := (((hasDerivAt_const u (2 * V m)).add (hVd u).hasDerivAt).add
      ((hVd (-u)).hasDerivAt.comp u (hasDerivAt_neg u))).sub_const (2 * V 0)
    have heq : (fun t => V (m + t) + V (m - t)) =
        (fun t => 2 * V m + V t + V (-t) - 2 * V 0) :=
      funext (locationArrangementSeparation_centered_identity hsep m)
    change HasDerivAt (fun t => 2 * V m + V t + V (-t) - 2 * V 0) _ _ at hr
    rw [← heq] at hr
    have hu := hl.unique hr
    linarith
  have hsecond (m : ℝ) : deriv (deriv V) m = deriv (deriv V) 0 := by
    have hl := ((hDd (m + 0)).hasDerivAt.comp 0 ((hasDerivAt_id 0).const_add m)).sub
      ((hDd (m - 0)).hasDerivAt.comp 0 ((hasDerivAt_id 0).const_sub m))
    have hr := (hDd 0).hasDerivAt.sub
      ((hDd (-0)).hasDerivAt.comp 0 (hasDerivAt_neg 0))
    have heq : (fun t => deriv V (m + t) - deriv V (m - t)) =
        (fun t => deriv V t - deriv V (-t)) := funext (hfirst m)
    change HasDerivAt (fun t => deriv V t - deriv V (-t)) _ _ at hr
    rw [← heq] at hr
    have hu := hl.unique hr
    simp only [add_zero, sub_zero, neg_zero] at hu
    linarith
  have hlinear (x : ℝ) : deriv V x = deriv (deriv V) 0 * x + deriv V 0 := by
    have hdiff : Differentiable ℝ (fun t => deriv V t - deriv (deriv V) 0 * t) :=
      hDd.sub (differentiable_id.const_mul _)
    have hzero (t : ℝ) : deriv (fun s => deriv V s - deriv (deriv V) 0 * s) t = 0 := by
      have hh := ((hDd t).hasDerivAt.sub
        ((hasDerivAt_id t).const_mul (deriv (deriv V) 0))).deriv
      change deriv (fun s => deriv V s - deriv (deriv V) 0 * s) t = _ at hh
      rw [hh]
      simp only [mul_one, hsecond, sub_self]
    have hc := is_const_of_deriv_eq_zero hdiff hzero x 0
    simp only [mul_zero, sub_zero] at hc
    linarith
  have hdiff : Differentiable ℝ (fun t =>
      V t - (deriv (deriv V) 0 / 2 * t ^ 2 + deriv V 0 * t)) := by fun_prop
  have hzero (t : ℝ) : deriv (fun s =>
      V s - (deriv (deriv V) 0 / 2 * s ^ 2 + deriv V 0 * s)) t = 0 := by
    have hp := (((hasDerivAt_id t).pow 2).const_mul (deriv (deriv V) 0 / 2)).add
      ((hasDerivAt_id t).const_mul (deriv V 0))
    have hh := ((hVd t).hasDerivAt.sub hp).deriv
    change deriv (fun s => V s - (deriv (deriv V) 0 / 2 * s ^ 2 + deriv V 0 * s)) t = _ at hh
    rw [hh, hlinear]
    norm_num
    ring
  have hc := is_const_of_deriv_eq_zero hdiff hzero
  intro x
  have hx := hc x 0
  simp only [sq, mul_zero, add_zero, sub_zero] at hx
  linarith

theorem integrable_exp_neg_quadratic_coefficient_pos (a b c : ℝ)
    (hf : Integrable (fun x : ℝ => Real.exp (-(a * x ^ 2 + b * x + c)))) :
    0 < a := by
  let f : ℝ → ℝ := fun x => Real.exp (-(a * x ^ 2 + b * x + c))
  have hneg : Integrable (fun x => f (-x)) := hf.comp_neg
  have hbound : Integrable (fun x => Real.exp c / 2 * (f x + f (-x))) :=
    (hf.add hneg).const_mul _
  have hg : Integrable (fun x : ℝ => Real.exp (-a * x ^ 2)) := by
    apply hbound.mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp : 2 ≤ Real.exp (b * x) + Real.exp (-b * x) := by
      linarith [Real.add_one_le_exp (b * x), Real.add_one_le_exp (-b * x)]
    have hfactor : f x + f (-x) = Real.exp (-a * x ^ 2 - c) *
        (Real.exp (-b * x) + Real.exp (b * x)) := by
      dsimp [f]
      rw [show -(a * x ^ 2 + b * x + c) = (-a * x ^ 2 - c) + (-b * x) by ring,
        show -(a * (-x) ^ 2 + b * (-x) + c) = (-a * x ^ 2 - c) + b * x by ring,
        Real.exp_add, Real.exp_add, mul_add]
    have hcancel : Real.exp c * Real.exp (-a * x ^ 2 - c) = Real.exp (-a * x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    have ht := mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg (-a * x ^ 2 - c))
    have hu := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg c)
    nlinarith [hcancel, Real.exp_pos (-a * x ^ 2)]
  exact integrable_exp_neg_mul_sq_iff.mp hg

/-- A positive smooth probability density with the claimed separation is an
actual normalized Gaussian density up to its location and positive scale. -/
theorem separated_probability_density_gaussian (q : ℝ → ℝ)
    (hq : ∀ x, 0 < q x) (hint : Integrable q) (hmass : ∫ x, q x = 1)
    (hsmooth : ContDiff ℝ 2 (fun x => -Real.log (q x)))
    (hsep : LocationArrangementSeparation (fun x => -Real.log (q x))) :
    ∃ a : ℝ, 0 < a ∧ ∃ m : ℝ, ∀ x : ℝ,
      q x = (Real.sqrt (Real.pi / a))⁻¹ * Real.exp (-a * (x - m) ^ 2) := by
  let V : ℝ → ℝ := fun x => -Real.log (q x)
  let a := deriv (deriv V) 0 / 2
  let b := deriv V 0
  let c := V 0
  have hquad (x : ℝ) : V x = a * x ^ 2 + b * x + c :=
    separated_potential_quadratic hsmooth hsep x
  have hqform (x : ℝ) : q x = Real.exp (-(a * x ^ 2 + b * x + c)) := by
    rw [← hquad]
    simp only [V, neg_neg, Real.exp_log (hq x)]
  have ha : 0 < a := integrable_exp_neg_quadratic_coefficient_pos a b c (by
    simpa only [← hqform] using hint)
  let m := -b / (2 * a)
  let C := Real.exp (-c + b ^ 2 / (4 * a))
  have hform (x : ℝ) : q x = C * Real.exp (-a * (x - m) ^ 2) := by
    rw [hqform]
    dsimp [C]
    rw [← Real.exp_add]
    congr 1
    dsimp [m]
    field_simp
    ring
  have hnorm : C * Real.sqrt (Real.pi / a) = 1 := by
    calc
      _ = C * ∫ x : ℝ, Real.exp (-a * (x - m) ^ 2) := by
        rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-a * x ^ 2)), integral_gaussian]
      _ = ∫ x : ℝ, C * Real.exp (-a * (x - m) ^ 2) := (integral_const_mul _ _).symm
      _ = 1 := by simpa only [← hform] using hmass
  have hs : Real.sqrt (Real.pi / a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (div_pos Real.pi_pos ha))
  have hC : C = (Real.sqrt (Real.pi / a))⁻¹ := by
    apply (mul_right_cancel₀ hs)
    rw [hnorm, inv_mul_cancel₀ hs]
  exact ⟨a, ha, m, fun x => by rw [hform, hC]⟩

/-- Source form: smoothness is imposed on the positive density itself. -/
theorem gaussian_location_arrangement_characterization_source (q : ℝ → ℝ)
    (hq : ∀ x, 0 < q x) (hsmooth : ContDiff ℝ 2 q)
    (hint : Integrable q) (hmass : ∫ x, q x = 1)
    (hsep : LocationArrangementSeparation (fun x => -Real.log (q x))) :
    ∃ a : ℝ, 0 < a ∧ ∃ m : ℝ, ∀ x : ℝ,
      q x = (Real.sqrt (Real.pi / a))⁻¹ * Real.exp (-a * (x - m) ^ 2) := by
  apply separated_probability_density_gaussian q hq hint hmass
  · exact (hsmooth.log (fun x => (hq x).ne')).neg
  · exact hsep

end Antichain
