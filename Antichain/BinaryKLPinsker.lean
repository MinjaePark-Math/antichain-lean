import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Binary relative entropy and its sharp quadratic lower bound.

The definition uses the continuous x log x expression, including both
endpoint conventions. The ratio formula and Pinsker bound are proved.
This module has no empirical-process or DKW hypothesis.
-/

noncomputable section

namespace Antichain

open Set

def binaryKL (r p : ℝ) : ℝ :=
  r * Real.log r + (1 - r) * Real.log (1 - r) -
    r * Real.log p - (1 - r) * Real.log (1 - p)

theorem binaryKL_self (p : ℝ) : binaryKL p p = 0 := by
  unfold binaryKL
  ring

theorem binaryKL_continuous_left (p : ℝ) : Continuous (fun r => binaryKL r p) := by
  unfold binaryKL
  exact ((Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
      (continuous_id.mul continuous_const)).sub
        ((continuous_const.sub continuous_id).mul continuous_const)

theorem binaryKL_eq_ratios {r p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    binaryKL r p =
      r * Real.log (r / p) + (1 - r) * Real.log ((1 - r) / (1 - p)) := by
  by_cases hr0 : r = 0
  · subst r
    simp [binaryKL, one_div, Real.log_inv]
  by_cases hr1 : r = 1
  · subst r
    simp [binaryKL, one_div, Real.log_inv]
  rw [Real.log_div hr0 hp.1.ne',
    Real.log_div (by intro h; apply hr1; linarith) (by linarith [hp.2] : 1 - p ≠ 0)]
  unfold binaryKL
  ring

theorem binaryKL_hasDerivAt_left (p : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => binaryKL x p)
      (Real.log r - Real.log (1 - r) - Real.log p + Real.log (1 - p)) r := by
  have h0 : r ≠ 0 := hr.1.ne'
  have h1 : 1 - r ≠ 0 := by linarith [hr.2]
  have h := (((Real.hasDerivAt_mul_log h0).add
    ((Real.hasDerivAt_mul_log h1).comp r ((hasDerivAt_const r (1 : ℝ)).sub
      (hasDerivAt_id r)))).sub
        ((hasDerivAt_id r).mul_const (Real.log p))).sub
          (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).mul_const
            (Real.log (1 - p)))
  convert h using 1
  simp
  ring

def binaryKLPinskerDerivative (p r : ℝ) : ℝ :=
  Real.log r - Real.log (1 - r) - Real.log p + Real.log (1 - p) - 4 * (r - p)

theorem binaryKL_sub_quadratic_hasDerivAt (p : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => binaryKL x p - 2 * (x - p) ^ 2)
      (binaryKLPinskerDerivative p r) r := by
  have h := (binaryKL_hasDerivAt_left p hr).sub
    ((((hasDerivAt_id r).sub_const p).pow 2).const_mul 2)
  convert h using 1
  simp [binaryKLPinskerDerivative]
  ring

theorem binaryKLPinskerDerivative_hasDerivAt (p : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (binaryKLPinskerDerivative p)
      (1 / r + 1 / (1 - r) - 4) r := by
  have h0 : r ≠ 0 := hr.1.ne'
  have h1 : 1 - r ≠ 0 := by linarith [hr.2]
  have h := (((((Real.hasDerivAt_log h0).sub
    ((Real.hasDerivAt_log h1).comp r ((hasDerivAt_const r (1 : ℝ)).sub
      (hasDerivAt_id r)))).sub_const (Real.log p)).add_const
        (Real.log (1 - p)))).sub
          (((hasDerivAt_id r).sub_const p).const_mul 4)
  convert h using 1
  simp

theorem binaryKL_second_derivative_ge_four {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 ≤ 1 / r + 1 / (1 - r) - 4 := by
  have h0 : 0 < r := hr.1
  have h1 : 0 < 1 - r := by linarith [hr.2]
  have heq : 1 / r + 1 / (1 - r) - 4 =
      (2 * r - 1) ^ 2 / (r * (1 - r)) := by
    field_simp
    ring
  rw [heq]
  exact div_nonneg (sq_nonneg _) (mul_pos h0 h1).le

theorem binaryKL_sub_quadratic_convex (p : ℝ) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun r => binaryKL r p - 2 * (r - p) ^ 2) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := binaryKLPinskerDerivative p)
    (f'' := fun r => 1 / r + 1 / (1 - r) - 4) (convex_Icc _ _)
  · exact ((binaryKL_continuous_left p).sub (by fun_prop)).continuousOn
  · intro r hr
    rw [interior_Icc] at hr
    exact (binaryKL_sub_quadratic_hasDerivAt p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact (binaryKLPinskerDerivative_hasDerivAt p hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    exact binaryKL_second_derivative_ge_four hr

/-- Sharp binary Pinsker inequality, including r=0 and r=1. -/
theorem binaryKL_pinsker {r p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    2 * (r - p) ^ 2 ≤ binaryKL r p := by
  have hconv := binaryKL_sub_quadratic_convex p
  have hpint : p ∈ interior (Icc (0 : ℝ) 1) := by simpa only [interior_Icc] using hp
  have hd := binaryKL_sub_quadratic_hasDerivAt p hp
  have hd0 : binaryKLPinskerDerivative p p = 0 := by
    unfold binaryKLPinskerDerivative
    ring
  have hder : derivWithin (fun r => binaryKL r p - 2 * (r - p) ^ 2) (Ioi p) p = 0 := by
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi p), hd0]
  have hmin : 0 ≤ binaryKL r p - 2 * (r - p) ^ 2 := by
    simpa only [binaryKL_self, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, sub_zero] using
      (hconv.isMinOn_of_rightDeriv_eq_zero hpint hder hr)
  linarith

theorem binaryKL_zero_left (p : ℝ) : binaryKL 0 p = -Real.log (1 - p) := by
  simp [binaryKL]

theorem binaryKL_one_left (p : ℝ) : binaryKL 1 p = -Real.log p := by
  simp [binaryKL]

/-- Exact value of the reverse-binomial likelihood exponent at its optimizer.
This is an identity about the actual logarithms, not an optimization hypothesis. -/
theorem binaryKL_optimizer_identity {p r : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpr : p < r) (hr : r < 1) :
    Real.log (1 + (r - p) / (1 - r)) -
      r * Real.log (1 + ((r - p) / (1 - r)) / p) = -binaryKL r p := by
  have hr0 : 0 < r := lt_trans hp.1 hpr
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hr1 : 0 < 1 - r := by linarith
  have hfirst : 1 + (r - p) / (1 - r) = (1 - p) / (1 - r) := by
    field_simp
    ring
  have hsecond : 1 + ((r - p) / (1 - r)) / p =
      (r * (1 - p)) / (p * (1 - r)) := by
    field_simp [hp.1.ne', hr1.ne']
    ring
  rw [hfirst, hsecond, Real.log_div hp1.ne' hr1.ne',
    Real.log_div (mul_pos hr0 hp1).ne' (mul_pos hp.1 hr1).ne',
    Real.log_mul hr0.ne' hp1.ne', Real.log_mul hp.1.ne' hr1.ne']
  unfold binaryKL
  ring

theorem binaryKL_optimizer_le_neg_two_sq {p r : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpr : p < r) (hr : r < 1) :
    Real.log (1 + (r - p) / (1 - r)) -
      r * Real.log (1 + ((r - p) / (1 - r)) / p) ≤ -2 * (r - p) ^ 2 := by
  rw [binaryKL_optimizer_identity hp hpr hr]
  have hpin := binaryKL_pinsker hp ⟨(lt_trans hp.1 hpr).le, hr.le⟩
  linarith

end Antichain
