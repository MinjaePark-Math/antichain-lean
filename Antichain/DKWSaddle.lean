import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import Antichain.DKWStationary

/-! Analytic saddle point for the sharp uniform empirical-CDF bound.
No empirical-process or entropy bound is assumed in this module. -/

noncomputable section
namespace Antichain
open Set Filter
open scoped Topology

def dkwLogGap (z : ℝ) : ℝ := (z + 2) * Real.log (1 + z) - 2 * z

theorem dkw_log_fraction_lt {z : ℝ} (hz : 0 < z) :
    z / (1 + z) < Real.log (1 + z) := by
  have hp : 0 < 1 + z := by linarith
  have hn : (1 + z)⁻¹ ≠ (1 : ℝ) := by
    intro h
    have h' := congrArg (fun t : ℝ => t * (1 + z)) h
    simp only [inv_mul_cancel₀ hp.ne', one_mul] at h'
    linarith
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hp) hn
  rw [Real.log_inv] at h
  have heq : 1 - (1 + z)⁻¹ = z / (1 + z) := by field_simp; ring
  linarith

theorem dkwLogGap_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt dkwLogGap (Real.log (1 + z) - z / (1 + z)) z := by
  have hp : 1 + z ≠ 0 := by positivity
  have hlog := ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)).log hp
  have h := (((hasDerivAt_id z).add_const 2).mul hlog).sub
    ((hasDerivAt_id z).const_mul 2)
  convert h using 1
  dsimp [dkwLogGap]
  field_simp
  ring

theorem dkwLogGap_strictMono : StrictMonoOn dkwLogGap (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro z hz
    exact (dkwLogGap_hasDerivAt hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ici] at hz
    rw [(dkwLogGap_hasDerivAt hz.le).deriv]
    exact sub_pos.mpr (dkw_log_fraction_lt hz)

theorem dkwLogGap_pos {z : ℝ} (hz : 0 < z) : 0 < dkwLogGap z := by
  have h := dkwLogGap_strictMono (by simp) hz.le hz
  simpa [dkwLogGap] using h

def dkwSlopeRatio (z : ℝ) : ℝ :=
  ((1 + z) * Real.log (1 + z) - z) / z ^ 2

theorem dkwSlopeRatio_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt dkwSlopeRatio (-dkwLogGap z / z ^ 3) z := by
  have hp : 1 + z ≠ 0 := by positivity
  have hlog := ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)).log hp
  have hnum := (((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)).mul hlog).sub
    (hasDerivAt_id z)
  have h := hnum.div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz.ne')
  convert h using 1
  dsimp [dkwSlopeRatio, dkwLogGap]
  field_simp
  ring

theorem dkwSlopeRatio_strictAnti : StrictAntiOn dkwSlopeRatio (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro z hz
    exact (dkwSlopeRatio_hasDerivAt hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioi] at hz
    rw [(dkwSlopeRatio_hasDerivAt hz).deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (dkwLogGap_pos hz)) (pow_pos hz 3)

def dkwBarrier (δ lam p : ℝ) : ℝ :=
  Real.log (1 + lam) - (p + δ) * (Real.log (p + lam) - Real.log p)

def dkwBarrierDerivative (δ lam p : ℝ) : ℝ :=
  -(Real.log (p + lam) - Real.log p) + (p + δ) * lam / (p * (p + lam))

theorem dkwBarrier_hasDerivAt {δ lam p : ℝ} (hlam : 0 < lam) (hp : 0 < p) :
    HasDerivAt (dkwBarrier δ lam) (dkwBarrierDerivative δ lam p) p := by
  have hlog := ((hasDerivAt_id p).add_const lam).log (by positivity : p + lam ≠ 0)
  have h := (hasDerivAt_const p (Real.log (1 + lam))).sub
    (((hasDerivAt_id p).add_const δ).mul (hlog.sub (Real.hasDerivAt_log hp.ne')))
  convert h using 1
  dsimp [dkwBarrier, dkwBarrierDerivative]
  field_simp
  ring

theorem dkwBarrierDerivative_ratio {δ lam p : ℝ} (hlam : 0 < lam) (hp : 0 < p) :
    dkwBarrierDerivative δ lam p =
      (lam ^ 2 / (p * (p + lam))) * (δ / lam - dkwSlopeRatio (lam / p)) := by
  have hplam : 0 < p + lam := by positivity
  have hr : 1 + lam / p = (p + lam) / p := by field_simp
  have hlog : Real.log (1 + lam / p) = Real.log (p + lam) - Real.log p := by
    rw [hr, Real.log_div hplam.ne' hp.ne']
  unfold dkwBarrierDerivative dkwSlopeRatio
  rw [hlog]
  field_simp
  ring

theorem dkwBarrier_eq_likelihood {δ lam p : ℝ} (hlam : 0 < lam) (hp : 0 < p) :
    dkwBarrier δ lam p =
      Real.log (1 + lam) - (p + δ) * Real.log (1 + lam / p) := by
  have heq : 1 + lam / p = (p + lam) / p := by field_simp
  rw [heq, Real.log_div (by positivity : p + lam ≠ 0) hp.ne']
  rfl

/-- The stationary point in the spatial variable is a genuine global maximum.
The proof uses the strictly decreasing logarithmic slope ratio, not a minimax
theorem or an assumed saddle-point property. -/
theorem dkwBarrier_stationary_global {δ lam p0 : ℝ} (hlam : 0 < lam)
    (hp0 : 0 < p0) (hstation : dkwBarrierDerivative δ lam p0 = 0)
    {p : ℝ} (hp : 0 < p) : dkwBarrier δ lam p ≤ dkwBarrier δ lam p0 := by
  have hf0 : 0 < lam ^ 2 / (p0 * (p0 + lam)) := by positivity
  have heq : δ / lam = dkwSlopeRatio (lam / p0) := by
    rw [dkwBarrierDerivative_ratio hlam hp0] at hstation
    have h := (mul_eq_zero.mp hstation).resolve_left hf0.ne'
    exact sub_eq_zero.mp h
  have hleft (x : ℝ) (hx : 0 < x) (hxp : x ≤ p0) :
      0 ≤ dkwBarrierDerivative δ lam x := by
    have hdiv : lam / p0 ≤ lam / x :=
      div_le_div_of_nonneg_left hlam.le hx hxp
    have hratio := dkwSlopeRatio_strictAnti.antitoneOn
      (div_pos hlam hp0) (div_pos hlam hx) hdiv
    rw [dkwBarrierDerivative_ratio hlam hx, heq]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hratio)
  have hright (x : ℝ) (hx : 0 < x) (hpx : p0 ≤ x) :
      dkwBarrierDerivative δ lam x ≤ 0 := by
    have hdiv : lam / x ≤ lam / p0 :=
      div_le_div_of_nonneg_left hlam.le hp0 hpx
    have hratio := dkwSlopeRatio_strictAnti.antitoneOn
      (div_pos hlam hx) (div_pos hlam hp0) hdiv
    rw [dkwBarrierDerivative_ratio hlam hx, heq]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hratio)
  rcases le_total p p0 with hpp | hpp
  · have hc : ContinuousOn (dkwBarrier δ lam) (Icc p p0) := by
      intro x hx
      exact (dkwBarrier_hasDerivAt hlam (hp.trans_le hx.1)).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ (dkwBarrier δ lam) (interior (Icc p p0)) := by
      intro x hx
      rw [interior_Icc] at hx
      exact (dkwBarrier_hasDerivAt hlam (hp.trans hx.1)).differentiableAt.differentiableWithinAt
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc p p0) hc hd (by
      intro x hx
      rw [interior_Icc] at hx
      rw [(dkwBarrier_hasDerivAt hlam (hp.trans hx.1)).deriv]
      exact hleft x (hp.trans hx.1) hx.2.le)
    exact hm ⟨le_rfl, hpp⟩ ⟨hpp, le_rfl⟩ hpp

  · have hc : ContinuousOn (dkwBarrier δ lam) (Icc p0 p) := by
      intro x hx
      exact (dkwBarrier_hasDerivAt hlam (hp0.trans_le hx.1)).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ (dkwBarrier δ lam) (interior (Icc p0 p)) := by
      intro x hx
      rw [interior_Icc] at hx
      exact (dkwBarrier_hasDerivAt hlam (hp0.trans hx.1)).differentiableAt.differentiableWithinAt
    have hm := antitoneOn_of_deriv_nonpos (convex_Icc p0 p) hc hd (by
      intro x hx
      rw [interior_Icc] at hx
      rw [(dkwBarrier_hasDerivAt hlam (hp0.trans hx.1)).deriv]
      exact hright x (hp0.trans hx.1) hx.1.le)
    exact hm ⟨le_rfl, hpp⟩ ⟨hpp, le_rfl⟩ hpp

theorem dkwBarrier_stationary_of_gap {δ p : ℝ} (hδ : 0 < δ)
    (hp : p ∈ Ioo (0 : ℝ) (1 - δ)) (hgap : dkwStationaryGap δ p = 0) :
    dkwBarrierDerivative δ (δ / (1 - p - δ)) p = 0 := by
  have hppos : 0 < p := hp.1
  have hD : 0 < 1 - p - δ := by linarith [hp.2]
  have h1p : 0 < 1 - p := by linarith [hp.2]
  have hq : 0 < p + δ := by positivity
  have hsum : p + δ / (1 - p - δ) = (p + δ) * (1 - p) / (1 - p - δ) := by
    field_simp
    ring
  have hlog : Real.log (p + δ / (1 - p - δ)) - Real.log p =
      Real.log (p + δ) + Real.log (1 - p) - Real.log p - Real.log (1 - p - δ) := by
    rw [hsum, Real.log_div (mul_pos hq h1p).ne' hD.ne', Real.log_mul hq.ne' h1p.ne']
    ring
  have hfrac : (p + δ) * (δ / (1 - p - δ)) /
      (p * (p + δ / (1 - p - δ))) = δ / (p * (1 - p)) := by
    rw [hsum]
    field_simp
  have hL : Real.log (p + δ) + Real.log (1 - p) - Real.log p - Real.log (1 - p - δ) =
      δ / (p * (1 - p)) := by
    apply (eq_div_iff (mul_ne_zero hp.1.ne' h1p.ne')).mpr
    unfold dkwStationaryGap at hgap
    linarith
  unfold dkwBarrierDerivative
  rw [hlog, hfrac, hL]
  ring

/-- The exact uniform likelihood barrier giving the constant 2 in DKW.
An actual stationary point is constructed by the preceding IVT development,
then the global maximum and the proved sharp binary Pinsker inequality apply.
This theorem assumes no saddle-point or empirical-distribution result. -/
theorem sharpDKW_likelihood_barrier {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p : ℝ, 0 < p →
      Real.log (1 + lam) - (p + δ) * Real.log (1 + lam / p) ≤ -2 * δ ^ 2 := by
  obtain ⟨p0, hp0, hgap⟩ := exists_dkwStationaryGap_zero hδ hδ1
  let lam := δ / (1 - p0 - δ)
  have hlam : 0 < lam := div_pos hδ (by linarith [hp0.2])
  have hstation : dkwBarrierDerivative δ lam p0 = 0 :=
    dkwBarrier_stationary_of_gap hδ hp0 hgap
  have hopt := binaryKL_optimizer_le_neg_two_sq
    (show p0 ∈ Ioo (0 : ℝ) 1 by exact ⟨hp0.1, by linarith [hp0.2]⟩)
    (show p0 < p0 + δ by linarith) (show p0 + δ < 1 by linarith [hp0.2])
  have heqlam : ((p0 + δ) - p0) / (1 - (p0 + δ)) = lam := by
    dsimp [lam]
    congr 1 <;> ring
  rw [heqlam] at hopt
  have hbound : dkwBarrier δ lam p0 ≤ -2 * δ ^ 2 := by
    rw [dkwBarrier_eq_likelihood hlam hp0.1]
    convert hopt using 1
    ring
  refine ⟨lam, hlam, ?_⟩
  intro p hp
  rw [← dkwBarrier_eq_likelihood hlam hp]
  exact (dkwBarrier_stationary_global hlam hp0.1 hstation hp).trans hbound

end Antichain
