import Antichain.BinaryKLPinsker
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-! Actual existence of the interior stationary point used for the sharp
one-sided empirical-CDF likelihood barrier. No stationary-point hypothesis
or DKW conclusion is assumed. -/

noncomputable section

namespace Antichain

open Set Filter
open scoped Topology

def dkwStationaryGap (δ p : ℝ) : ℝ :=
  p * (1 - p) *
    (Real.log (p + δ) + Real.log (1 - p) - Real.log p - Real.log (1 - p - δ)) - δ

theorem dkwStationaryGap_continuousOn {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ < 1) :
    ContinuousOn (dkwStationaryGap δ) (Ioo (0 : ℝ) (1 - δ)) := by
  intro p hp
  have hp0 : 0 < p := hp.1
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hpd : 0 < p + δ := by linarith
  have htail : 0 < 1 - p - δ := by linarith [hp.2]
  have hcont : ContinuousAt (dkwStationaryGap δ) p := by
    unfold dkwStationaryGap
    fun_prop (disch := positivity)
  exact hcont.continuousWithinAt

theorem dkwStationaryGap_continuousAt_zero {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ContinuousAt (dkwStationaryGap δ) 0 := by
  have hlog1 : ContinuousAt (fun p : ℝ => Real.log (p + δ)) 0 :=
    (continuousAt_id.add_const δ).log (by dsimp; linarith)
  have hlog2 : ContinuousAt (fun p : ℝ => Real.log (1 - p)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  have hlog3 : ContinuousAt (fun p : ℝ => Real.log (1 - p - δ)) 0 :=
    ((continuousAt_const.sub continuousAt_id).sub_const δ).log (by dsimp; linarith)
  have heq : dkwStationaryGap δ = fun p =>
      p * (1 - p) * (Real.log (p + δ) + Real.log (1 - p) - Real.log (1 - p - δ)) -
        (1 - p) * (p * Real.log p) - δ := by
    funext p
    unfold dkwStationaryGap
    ring
  rw [heq]
  exact (((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).mul
    ((hlog1.add hlog2).sub hlog3)).sub
      ((continuousAt_const.sub continuousAt_id).mul
        Real.continuous_mul_log.continuousAt)).sub_const δ

theorem dkwStationaryGap_tendsto_zero_right {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (dkwStationaryGap δ) (𝓝[>] (0 : ℝ)) (𝓝 (-δ)) := by
  simpa [dkwStationaryGap] using
    (dkwStationaryGap_continuousAt_zero hδ hδ1).tendsto.mono_left nhdsWithin_le_nhds

theorem dkwStationaryGap_tendsto_upper_left {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (dkwStationaryGap δ) (𝓝[<] (1 - δ)) atTop := by
  have hb : 0 < 1 - δ := by linarith
  have hid : Tendsto (fun p : ℝ => p) (𝓝[<] (1 - δ)) (𝓝 (1 - δ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun p : ℝ => 1 - p - δ) (𝓝[<] (1 - δ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hzero : (1 : ℝ) - (1 - δ) - δ = 0 := by ring
      simpa only [hzero] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hid).sub_const δ
    · filter_upwards [self_mem_nhdsWithin] with p hp
      change 0 < 1 - p - δ
      have hp' : p < 1 - δ := hp
      linarith
  have hlog : Tendsto (fun p : ℝ => -Real.log (1 - p - δ))
      (𝓝[<] (1 - δ)) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)
  have hcoef : Tendsto (fun p : ℝ => p * (1 - p))
      (𝓝[<] (1 - δ)) (𝓝 ((1 - δ) * (1 - (1 - δ)))) :=
    hid.mul (tendsto_const_nhds.sub hid)
  have hcoefpos : 0 < (1 - δ) * (1 - (1 - δ)) := by
    exact mul_pos hb (by linarith)
  have hprod := hcoef.pos_mul_atTop hcoefpos hlog
  have hlog1 : ContinuousAt (fun p : ℝ => Real.log (p + δ)) (1 - δ) :=
    (continuousAt_id.add_const δ).log (by dsimp; linarith)
  have hlog2 : ContinuousAt (fun p : ℝ => Real.log (1 - p)) (1 - δ) :=
    (continuousAt_const.sub continuousAt_id).log (by dsimp; linarith)
  have hlog3 : ContinuousAt (fun p : ℝ => Real.log p) (1 - δ) :=
    Real.continuousAt_log hb.ne'
  have hfinite : ContinuousAt (fun p : ℝ =>
      p * (1 - p) * (Real.log (p + δ) + Real.log (1 - p) - Real.log p) - δ)
      (1 - δ) :=
    ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).mul
      ((hlog1.add hlog2).sub hlog3)).sub_const δ
  have hlim := (hfinite.tendsto.mono_left nhdsWithin_le_nhds).add_atTop hprod
  convert hlim using 1
  funext p
  unfold dkwStationaryGap
  ring

theorem exists_dkwStationaryGap_zero {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ p ∈ Ioo (0 : ℝ) (1 - δ), dkwStationaryGap δ p = 0 := by
  have hb : 0 < 1 - δ := by linarith
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓟 (Ioo (0 : ℝ) (1 - δ)) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with p hp0 hp1
    exact ⟨hp0, hp1⟩
  have hr : 𝓝[<] (1 - δ) ≤ 𝓟 (Ioo (0 : ℝ) (1 - δ)) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hb).filter_mono nhdsWithin_le_nhds] with p hp1 hp0
    exact ⟨hp0, hp1⟩
  have himage := isPreconnected_Ioo.intermediate_value_Ioi hl hr
    (dkwStationaryGap_continuousOn hδ hδ1)
    (dkwStationaryGap_tendsto_zero_right hδ hδ1)
    (dkwStationaryGap_tendsto_upper_left hδ hδ1)
    (show (0 : ℝ) ∈ Ioi (-δ) by change -δ < 0; linarith)
  exact himage

end Antichain
