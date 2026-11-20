import Antichain.UpperBound
import Antichain.LowerBound

/-! The paper's actual weighted limit and logarithmic antichain counting theorem. -/

noncomputable section

namespace Antichain

open Filter MeasureTheory Asymptotics
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def weightedRateValue (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) : ℝ :=
  localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
    (d : ℝ) / ((d : ℝ) - 1) * Real.log
      (∫ u : FloorSpace (Fin d), weightedFloorDensity sigma u ^
        (((d : ℝ) - 1) / (d : ℝ)))

/-- Proposition 1.3 for the actual antichain model. Every analytic, geometric
volume and probability-model step is supplied. The only external premise is
the exact major cited alcove geometry, represented by `HumphreysAlcoveInput`. -/
theorem weightedPartition_rate_limit (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Tendsto (fun n : ℕ => normalizedPartitionLog n sigma c) atTop
      (𝓝 (weightedRateValue d hd sigma)) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [normalizedPartitionLog_lower hd H sigma c hc (half_pos hδ),
    normalizedPartitionLog_upper hd H sigma c hc (half_pos hδ)] with n hnlo hnhi
  rw [Real.dist_eq]
  apply abs_lt.mpr
  unfold weightedRateValue
  constructor <;> linarith

/-- Direct real-limsup source endpoint. Its finiteness is certified by the
proved limit, so no default real limsup of an unbounded sequence is used. -/
theorem weightedPartition_rate_limsup (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Filter.limsup (fun n : ℕ => normalizedPartitionLog n sigma c) atTop =
      weightedRateValue d hd sigma :=
  (weightedPartition_rate_limit hd H sigma c hc).limsup_eq

theorem weightedPartition_rate_liminf (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Filter.liminf (fun n : ℕ => normalizedPartitionLog n sigma c) atTop =
      weightedRateValue d hd sigma :=
  (weightedPartition_rate_limit hd H sigma c hc).liminf_eq

/-- Theorem 1.1, with the literal actual cube-antichain probability and a genuine
little-o remainder. The constant is independent of the sample count. -/
theorem antichain_counting_source (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) :
    ∃ beta : ℝ,
      (fun n : ℕ => Real.log (antichainProbability n d) +
        (n : ℝ) / ((d : ℝ) - 1) * Real.log (n : ℝ) - beta * (n : ℝ))
        =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  let beta := weightedRateValue d hd (0 : FloorSpace (Fin d) →ᵇ ℝ)
  refine ⟨beta, ?_⟩
  have hlim : Tendsto (fun n : ℕ =>
      normalizedPartitionLog n (0 : FloorSpace (Fin d) →ᵇ ℝ) 0 - beta) atTop (𝓝 0) := by
    simpa only [beta, sub_self] using
      (weightedPartition_rate_limit hd H (0 : FloorSpace (Fin d) →ᵇ ℝ)
        0 (by norm_num)).sub_const beta
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn hzero
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact False.elim (hnR.ne' hzero)
  · apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold normalizedPartitionLog
    rw [weightedPartition_zero]
    field_simp

end Antichain
