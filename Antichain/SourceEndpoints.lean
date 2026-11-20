import Antichain.WeightedLimit

/-! Literal source-facing real limsup/liminf and universal weighted-limit
statements, with all boundedness and actual-model bridges supplied internally. -/

noncomputable section

namespace Antichain

open Filter MeasureTheory Set Metric
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

/-- The complete quantifier order of Proposition 1.3: one finite real constant
works for every bounded continuous floor test and every c<1/2. -/
theorem weighted_volume_source (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) :
    ∃ gamma : ℝ, ∀ sigma : FloorSpace (Fin d) →ᵇ ℝ, ∀ c : ℝ, c < 1 / 2 →
      Tendsto (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop
        (𝓝 (gamma - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
          (d : ℝ) / ((d : ℝ) - 1) * Real.log
            (∫ u : FloorSpace (Fin d), (standardFloorDensity u * Real.exp (sigma u)) ^
              (((d : ℝ) - 1) / (d : ℝ))))) := by
  refine ⟨localGammaConstant d hd, fun sigma c hc => ?_⟩
  simpa only [normalizedPartitionLog, weightedRateValue, weightedFloorDensity] using
    weightedPartition_rate_limit hd H sigma c hc

/-- Literal printed real-limsup Lemma 4.5. Finiteness follows from the proved
actual weighted limit; no separate boundedness hypothesis is introduced. -/
theorem weighted_upper_limsup_source (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Filter.limsup (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
      Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop ≤
      localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log
          (∫ u : FloorSpace (Fin d), (standardFloorDensity u * Real.exp (sigma u)) ^
            (((d : ℝ) - 1) / (d : ℝ))) := by
  simpa only [normalizedPartitionLog, weightedRateValue, weightedFloorDensity] using
    (weightedPartition_rate_limsup hd H sigma c hc).le

/-- Literal printed real-liminf Lemma 5.5. -/
theorem weighted_lower_liminf_source (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log
        (∫ u : FloorSpace (Fin d), (standardFloorDensity u * Real.exp (sigma u)) ^
          (((d : ℝ) - 1) / (d : ℝ))) ≤
      Filter.liminf (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop := by
  simpa only [normalizedPartitionLog, weightedRateValue, weightedFloorDensity] using
    (weightedPartition_rate_liminf hd H sigma c hc).symm.le

/-- Literal printed real-liminf Lemma 5.4 for positive-volume closed cubes
with pairwise disjoint interiors. Actual upper boundedness is derived from
the proved weighted limit before the real liminf is used. -/
theorem cube_lower_liminf_source (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (hJ : 0 < J) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j => Disjoint (interior (orthonormalFloorCube b (a i) (L i)))
      (interior (orthonormalFloorCube b (a j) (L j))))) :
    localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log (cubeLowerSum sigma b J a L) ≤
      Filter.liminf (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop := by
  have hlim := weightedPartition_rate_limit hd H sigma c hc
  change _ ≤ Filter.liminf (fun n : ℕ => normalizedPartitionLog n sigma c) atTop
  apply (le_liminf_iff' hlim.isBoundedUnder_le.isCobounded_flip hlim.isBoundedUnder_ge).mpr
  intro y hy
  have he := normalizedPartitionLog_cubes_lower hd H sigma c hc b J hJ a L hL hdis
    (sub_pos.mpr hy)
  filter_upwards [he] with n hn
  linarith

end Antichain
