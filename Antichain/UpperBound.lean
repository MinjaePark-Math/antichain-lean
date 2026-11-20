import Antichain.TileProduct
import Antichain.ChernoffRate
import Antichain.PartitionInterpolation
import Antichain.FloorIntegralApproximation

/-! The actual weighted partition upper bound, with only cited alcove geometry external. -/

noncomputable section

namespace Antichain

open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

theorem normalizedPartitionLog_upper_at_scale (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, normalizedPartitionLog n sigma c ≤
      tileCoefficientRate d hd epsilon + (d : ℝ) / ((d : ℝ) - 1) *
        Real.log (∑' B : AlcoveTile d,
          alcoveWeightSup sigma epsilon B ^ (((d : ℝ) - 1) / (d : ℝ))) + δ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < ((d : ℝ) - 1) / (d : ℝ) := div_pos (by linarith) (by linarith)
  have hs := alcoveWeightSup_rpow_summable hd H sigma hp hepsilon hepsilon1
  have hS : 0 < ∑' B : AlcoveTile d,
      alcoveWeightSup sigma epsilon B ^ (((d : ℝ) - 1) / (d : ℝ)) :=
    (Real.rpow_pos_of_pos (alcoveWeightSup_pos hd sigma epsilon (wordAlcove d [])) _).trans_le
      (hs.le_tsum (wordAlcove d []) (fun B _ => Real.rpow_nonneg
        (alcoveWeightSup_pos hd sigma epsilon B).le _))
  exact coefficient_dimension_upper_rate (fun n => weightedPartition n sigma c)
    (fun t => ∑' B : AlcoveTile d,
      Real.log (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B)))
    hd (fun n => weightedPartition_pos n sigma c hc hd) hS
    (fun n t ht => weightedPartition_le_factorial_exp_tileLogs hd H n sigma hepsilon hepsilon1 hc ht)
    (fun e he => alcoveTile_log_upper_rate hd H sigma hepsilon hepsilon1 hc he) hδ

theorem normalizedPartitionLog_upper_scaled (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, normalizedPartitionLog n sigma c ≤
      localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log (scaledSimplexVolume d epsilon *
          (∑' B : AlcoveTile d,
            alcoveWeightSup sigma epsilon B ^ (((d : ℝ) - 1) / (d : ℝ)))) + δ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < ((d : ℝ) - 1) / (d : ℝ) := div_pos (by linarith) (by linarith)
  have hs := alcoveWeightSup_rpow_summable hd H sigma hp hepsilon hepsilon1
  have hS : 0 < ∑' B : AlcoveTile d,
      alcoveWeightSup sigma epsilon B ^ (((d : ℝ) - 1) / (d : ℝ)) :=
    (Real.rpow_pos_of_pos (alcoveWeightSup_pos hd sigma epsilon (wordAlcove d [])) _).trans_le
      (hs.le_tsum (wordAlcove d []) (fun B _ => Real.rpow_nonneg
        (alcoveWeightSup_pos hd sigma epsilon B).le _))
  have h := normalizedPartitionLog_upper_at_scale hd H sigma hepsilon hepsilon1 hc hδ
  rw [Real.log_mul (scaledSimplexVolume_pos hd hepsilon).ne' hS.ne']
  unfold tileCoefficientRate at h
  filter_upwards [h] with n hn
  linarith

/-- The complete eventual upper-rate estimate in Lemma 4.5 for the actual Z_n.
All summation, coefficient optimization and Riemann approximation steps are
supplied internally. Only the precise cited alcove geometry remains external. -/
theorem normalizedPartitionLog_upper (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, normalizedPartitionLog n sigma c ≤
      localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log
          (∫ u : FloorSpace (Fin d), weightedFloorDensity sigma u ^
            (((d : ℝ) - 1) / (d : ℝ))) + δ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < ((d : ℝ) - 1) / (d : ℝ) := div_pos (by linarith) (by linarith)
  have hI := weightedFloorDensity_rpow_integral_pos sigma hp
  let C : ℝ := localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi)
  let q : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  let I : ℝ := ∫ u : FloorSpace (Fin d), weightedFloorDensity sigma u ^
    (((d : ℝ) - 1) / (d : ℝ))
  have hlim := (((Real.continuousAt_log hI.ne').tendsto.comp
    (tendsto_scaled_alcoveWeightSup_sum hd H sigma hp)).const_mul q).const_add C
  have hevent : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      0 < epsilon ∧ epsilon ≤ 1 ∧
        C + q * Real.log (epsilon ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal *
          (∑' B : AlcoveTile d, alcoveWeightSup sigma epsilon B ^
            (((d : ℝ) - 1) / (d : ℝ)))) < C + q * Real.log I + δ / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      hlim.eventually (Iio_mem_nhds (by linarith : C + q * Real.log I < C + q * Real.log I + δ / 2))]
      with epsilon hpos hle hsmall
    exact ⟨hpos, hle, hsmall⟩
  obtain ⟨epsilon, hpos, hle, hsmall⟩ := hevent.exists
  have h := normalizedPartitionLog_upper_scaled hd H sigma hpos hle hc (half_pos hδ)
  rw [scaledSimplexVolume_eq hd hpos] at h
  filter_upwards [h] with n hn
  change normalizedPartitionLog n sigma c ≤ C + q * Real.log I + δ
  change normalizedPartitionLog n sigma c ≤ C + q * Real.log _ + δ / 2 at hn
  linarith

end Antichain
