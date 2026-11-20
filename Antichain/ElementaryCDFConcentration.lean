import Antichain.RankCDF
import Antichain.UniformCDFConcentration

/-! Unconditional actual sorted-value and conditional rank-displacement tails. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 800000

theorem scalarSortedLaw_midpoint_exponential_tail_elementary {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      scalarSortedLaw n (sortedMidpointBad n epsilon) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  let delta := epsilon / 2
  have hd : 0 < delta := half_pos hepsilon
  obtain ⟨alpha, ha, hCDFtail⟩ := elementary_uniform_cdf_exponential_tail hd
  have hlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / epsilon ≤ n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [hCDFtail, hlarge, eventually_gt_atTop (0 : ℕ)] with n hnCDF hnlarge hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall : delta + 1 / (2 * (n : ℝ)) ≤ epsilon := by
    have hnε : 1 ≤ (n : ℝ) * epsilon := (div_le_iff₀ hepsilon).mp hnlarge
    have hf : (1 : ℝ) / (2 * (n : ℝ)) ≤ epsilon / 2 :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    dsimp [delta]
    linarith
  have hcube : ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => cubeCoordinateLaw),
      ∀ j, x j ∈ Icc (0 : ℝ) 1 := by
    rw [show Measure.pi (fun _ : Fin n => cubeCoordinateLaw) =
      (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi (fun _ => Icc (0 : ℝ) 1)) from
        (Measure.restrict_pi_pi (fun _ => (volume : Measure ℝ)) _).symm]
    exact (ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))).mono
      (fun _ h j => h j (Set.mem_univ j))
  rw [scalarSortedLaw, Measure.map_apply (sampleSortedValues_measurable n)
    (measurableSet_sortedMidpointBad n epsilon)]
  apply le_trans (measure_mono_ae ?_) hnCDF
  filter_upwards [iid_scalar_injective_ae n cubeCoordinateLaw, hcube] with x hx hxcube
  intro hbad
  by_contra hnot
  have hCDF : ∀ s ∈ Icc (0 : ℝ) 1, |scalarEmpiricalCDF n x s - s| ≤ delta := by
    intro s hs
    exact le_of_not_gt (fun h => hnot ⟨s, hs, h⟩)
  obtain ⟨r, hr⟩ := hbad
  exact not_lt_of_ge ((sorted_midpoint_error_le hn x hx hxcube hCDF r).trans hsmall) hr

/-- Actual conditional rank displacement, now proved without a cited DKW
premise. Conditioning uses the already proved exact sorted-coordinate law. -/
theorem rank_displacement_exponential_tail_elementary (d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (rankDisplacementEvent n d epsilon) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, hscalar⟩ := scalarSortedLaw_midpoint_exponential_tail_elementary hepsilon
  have htail (i : Fin d) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d
        ((fun x => coordinateSortedValues n d x i) ⁻¹' sortedMidpointBad n epsilon) ≤
          ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    refine ⟨alpha, ha, hscalar.mono ?_⟩
    intro n hn
    have hmeas : Measurable (fun x : CubeSample n d => coordinateSortedValues n d x i) :=
      (measurable_pi_apply i).comp (coordinateSortedValues_measurable n d)
    rw [← Measure.map_apply hmeas (measurableSet_sortedMidpointBad n epsilon),
      cubeAntichain_sortedCoordinate_law n d hd i]
    exact hn
  obtain ⟨a, ha, htail⟩ := finite_union_exponential_tail
    (fun n => cubeAntichainLaw n d)
    (fun i n => (fun x => coordinateSortedValues n d x i) ⁻¹' sortedMidpointBad n epsilon) htail
  refine ⟨a, ha, ?_⟩
  simpa only [rankDisplacementEvent_eq_sorted_union] using htail

end Antichain
