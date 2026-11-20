import Antichain.OneTileModel

/-! Ordinary-real integral endpoints for every inequality of source Lemma 4.1. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal Pointwise BoundedContinuousFunction

def oneTileMiddleKernel {d : ℕ} (n : ℕ) (c : ℝ) (p : FloorHeightConfiguration n d) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-((1 / 2 : ℝ) - c) * ∑ j, p.2 j ^ 2)

theorem oneTileMiddleKernel_nonneg {d : ℕ} (n : ℕ) (c : ℝ) (p : FloorHeightConfiguration n d) :
    0 ≤ oneTileMiddleKernel n c p := by unfold oneTileMiddleKernel; positivity

theorem oneTileMiddleKernel_continuous {d : ℕ} (n : ℕ) (c : ℝ) :
    Continuous (oneTileMiddleKernel (d := d) n c) := by unfold oneTileMiddleKernel; fun_prop

theorem oneTileIntegral_one_eq_middleKernel_lintegral {d : ℕ}
    {B : Set (FloorSpace (Fin d))} (hB : MeasurableSet B) (r : ℕ) (c : ℝ) :
    oneTileIntegral B (fun _ => 1) c r =
      ∫⁻ p in flooredTileEvent B (r + 1), ENNReal.ofReal (oneTileMiddleKernel (r + 1) c p) := by
  rw [oneTileIntegral_one, ← lintegral_indicator (flooredTileEvent_measurable hB (r + 1))]
  change _ = ∫⁻ p, (flooredTileEvent B (r + 1)).indicator
    (fun p => ENNReal.ofReal (oneTileMiddleKernel (r + 1) c p)) p
    ∂((volume : Measure (Fin (r + 1) → FloorSpace (Fin d))).prod
      (volume : Measure (Fin (r + 1) → ℝ)))
  rw [lintegral_prod _ (((oneTileMiddleKernel_continuous _ c).measurable.ennreal_ofReal.indicator
    (flooredTileEvent_measurable hB (r + 1))).aemeasurable)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi (fun _ => hB))]
  apply lintegral_congr
  intro f
  by_cases hf : ∀ j, f j ∈ B
  · have hfmem : f ∈ univ.pi (fun _ : Fin (r + 1) => B) := by simpa using hf
    rw [Set.indicator_of_mem hfmem,
      ← lintegral_indicator (measurableSet_antichainHeightFiber f)]
    apply lintegral_congr
    intro h
    by_cases hh : h ∈ antichainHeightFiber f
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem
        ((flooredTileEvent_fiber B r f h).mpr ⟨hf, hh⟩)]
      rfl
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem
        (fun hp => hh ((flooredTileEvent_fiber B r f h).mp hp).2)]
  · have hfmem : f ∉ univ.pi (fun _ : Fin (r + 1) => B) := by simpa using hf
    rw [Set.indicator_of_notMem hfmem]
    symm
    calc
      _ = ∫⁻ _h : Fin (r + 1) → ℝ, (0 : ℝ≥0∞) := by
        apply lintegral_congr
        intro h
        exact Set.indicator_of_notMem (fun hp => hf ((flooredTileEvent_fiber B r f h).mp hp).1) _
      _ = 0 := by simp

theorem oneTile_middle_real_eq_toReal {d : ℕ} {B : Set (FloorSpace (Fin d))}
    (hB : MeasurableSet B) (r : ℕ) (c : ℝ) :
    (∫ p in flooredTileEvent B (r + 1), oneTileMiddleKernel (r + 1) c p) =
      (oneTileIntegral B (fun _ => 1) c r).toReal := by
  rw [oneTileIntegral_one_eq_middleKernel_lintegral hB]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (oneTileMiddleKernel_nonneg _ c))
    (oneTileMiddleKernel_continuous _ c).measurable.aestronglyMeasurable

theorem oneTile_weighted_real_eq_toReal {d : ℕ} (r : ℕ)
    (B : Set (FloorSpace (Fin d))) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    (∫ p in flooredTileEvent B (r + 1), flooredPartitionKernel (r + 1) sigma c p) =
      (∫⁻ p in flooredTileEvent B (r + 1),
        ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p)).toReal :=
  integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (flooredPartitionKernel_nonneg _ sigma c))
    (flooredPartitionKernel_continuous _ sigma c).measurable.aestronglyMeasurable

variable {d : ℕ} [NeZero d]

theorem tileWeightSup_pos (hd : 2 ≤ d) (word : List (Fin d)) (s : ℝ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) :
    0 < tileWeightSup sigma (s • reflectionTile d word) := by
  have hzero : (0 : FloorSpace (Fin d)) ∈ referenceSimplex d := by
    constructor
    · intro i j _
      exact le_rfl
    · intro i j
      simp
  have hmem : s • reflectionWordMap d word 0 ∈ s • reflectionTile d word :=
    ⟨reflectionWordMap d word 0, ⟨0, hzero, rfl⟩, rfl⟩
  exact (tileFloorWeight_pos sigma _).trans_le
    (tileWeight_le_sup sigma (isCompact_scaled_reflectionTile hd word s) hmem)

/-- Every ordinary integral in Lemma 4.1 is integrable on the actual one-tile
region; no default value of an undefined Bochner integral is used. -/
theorem oneTile_middle_integrableOn (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s c : ℝ) (hs : 0 < s) (hc : c < 1 / 2) :
    IntegrableOn (oneTileMiddleKernel (r + 1) c)
      (flooredTileEvent (s • reflectionTile d word) (r + 1)) := by
  constructor
  · exact (oneTileMiddleKernel_continuous _ c).measurable.aestronglyMeasurable
  · apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (oneTileMiddleKernel_nonneg _ c))).mpr
    rw [← oneTileIntegral_one_eq_middleKernel_lintegral
      (isCompact_scaled_reflectionTile hd word s).measurableSet]
    exact ((oneTile_model_full_spec hd word r s hs 0 c hc).2).trans_lt ENNReal.ofReal_lt_top

theorem oneTile_weighted_integrableOn (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s : ℝ) (hs : 0 < s) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    IntegrableOn (flooredPartitionKernel (r + 1) sigma c)
      (flooredTileEvent (s • reflectionTile d word) (r + 1)) := by
  constructor
  · exact (flooredPartitionKernel_continuous _ sigma c).measurable.aestronglyMeasurable
  · apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (flooredPartitionKernel_nonneg _ sigma c))).mpr
    exact oneTile_kernelIntegral_lt_top hd word r s hs sigma c hc

/-- Both printed one-tile inequalities, now as finite ordinary real integrals
with the actual supremum, weight-one middle kernel, and exact coefficient. -/
theorem oneTile_real_full_spec (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s : ℝ) (hs : 0 < s) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    let B := s • reflectionTile d word
    (∫ p in flooredTileEvent B (r + 1), flooredPartitionKernel (r + 1) sigma c p) ≤
      tileWeightSup sigma B ^ (r + 1) *
        (∫ p in flooredTileEvent B (r + 1), oneTileMiddleKernel (r + 1) c p) ∧
    (∫ p in flooredTileEvent B (r + 1), oneTileMiddleKernel (r + 1) c p) ≤
      tileCoefficient d s c (r + 1) := by
  intro B
  have hB := (isCompact_scaled_reflectionTile hd word s).measurableSet
  have hspec := oneTile_model_full_spec hd word r s hs sigma c hc
  have hmiddle : oneTileIntegral B (fun _ => 1) c r < ⊤ := hspec.2.trans_lt ENNReal.ofReal_lt_top
  have hsup := (tileWeightSup_pos hd word s sigma).le
  have hcoef := (tileCoefficient_pos hd hs hc (r + 1)).le
  constructor
  · rw [oneTile_weighted_real_eq_toReal, oneTile_middle_real_eq_toReal hB]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hmiddle.ne) hspec.1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hsup] using h
  · rw [oneTile_middle_real_eq_toReal hB]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hspec.2
    simpa only [ENNReal.toReal_ofReal hcoef] using h

end Antichain
