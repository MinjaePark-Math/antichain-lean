import Antichain.OneTileIntegral
import Antichain.GaussianPartitionIntegral

/-! The source one-tile bound for the actual Gaussian partition kernel. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal Pointwise BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def tileFloorWeight (sigma : FloorSpace (Fin d) →ᵇ ℝ) (u : FloorSpace (Fin d)) : ℝ :=
  standardFloorDensity u * Real.exp (sigma u)

omit [NeZero d] in
theorem tileFloorWeight_pos (sigma : FloorSpace (Fin d) →ᵇ ℝ) (u : FloorSpace (Fin d)) :
    0 < tileFloorWeight sigma u :=
  mul_pos (radialGaussianDensity_pos (by norm_num : (0 : ℝ) < 1) _) (Real.exp_pos _)

omit [NeZero d] in
theorem tileFloorWeight_continuous (sigma : FloorSpace (Fin d) →ᵇ ℝ) :
    Continuous (tileFloorWeight sigma) := by
  exact (radialGaussianDensity_continuous (V := FloorSpace (Fin d)) 1).mul
    (Real.continuous_exp.comp sigma.continuous)

def flooredTileEvent (B : Set (FloorSpace (Fin d))) (n : ℕ) :
    Set (FloorHeightConfiguration n d) :=
  {p | (∀ j, p.1 j ∈ B) ∧ p ∈ flooredAntichainEvent n d}

omit [NeZero d] in
theorem flooredTileEvent_measurable {B : Set (FloorSpace (Fin d))} (hB : MeasurableSet B)
    (n : ℕ) : MeasurableSet (flooredTileEvent B n) := by
  have hf : MeasurableSet {p : FloorHeightConfiguration n d | ∀ j, p.1 j ∈ B} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => hB.preimage ((measurable_pi_apply j).comp measurable_fst))
  exact hf.inter (flooredAntichainEvent_measurable n)

omit [NeZero d] in
theorem flooredTileEvent_fiber (B : Set (FloorSpace (Fin d))) (r : ℕ)
    (f : Fin (r + 1) → FloorSpace (Fin d)) (h : Fin (r + 1) → ℝ) :
    (f, h) ∈ flooredTileEvent B (r + 1) ↔
      (∀ j, f j ∈ B) ∧ h ∈ antichainHeightFiber f := by
  have heq : flooredPointCloud (r + 1) (f, h) = fullHeightPointCloud f h := by
    funext j i
    simp [flooredPointCloud, fullHeightPointCloud]
  simp only [flooredTileEvent, Set.mem_setOf_eq, flooredAntichainEvent,
    Set.mem_preimage, strictAntichainEvent, antichainHeightFiber, heq]

omit [NeZero d] in
theorem flooredPartitionKernel_ofReal_separated (r : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (f : Fin (r + 1) → FloorSpace (Fin d)) (h : Fin (r + 1) → ℝ) :
    ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c (f, h)) =
      (∏ j, ENNReal.ofReal (tileFloorWeight sigma (f j))) *
        normalizedHeightGaussianWeight (r + 1) c h := by
  unfold flooredPartitionKernel normalizedHeightGaussianWeight tileFloorWeight
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_prod_of_nonneg (fun j _ => by
      exact (tileFloorWeight_pos sigma (f j)).le)]
  ring

omit [NeZero d] in
/-- Tonelli identifies the auxiliary fiber integral with the source's literal
Gaussian kernel integral over the actual one-tile antichain region. -/
theorem oneTileIntegral_eq_kernelIntegral {B : Set (FloorSpace (Fin d))}
    (hB : MeasurableSet B) (r : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    oneTileIntegral B (tileFloorWeight sigma) c r =
      ∫⁻ p in flooredTileEvent B (r + 1),
        ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p) := by
  rw [← lintegral_indicator (flooredTileEvent_measurable hB (r + 1))]
  change oneTileIntegral B (tileFloorWeight sigma) c r =
    ∫⁻ p, (flooredTileEvent B (r + 1)).indicator
      (fun p => ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p)) p
      ∂((volume : Measure (Fin (r + 1) → FloorSpace (Fin d))).prod
        (volume : Measure (Fin (r + 1) → ℝ)))
  rw [lintegral_prod _ (((flooredPartitionKernel_continuous _ sigma c).measurable.ennreal_ofReal.indicator
    (flooredTileEvent_measurable hB (r + 1))).aemeasurable)]
  unfold oneTileIntegral
  rw [← lintegral_indicator (MeasurableSet.univ_pi (fun _ => hB))]
  apply lintegral_congr
  intro f
  by_cases hf : ∀ j, f j ∈ B
  · have hfmem : f ∈ univ.pi (fun _ : Fin (r + 1) => B) := by simpa using hf
    rw [Set.indicator_of_mem hfmem]
    have hconst : (∏ j, ENNReal.ofReal (tileFloorWeight sigma (f j))) ≠ ⊤ :=
      ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
    rw [← lintegral_const_mul' _ _ hconst,
      ← lintegral_indicator (measurableSet_antichainHeightFiber f)]
    apply lintegral_congr
    intro h
    by_cases hh : h ∈ antichainHeightFiber f
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem
        ((flooredTileEvent_fiber B r f h).mpr ⟨hf, hh⟩), flooredPartitionKernel_ofReal_separated]
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

theorem isCompact_scaled_reflectionTile (hd : 2 ≤ d) (word : List (Fin d)) (s : ℝ) :
    IsCompact (s • reflectionTile d word) := by
  have heq : reflectionWordMap d word =
      fun x => wordTranslation d word + floorPermutation (wordPermutation d word) x :=
    funext (reflectionWordMap_eq_affine d word)
  have hcont : Continuous (reflectionWordMap d word) := by
    rw [heq]
    exact continuous_const.add (floorPermutation (wordPermutation d word)).continuous
  have htile : IsCompact (reflectionTile d word) := (isCompact_referenceSimplex hd).image hcont
  exact htile.image (continuous_const_smul s)

/-- The exact model coefficient equals the integrated common-height coefficient
times the actual scaled pinned volume. -/
theorem tileCoefficient_as_pinnedMass (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s c : ℝ) (hs : 0 < s) (hc : c < 1 / 2) :
    ENNReal.ofReal (tileCoefficient d s c (r + 1)) =
      ENNReal.ofReal (commonHeightGaussianCoefficient (r + 1) c) *
        pinnedMass (s • reflectionTile d word) r := by
  have hcoef : 0 ≤ commonHeightGaussianCoefficient (r + 1) c :=
    (commonHeightGaussianCoefficient_pos (by omega) hc).le
  have hreal : ENNReal.ofReal (pinnedVolume (referenceSimplex d) r) =
      pinnedMass (referenceSimplex d) r :=
    ENNReal.ofReal_toReal (pinnedMass_referenceSimplex_lt_top hd r).ne
  rw [tileCoefficient_succ, ENNReal.ofReal_mul (mul_nonneg hcoef (pow_nonneg hs.le _)),
    ENNReal.ofReal_mul hcoef, ENNReal.ofReal_pow hs.le, hreal,
    pinnedMass_smul s hs, pinnedMass_reflectionTile]
  simp only [Fintype.card_fin]
  exact mul_assoc _ _ _

/-- The source one-tile kernel estimate for every scaled literal reflection tile. -/
theorem oneTile_model_bound_of_upperWeight (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s : ℝ) (hs : 0 < s) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) (M : ℝ)
    (hw : ∀ u ∈ s • reflectionTile d word, tileFloorWeight sigma u ≤ M) :
    (∫⁻ p in flooredTileEvent (s • reflectionTile d word) (r + 1),
      ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p)) ≤
        ENNReal.ofReal M ^ (r + 1) * ENNReal.ofReal (tileCoefficient d s c (r + 1)) := by
  rw [← oneTileIntegral_eq_kernelIntegral (isCompact_scaled_reflectionTile hd word s).measurableSet]
  rw [tileCoefficient_as_pinnedMass hd word r s c hs hc]
  exact oneTileIntegral_le (isCompact_scaled_reflectionTile hd word s).measurableSet
    (tileFloorWeight sigma) M c hc r hw

/-- The literal supremum of the floor weight over a tile, as in Section 4.1. -/
def tileWeightSup (sigma : FloorSpace (Fin d) →ᵇ ℝ) (B : Set (FloorSpace (Fin d))) : ℝ :=
  sSup (tileFloorWeight sigma '' B)

omit [NeZero d] in
theorem tileWeight_le_sup (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    {B : Set (FloorSpace (Fin d))} (hB : IsCompact B) {u : FloorSpace (Fin d)} (hu : u ∈ B) :
    tileFloorWeight sigma u ≤ tileWeightSup sigma B :=
  le_csSup (hB.image (tileFloorWeight_continuous sigma)).bddAbove
    (Set.mem_image_of_mem _ hu)

/-- Both inequalities in Lemma 4.1, with the actual tile supremum and actual model coefficient. -/
theorem oneTile_model_full_spec (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s : ℝ) (hs : 0 < s) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    let B := s • reflectionTile d word
    (∫⁻ p in flooredTileEvent B (r + 1),
      ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p)) ≤
        ENNReal.ofReal (tileWeightSup sigma B) ^ (r + 1) *
          oneTileIntegral B (fun _ => 1) c r ∧
    oneTileIntegral B (fun _ => 1) c r ≤ ENNReal.ofReal (tileCoefficient d s c (r + 1)) := by
  intro B
  have hB := isCompact_scaled_reflectionTile hd word s
  constructor
  · rw [← oneTileIntegral_eq_kernelIntegral hB.measurableSet]
    exact oneTileIntegral_le_weightBound hB.measurableSet (tileFloorWeight sigma)
      (tileWeightSup sigma B) c r (fun u hu => tileWeight_le_sup sigma hB hu)
  · rw [tileCoefficient_as_pinnedMass hd word r s c hs hc]
    exact oneTileIntegral_one_le_pinnedMass hB.measurableSet c hc r

theorem oneTile_model_bound (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s : ℝ) (hs : 0 < s) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    (∫⁻ p in flooredTileEvent (s • reflectionTile d word) (r + 1),
      ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p)) ≤
        ENNReal.ofReal (tileWeightSup sigma (s • reflectionTile d word)) ^ (r + 1) *
          ENNReal.ofReal (tileCoefficient d s c (r + 1)) :=
  oneTile_model_bound_of_upperWeight hd word r s hs sigma c hc _
    (fun _ hu => tileWeight_le_sup sigma (isCompact_scaled_reflectionTile hd word s) hu)

/-- The actual one-tile source integral is finite, so its nonnegative and
ordinary-real integral interpretations agree. -/
theorem oneTile_kernelIntegral_lt_top (hd : 2 ≤ d) (word : List (Fin d))
    (r : ℕ) (s : ℝ) (hs : 0 < s) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    (∫⁻ p in flooredTileEvent (s • reflectionTile d word) (r + 1),
      ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p)) < ⊤ :=
  (oneTile_model_bound hd word r s hs sigma c hc).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)

end Antichain
