import Antichain.GaussianConcentration
import Antichain.DirectAlcoveInput
import Antichain.SourceEndpoints
import Antichain.SourceCalculations
import Antichain.ProbabilityConsequences
import Antichain.RankCounting
import Antichain.WeakBruhatIntervals
import Antichain.Replication
import Antichain.ShapeGeometry

/-! Complete source statements with the actual geometric record supplied by
its direct proof. No cited mathematical premise remains in these types. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

theorem weighted_volume_source_direct (hd : 2 ≤ d) :
    ∃ gamma : ℝ, ∀ sigma : FloorSpace (Fin d) →ᵇ ℝ, ∀ c : ℝ, c < 1 / 2 →
      Tendsto (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop
        (𝓝 (gamma - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
          (d : ℝ) / ((d : ℝ) - 1) * Real.log
            (∫ u : FloorSpace (Fin d), (standardFloorDensity u * Real.exp (sigma u)) ^
              (((d : ℝ) - 1) / (d : ℝ))))) := by
  exact @weighted_volume_source d _ hd (humphreysAlcoveInput_direct hd)

theorem weightedPartition_rate_limit_direct (hd : 2 ≤ d) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Tendsto (fun n : ℕ => normalizedPartitionLog n sigma c) atTop
      (𝓝 (weightedRateValue d hd sigma)) := by
  exact @weightedPartition_rate_limit d _ hd (humphreysAlcoveInput_direct hd) sigma c hc

theorem antichain_counting_source_direct (hd : 2 ≤ d) :
    ∃ beta : ℝ,
      (fun n : ℕ => Real.log (antichainProbability n d) +
        (n : ℝ) / ((d : ℝ) - 1) * Real.log (n : ℝ) - beta * (n : ℝ))
        =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  exact @antichain_counting_source d _ hd (humphreysAlcoveInput_direct hd)

theorem antichain_normalized_log_limit_explicit_direct (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => Real.log (antichainProbability n d) / (n : ℝ) +
      Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop
      (𝓝 (localGammaConstant d hd + (d : ℝ) / 2 * Real.log ((d : ℝ) / ((d : ℝ) - 1)))) := by
  exact @antichain_normalized_log_limit_explicit d _ hd (humphreysAlcoveInput_direct hd)

theorem euclidean_shape_exponential_concentration_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d {x | δ < hausdorffDist (euclideanSampleSet n d x)
        (closure ((WithLp.toLp 2 : CubePoint d → EuclideanSpace ℝ (Fin d)) ''
          normalQuantileSurface (Fin d)))} ≤ ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  exact @euclidean_shape_exponential_concentration d _ hd (humphreysAlcoveInput_direct hd) δ hδ

theorem closed_cube_empirical_source_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d) {U : Set (ProbabilityMeasure (ClosedCubePoint d))} (hUopen : IsOpen U) (hUmem : closedCubeLimitingProbability d ∈ U) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      closedCubeAntichainLaw n d {x | empiricalClosedCubeProbability n d x ∉ U} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  exact @closed_cube_empirical_source d _ hd (humphreysAlcoveInput_direct hd) U hUopen hUmem

theorem closed_cube_continuity_set_concentration_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d) {B : Set (ClosedCubePoint d)} (hB : MeasurableSet B) (hfrontier : (closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) (frontier B) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      closedCubeAntichainLaw n d {x | ε ≤ |empiricalClosedSetFrequency n d B x -
        ((closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) B).toReal|} ≤
        ENNReal.ofReal (Real.exp (-α * (n : ℝ))) := by
  exact @closed_cube_continuity_set_concentration d _ hd (humphreysAlcoveInput_direct hd) B hB hfrontier ε hε

theorem closed_cube_continuity_set_in_probability_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d) {B : Set (ClosedCubePoint d)} (hB : MeasurableSet B) (hfrontier : (closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) (frontier B) = 0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => closedCubeAntichainLaw n d {x | ε ≤ |empiricalClosedSetFrequency n d B x -
      ((closedCubeLimitingProbability d : Measure (ClosedCubePoint d)) B).toReal|})
      atTop (𝓝 0) := by
  exact @closed_cube_continuity_set_in_probability d _ hd (humphreysAlcoveInput_direct hd) B hB hfrontier ε hε

theorem scaledAlcove_covers_direct (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (⋃ t : AlcoveTile d, scaledAlcove d ε t) = Set.univ := by
  exact @scaledAlcove_covers d _ (humphreysAlcoveInput_direct hd) ε hε

theorem scaledAlcove_disjoint_interiors_direct (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun t u : AlcoveTile d ↦ Disjoint (interior (scaledAlcove d ε t))
      (interior (scaledAlcove d ε u))) := by
  exact @scaledAlcove_disjoint_interiors d _ (humphreysAlcoveInput_direct hd) ε hε

theorem scaledAlcove_locallyFinite_direct (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    LocallyFinite (scaledAlcove d ε) := by
  exact @scaledAlcove_locallyFinite d _ (humphreysAlcoveInput_direct hd) ε hε

theorem completeCubeTile_count_isBigO_direct (hd : 2 ≤ d) (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d))) (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    (fun ε : ℝ ↦ (completeCubeTileCount b a L ε : ℝ) -
      L ^ (d - 1) / (ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal))
        =O[𝓝[>] (0 : ℝ)] (fun ε : ℝ ↦ ε ^ ((2 : ℝ) - (d : ℝ))) := by
  exact @completeCubeTile_count_isBigO d _ hd (humphreysAlcoveInput_direct hd) b a L hL

theorem weightedPartitionSeries_le_tileProduct_direct (hd : 2 ≤ d) (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 ≤ t) :
    (∑' n : ℕ, weightedPartition n sigma c * t ^ n / (n.factorial : ℝ)) ≤
      ∏' B : AlcoveTile d, tileGeneratingFunction d epsilon c
        (t * alcoveWeightSup sigma epsilon B) := by
  exact @weightedPartitionSeries_le_tileProduct d _ hd (humphreysAlcoveInput_direct hd) sigma epsilon c t hepsilon hepsilon1 hc ht

theorem weightedPartition_le_factorial_tileProduct_direct (hd : 2 ≤ d) (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 < t) :
    weightedPartition n sigma c ≤ (n.factorial : ℝ) / t ^ n *
      ∏' B : AlcoveTile d, tileGeneratingFunction d epsilon c
        (t * alcoveWeightSup sigma epsilon B) := by
  exact @weightedPartition_le_factorial_tileProduct d _ hd (humphreysAlcoveInput_direct hd) n sigma epsilon c t hepsilon hepsilon1 hc ht

theorem weighted_upper_limsup_source_direct (hd : 2 ≤ d) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Filter.limsup (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
      Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop ≤
      localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log
          (∫ u : FloorSpace (Fin d), (standardFloorDensity u * Real.exp (sigma u)) ^
            (((d : ℝ) - 1) / (d : ℝ))) := by
  exact @weighted_upper_limsup_source d _ hd (humphreysAlcoveInput_direct hd) sigma c hc

theorem matching_replication_source_direct (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eta lam : ℝ, eta ∈ Set.Ioo 0 (1 / 2 : ℝ) →
      lam ∈ Set.Ioo 0 (1 / 2 : ℝ) → ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ,
      ∃ B : Set (FloorHeightConfiguration (r + 1) d), ∃ boundary : SimplexBoundary d →ᵇ ℝ,
        MeasurableSet B ∧
        (∀ p ∈ B, (∀ j, p.1 j ∈ referenceSimplex d) ∧ p ∈ flooredAntichainEvent (r + 1) d) ∧
        (∀ p ∈ B, ∀ j, |p.2 j| ≤ C ∧ eta / C ≤ infDist (p.1 j) (frontier (referenceSimplex d))) ∧
        (∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
          (∀ j, E (p.1 j) = p.2 j) ∧ (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
          (∀ a b, E a - E b ≤ nativeFloorCost a b)) ∧
        (2 / (M : ℝ)) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
          pinnedVolume (referenceSimplex d) r ≤ (volume B).toReal ∧
        ∀ q : ℕ, 1 ≤ q → ∀ ε : ℝ, 0 < ε → ∀ tiles : Fin q → AlcoveTile d,
          Function.Injective tiles →
          MeasurableSet (replicationFamily (r + 1) q (q * (r + 1)) ε tiles B) ∧
          volume (replicationFamily (r + 1) q (q * (r + 1)) ε tiles B) < ⊤ ∧
          (∀ p ∈ replicationFamily (r + 1) q (q * (r + 1)) ε tiles B,
            p ∈ flooredAntichainEvent (q * (r + 1)) d ∧ (∀ j, |p.2 j| ≤ C * ε) ∧
            (∀ j, p.1 j ∈ ⋃ i, scaledAlcove d ε (tiles i))) ∧
          (volume (replicationFamily (r + 1) q (q * (r + 1)) ε tiles B)).toReal =
            ((Nat.factorial (q * (r + 1)) : ℝ) / (Nat.factorial (r + 1) : ℝ) ^ q) *
              (ε ^ (d * (r + 1)) * (volume B).toReal) ^ q := by
  exact @matching_replication_source d _ hd (humphreysAlcoveInput_direct hd)

theorem cube_lower_liminf_source_direct (hd : 2 ≤ d) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d))) (J : ℕ) (hJ : 0 < J) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j) (hdis : Pairwise (fun i j => Disjoint (interior (orthonormalFloorCube b (a i) (L i)))
      (interior (orthonormalFloorCube b (a j) (L j))))) :
    localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log (cubeLowerSum sigma b J a L) ≤
      Filter.liminf (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop := by
  exact @cube_lower_liminf_source d _ hd (humphreysAlcoveInput_direct hd) sigma c hc b J hJ a L hL hdis

theorem weighted_lower_liminf_source_direct (hd : 2 ≤ d) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log
        (∫ u : FloorSpace (Fin d), (standardFloorDensity u * Real.exp (sigma u)) ^
          (((d : ℝ) - 1) / (d : ℝ))) ≤
      Filter.liminf (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop := by
  exact @weighted_lower_liminf_source d _ hd (humphreysAlcoveInput_direct hd) sigma c hc

theorem avoidance_counting_exponential_source_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ beta betaPrime : ℝ, betaPrime = Real.exp (beta - 1 / ((d : ℝ) - 1)) ∧
      0 < betaPrime ∧ ∃ r : ℕ → ℝ,
        r =o[atTop] (fun n : ℕ => (n : ℝ)) ∧
        ∀ n : ℕ, (avoidanceClassCard n d : ℝ) =
          (n.factorial : ℝ) ^ ((d : ℝ) - 1 - 1 / ((d : ℝ) - 1)) *
            betaPrime ^ n * Real.exp (r n) := by
  exact @avoidance_counting_exponential_source d _ hd (humphreysAlcoveInput_direct hd)

theorem signed_avoidance_counting_exponential_source_direct {d : ℕ} [NeZero d] (hd : 2 ≤ d) (sign : Fin (d - 1) → Bool) :
    ∃ beta betaPrime : ℝ, betaPrime = Real.exp (beta - 1 / ((d : ℝ) - 1)) ∧
      0 < betaPrime ∧ ∃ r : ℕ → ℝ,
        r =o[atTop] (fun n : ℕ => (n : ℝ)) ∧
        ∀ n : ℕ, (Fintype.card (SignedAvoidancePermutation n (d - 1) sign) : ℝ) =
          (n.factorial : ℝ) ^ ((d : ℝ) - 1 - 1 / ((d : ℝ) - 1)) *
            betaPrime ^ n * Real.exp (r n) := by
  exact @signed_avoidance_counting_exponential_source d _ hd (humphreysAlcoveInput_direct hd) sign

theorem weakBruhat_counting_exponential_source_direct  :
    ∃ beta betaPrime : ℝ, betaPrime = Real.exp (beta - 1 / 2) ∧ 0 < betaPrime ∧
      ∃ r : ℕ → ℝ, r =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
        ∀ n : ℕ,
          (weakBruhatIntervalCount n : ℝ) = (n.factorial : ℝ) ^ ((3 : ℝ) / 2) *
            betaPrime ^ n * Real.exp (r n) ∧
          weakBruhatComparabilityProbability n = (n.factorial : ℝ) ^ (-(1 : ℝ) / 2) *
            betaPrime ^ n * Real.exp (r n) := by
  exact @weakBruhat_counting_exponential_source (humphreysAlcoveInput_direct (by norm_num : 2 ≤ 3))

/-- Exponential control of the manuscript's mean squared Gaussian height. -/
theorem meanSquaredHeight_exponential_tail_direct (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      (gaussianAntichainLaw n d).real {g | δ * (n : ℝ) ≤ totalSquaredHeight n g} ≤
        Real.exp (-α * (n : ℝ)) :=
  gaussian_height_exponential_tail hd (humphreysAlcoveInput_direct hd) hδ

end Antichain
