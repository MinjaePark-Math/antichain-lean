import Antichain.ConfigurationContraction
import Antichain.OneTileModel

/-! The actual full-dimensional family obtained by releasing the first height
over [-1,1]. Its volume is exactly twice the pinned volume. -/

noncomputable section

namespace Antichain

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {d : ℕ} [NeZero d]

def heightTubeFiber {r : ℕ} (f : Fin (r + 1) → FloorSpace (Fin d)) : Set (Fin (r + 1) → ℝ) :=
  antichainHeightFiber f ∩ {h | h 0 ∈ Icc (-1 : ℝ) 1}

omit [NeZero d] in
theorem heightTubeFiber_measure {r : ℕ} (f : Fin (r + 1) → FloorSpace (Fin d)) :
    volume (heightTubeFiber f) = 2 * (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) := by
  let J : Set (Fin (r + 1) → ℝ) := {h | h 0 ∈ Icc (-1 : ℝ) 1}
  have hJ : MeasurableSet J := measurableSet_Icc.preimage (measurable_pi_apply 0)
  let W : (Fin (r + 1) → ℝ) → ℝ≥0∞ := J.indicator (fun _ => 1)
  have hW : Measurable W := measurable_const.indicator hJ
  have h := antichainHeightFiber_lintegral f W hW
  have hshift (delta : Fin r → ℝ) :
      (fun s : ℝ => W (heightCoordinates r (s, delta))) =
        (Icc (-1 : ℝ) 1).indicator (fun _ => 1) := by
    funext s
    simp [W, J, heightCoordinates, Set.indicator_apply]
  simp_rw [hshift] at h
  have hmass : (∫⁻ s : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) s) = 2 := by
    rw [lintegral_indicator measurableSet_Icc]
    norm_num [Real.volume_Icc]
  rw [hmass] at h
  dsimp [W] at h
  rw [lintegral_indicator hJ] at h
  simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ,
    Measure.restrict_apply hJ, heightTubeFiber, J, inter_comm] using h

/-- The source starting family: actual antichains in B with their first height in [-1,1]. -/
def baseTube (B : Set (FloorSpace (Fin d))) (r : ℕ) : Set (FloorHeightConfiguration (r + 1) d) :=
  flooredTileEvent B (r + 1) ∩ {p | p.2 0 ∈ Icc (-1 : ℝ) 1}

omit [NeZero d] in
theorem measurableSet_baseTube {B : Set (FloorSpace (Fin d))}
    (hB : MeasurableSet B) (r : ℕ) : MeasurableSet (baseTube B r) :=
  (flooredTileEvent_measurable hB (r + 1)).inter
    (measurableSet_Icc.preimage ((measurable_pi_apply 0).comp measurable_snd))

omit [NeZero d] in
theorem baseTube_fiber (B : Set (FloorSpace (Fin d))) (r : ℕ)
    (f : Fin (r + 1) → FloorSpace (Fin d)) (h : Fin (r + 1) → ℝ) :
    (f, h) ∈ baseTube B r ↔ (∀ j, f j ∈ B) ∧ h ∈ heightTubeFiber f := by
  simp only [baseTube, Set.mem_inter_iff, Set.mem_setOf_eq, heightTubeFiber]
  rw [flooredTileEvent_fiber]
  tauto

/-- Exact full-dimensional volume 2*S_N, with the free-height measure normalization. -/
theorem baseTube_volume {B : Set (FloorSpace (Fin d))} (hB : MeasurableSet B) (r : ℕ) :
    volume (baseTube B r) = 2 * pinnedMass B r := by
  change ((volume : Measure (Fin (r + 1) → FloorSpace (Fin d))).prod
    (volume : Measure (Fin (r + 1) → ℝ))) (baseTube B r) = _
  rw [Measure.prod_apply (measurableSet_baseTube hB r),
    pinnedMass_eq_lintegral_pinnedHeightFiber hB r,
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    ← lintegral_indicator (MeasurableSet.univ_pi (fun _ : Fin (r + 1) => hB))]
  apply lintegral_congr
  intro f
  by_cases hf : ∀ j, f j ∈ B
  · have hfmem : f ∈ univ.pi (fun _ : Fin (r + 1) => B) := by simpa using hf
    rw [Set.indicator_of_mem hfmem]
    have heq : Prod.mk f ⁻¹' baseTube B r = heightTubeFiber f := by
      ext h
      simp [baseTube_fiber, hf]
    rw [heq, heightTubeFiber_measure]
  · have hfmem : f ∉ univ.pi (fun _ : Fin (r + 1) => B) := by simpa using hf
    rw [Set.indicator_of_notMem hfmem]
    have heq : Prod.mk f ⁻¹' baseTube B r = ∅ := by
      ext h
      simp only [Set.mem_preimage, baseTube_fiber, hf, false_and, notMem_empty]
    rw [heq, measure_empty]

/-- The actual initial contracted full-dimensional family in Lemma 5.2. -/
def contractedTube (d : ℕ) [NeZero d] (eta : ℝ) (r : ℕ) :
    Set (FloorHeightConfiguration (r + 1) d) :=
  jointConfigurationContraction (r + 1) (referenceSimplexInteriorPoint d) eta ''
    baseTube (referenceSimplex d) r

theorem measurableSet_contractedTube (d : ℕ) [NeZero d] (eta : ℝ) (heta : eta < 1)
    (r : ℕ) : MeasurableSet (contractedTube d eta r) :=
  measurableSet_jointConfigurationContraction_image _ eta heta
    (measurableSet_baseTube (measurableSet_referenceSimplex d) r)

/-- Both actual Jacobian factors and the initial translation length are retained. -/
theorem contractedTube_volume (d : ℕ) [NeZero d] (eta : ℝ) (heta : eta < 1) (r : ℕ) :
    volume (contractedTube d eta r) =
      2 * ENNReal.ofReal (1 - eta) ^ (d * (r + 1)) * pinnedMass (referenceSimplex d) r := by
  rw [contractedTube, jointConfigurationContraction_volume _ _ eta heta
    (measurableSet_baseTube (measurableSet_referenceSimplex d) r),
    baseTube_volume (measurableSet_referenceSimplex d) r]
  ac_rfl

end Antichain
