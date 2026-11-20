import Antichain.AlcoveTiling
import Antichain.GaussianFloorLaw
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Gaussian-weight tile suprema and their actual summability and Riemann sums. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction Pointwise

variable {d : ℕ} [NeZero d]

/-- The exact source weight w=ψ_E exp σ. -/
def weightedFloorDensity (σ : FloorSpace (Fin d) →ᵇ ℝ) (u : FloorSpace (Fin d)) : ℝ :=
  standardFloorDensity u * Real.exp (σ u)

omit [NeZero d] in
theorem weightedFloorDensity_pos (σ : FloorSpace (Fin d) →ᵇ ℝ) (u : FloorSpace (Fin d)) :
    0 < weightedFloorDensity σ u :=
  mul_pos (radialGaussianDensity_pos (by norm_num : (0 : ℝ) < 1) u) (Real.exp_pos _)

omit [NeZero d] in
theorem weightedFloorDensity_continuous (σ : FloorSpace (Fin d) →ᵇ ℝ) :
    Continuous (weightedFloorDensity σ) :=
  (radialGaussianDensity_continuous 1).mul (Real.continuous_exp.comp σ.continuous)

/-- The actual maximum weight over a closed scaled tile. -/
def alcoveWeightSup (σ : FloorSpace (Fin d) →ᵇ ℝ) (ε : ℝ) (t : AlcoveTile d) : ℝ :=
  sSup (weightedFloorDensity σ '' scaledAlcove d ε t)

theorem alcoveWeightSup_attained (hd : 2 ≤ d) (σ : FloorSpace (Fin d) →ᵇ ℝ)
    (ε : ℝ) (t : AlcoveTile d) :
    ∃ v ∈ scaledAlcove d ε t, alcoveWeightSup σ ε t = weightedFloorDensity σ v ∧
      ∀ u ∈ scaledAlcove d ε t, weightedFloorDensity σ u ≤ alcoveWeightSup σ ε t := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_scaledAlcove d hd ε t).exists_isMaxOn
    (scaledAlcove_nonempty d hd ε t) (weightedFloorDensity_continuous σ).continuousOn
  have hg : IsGreatest (weightedFloorDensity σ '' scaledAlcove d ε t) (weightedFloorDensity σ v) := by
    refine ⟨Set.mem_image_of_mem _ hv, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hmax hu
  have heq : alcoveWeightSup σ ε t = weightedFloorDensity σ v := hg.csSup_eq
  exact ⟨v, hv, heq, fun u hu ↦ by rw [heq]; exact hmax hu⟩

theorem alcoveWeightSup_pos (hd : 2 ≤ d) (σ : FloorSpace (Fin d) →ᵇ ℝ)
    (ε : ℝ) (t : AlcoveTile d) : 0 < alcoveWeightSup σ ε t := by
  obtain ⟨v, _, hv, _⟩ := alcoveWeightSup_attained hd σ ε t
  rw [hv]
  exact weightedFloorDensity_pos σ v

/-- A norm-square estimate with the same constant used in the manuscript. -/
theorem norm_sq_lower_of_dist_le {E : Type*} [NormedAddCommGroup E]
    (u v : E) {D : ℝ} (hD : 0 ≤ D) (huv : dist u v ≤ D) :
    ‖u‖ ^ 2 / 2 - D ^ 2 ≤ ‖v‖ ^ 2 := by
  have hu : ‖u‖ ≤ ‖v‖ + D := by
    have ht := norm_add_le (u - v) v
    rw [sub_add_cancel, ← dist_eq_norm] at ht
    linarith
  have hsq : ‖u‖ ^ 2 ≤ (‖v‖ + D) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hD)).mpr hu
  nlinarith [sq_nonneg (‖v‖ - D)]

def gaussianTileMajorantConstant (σ : FloorSpace (Fin d) →ᵇ ℝ) (p : ℝ) : ℝ :=
  ((2 * Real.pi) ^ (-((d : ℝ) - 1) / 2)) ^ p *
    Real.exp (p * ‖σ‖ + p * (2 * (d : ℝ)) ^ 2 / 2)

omit [NeZero d] in
theorem gaussianTileMajorantConstant_pos (σ : FloorSpace (Fin d) →ᵇ ℝ) (p : ℝ) :
    0 < gaussianTileMajorantConstant σ p := by
  unfold gaussianTileMajorantConstant
  positivity

/-- The common Gaussian majorant for the actual source tile suprema. This
analytic result uses only the proved uniform diameter, not the cited tiling input. -/
theorem alcoveWeightSup_rpow_le_gaussian (hd : 2 ≤ d)
    (σ : FloorSpace (Fin d) →ᵇ ℝ) {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (t : AlcoveTile d) {u : FloorSpace (Fin d)} (hu : u ∈ scaledAlcove d ε t) :
    alcoveWeightSup σ ε t ^ p ≤ gaussianTileMajorantConstant σ p *
      Real.exp (-(p / 4) * ‖u‖ ^ 2) := by
  obtain ⟨v, hv, heq, _⟩ := alcoveWeightSup_attained hd σ ε t
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have huv : dist u v ≤ 2 * (d : ℝ) :=
    (scaledAlcove_dist_le d hd hε t hu hv).trans (by nlinarith)
  have hnorm := norm_sq_lower_of_dist_le u v hd0 huv
  have hσ := σ.apply_le_norm v
  rw [heq, weightedFloorDensity, standardFloorDensity_formula, Fintype.card_fin]
  let C : ℝ := (2 * Real.pi) ^ (-((d : ℝ) - 1) / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  change (C * Real.exp (-‖v‖ ^ 2 / 2) * Real.exp (σ v)) ^ p ≤ _
  rw [mul_assoc, ← Real.exp_add, Real.mul_rpow hC (Real.exp_nonneg _), ← Real.exp_mul]
  unfold gaussianTileMajorantConstant
  change C ^ p * Real.exp ((-‖v‖ ^ 2 / 2 + σ v) * p) ≤
    (C ^ p * Real.exp (p * ‖σ‖ + p * (2 * (d : ℝ)) ^ 2 / 2)) *
      Real.exp (-(p / 4) * ‖u‖ ^ 2)
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC p)
  apply Real.exp_le_exp.mpr
  nlinarith

omit [NeZero d] in
theorem integrable_gaussianTileMajorant (σ : FloorSpace (Fin d) →ᵇ ℝ) {p : ℝ} (hp : 0 < p) :
    Integrable (fun u : FloorSpace (Fin d) ↦ gaussianTileMajorantConstant σ p *
      Real.exp (-(p / 4) * ‖u‖ ^ 2)) :=
  (integrable_exp_neg_mul_norm_sq (V := FloorSpace (Fin d)) (by positivity : 0 < p / 4)).const_mul _

/-- The actual sum of tile-supremum powers is finite. Only the precise cited
geometric tiling input is external; the Gaussian majorant and the integration
over the countable a.e.-disjoint actual tiles are checked here. -/
theorem alcoveWeightSup_rpow_summable (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (σ : FloorSpace (Fin d) →ᵇ ℝ) {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Summable (fun t : AlcoveTile d ↦ alcoveWeightSup σ ε t ^ p) := by
  let M : FloorSpace (Fin d) → ℝ := fun u ↦ gaussianTileMajorantConstant σ p *
    Real.exp (-(p / 4) * ‖u‖ ^ 2)
  have hM : Integrable M := integrable_gaussianTileMajorant σ hp
  have hMnonneg : ∀ u, 0 ≤ M u := fun u ↦
    mul_nonneg (gaussianTileMajorantConstant_pos σ p).le (Real.exp_nonneg _)
  have hMfinite : (∫⁻ u, ENNReal.ofReal (M u)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hMnonneg)).mp hM.hasFiniteIntegral
  let V : ℝ≥0∞ := ENNReal.ofReal ε ^ (d - 1) * floorVolume (referenceSimplex d)
  have hVpos : 0 < V := ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.pow_pos (ENNReal.ofReal_pos.mpr hε) _, floorVolume_referenceSimplex_pos hd⟩
  have hterm (t : AlcoveTile d) : ENNReal.ofReal (alcoveWeightSup σ ε t ^ p) * V ≤
      ∫⁻ u in scaledAlcove d ε t, ENNReal.ofReal (M u) := by
    calc
      _ = ∫⁻ _u in scaledAlcove d ε t, ENNReal.ofReal (alcoveWeightSup σ ε t ^ p) := by
        rw [lintegral_const, Measure.restrict_apply_univ, volume_scaledAlcove d hd hε t]
      _ ≤ _ := setLIntegral_mono' (measurableSet_scaledAlcove d hd ε t)
        (fun u hu ↦ ENNReal.ofReal_le_ofReal (alcoveWeightSup_rpow_le_gaussian hd σ hp hε hε1 t hu))
  have hsum := ENNReal.tsum_le_tsum hterm
  rw [ENNReal.tsum_mul_right] at hsum
  have hUnion : (∑' t : AlcoveTile d, ∫⁻ u in scaledAlcove d ε t, ENNReal.ofReal (M u)) =
      ∫⁻ u, ENNReal.ofReal (M u) := by
    rw [← lintegral_iUnion₀ (fun t ↦ (measurableSet_scaledAlcove d hd ε t).nullMeasurableSet)
      (scaledAlcove_aedisjoint d H hε), scaledAlcove_covers d H hε, setLIntegral_univ]
  rw [hUnion] at hsum
  have hfinite : (∑' t : AlcoveTile d, ENNReal.ofReal (alcoveWeightSup σ ε t ^ p)) ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_left (ne_of_lt (hsum.trans_lt hMfinite)) hVpos.ne').ne
  have hs := ENNReal.summable_toReal hfinite
  simpa only [ENNReal.toReal_ofReal
    (Real.rpow_nonneg (alcoveWeightSup_pos hd σ ε _).le p)] using hs

/-- A measurable envelope using the proved boundary-assigned partition. -/
def alcoveSupStepENN (σ : FloorSpace (Fin d) →ᵇ ℝ) (p ε : ℝ) (u : FloorSpace (Fin d)) : ℝ≥0∞ :=
  ∑' t : AlcoveTile d, (alcoveCell d ε t).indicator
    (fun _ ↦ ENNReal.ofReal (alcoveWeightSup σ ε t ^ p)) u

def alcoveSupStep (σ : FloorSpace (Fin d) →ᵇ ℝ) (p ε : ℝ) (u : FloorSpace (Fin d)) : ℝ :=
  (alcoveSupStepENN σ p ε u).toReal

theorem measurable_alcoveSupStepENN (hd : 2 ≤ d) (σ : FloorSpace (Fin d) →ᵇ ℝ) (p ε : ℝ) :
    Measurable (alcoveSupStepENN σ p ε) :=
  Measurable.ennreal_tsum (fun t ↦ measurable_const.indicator (measurableSet_alcoveCell d hd ε t))

theorem measurable_alcoveSupStep (hd : 2 ≤ d) (σ : FloorSpace (Fin d) →ᵇ ℝ) (p ε : ℝ) :
    Measurable (alcoveSupStep σ p ε) := (measurable_alcoveSupStepENN hd σ p ε).ennreal_toReal

theorem alcoveSupStepENN_eq_on_cell (σ : FloorSpace (Fin d) →ᵇ ℝ) (p ε : ℝ)
    (t : AlcoveTile d) {u : FloorSpace (Fin d)} (hu : u ∈ alcoveCell d ε t) :
    alcoveSupStepENN σ p ε u = ENNReal.ofReal (alcoveWeightSup σ ε t ^ p) := by
  unfold alcoveSupStepENN
  rw [tsum_eq_single t]
  · exact Set.indicator_of_mem hu _
  · intro s hst
    apply Set.indicator_of_notMem
    intro hs
    exact Set.disjoint_left.mp (alcoveCell_pairwise_disjoint d ε hst) hs hu

theorem alcoveSupStep_eq_on_cell (hd : 2 ≤ d) (σ : FloorSpace (Fin d) →ᵇ ℝ) (p ε : ℝ)
    (t : AlcoveTile d) {u : FloorSpace (Fin d)} (hu : u ∈ alcoveCell d ε t) :
    alcoveSupStep σ p ε u = alcoveWeightSup σ ε t ^ p := by
  rw [alcoveSupStep, alcoveSupStepENN_eq_on_cell σ p ε t hu,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (alcoveWeightSup_pos hd σ ε t).le p)]

theorem alcoveSupStep_nonneg (σ : FloorSpace (Fin d) →ᵇ ℝ) (p ε : ℝ) (u : FloorSpace (Fin d)) :
    0 ≤ alcoveSupStep σ p ε u := ENNReal.toReal_nonneg

theorem alcoveSupStep_le_majorant (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (σ : FloorSpace (Fin d) →ᵇ ℝ) {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (u : FloorSpace (Fin d)) :
    alcoveSupStep σ p ε u ≤ gaussianTileMajorantConstant σ p * Real.exp (-(p / 4) * ‖u‖ ^ 2) := by
  have hu : u ∈ ⋃ t : AlcoveTile d, alcoveCell d ε t := by
    rw [alcoveCell_covers d H hε]
    exact Set.mem_univ u
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hu
  rw [alcoveSupStep_eq_on_cell hd σ p ε t ht]
  exact alcoveWeightSup_rpow_le_gaussian hd σ hp hε hε1 t (alcoveCell_subset d ε t ht)

theorem integrable_alcoveSupStep (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (σ : FloorSpace (Fin d) →ᵇ ℝ) {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (alcoveSupStep σ p ε) := by
  apply (integrable_gaussianTileMajorant σ hp).mono'
    (measurable_alcoveSupStep hd σ p ε).aestronglyMeasurable
  exact Eventually.of_forall (fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (alcoveSupStep_nonneg σ p ε u)]
    exact alcoveSupStep_le_majorant hd H σ hp hε hε1 u)

/-- The boundary-assigned step integral is exactly the scaled tile volume times
the actual countable sum of maximum-weight powers. -/
theorem integral_alcoveSupStep (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (σ : FloorSpace (Fin d) →ᵇ ℝ) (p : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ u : FloorSpace (Fin d), alcoveSupStep σ p ε u) =
      ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal *
        ∑' t : AlcoveTile d, alcoveWeightSup σ ε t ^ p := by
  have hstep : (fun u : FloorSpace (Fin d) ↦ ENNReal.ofReal (alcoveSupStep σ p ε u)) =
      alcoveSupStepENN σ p ε := by
    funext u
    have hu : u ∈ ⋃ t : AlcoveTile d, alcoveCell d ε t := by
      rw [alcoveCell_covers d H hε]
      exact Set.mem_univ u
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hu
    rw [alcoveSupStep_eq_on_cell hd σ p ε t ht, alcoveSupStepENN_eq_on_cell σ p ε t ht]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (alcoveSupStep_nonneg σ p ε))
    (measurable_alcoveSupStep hd σ p ε).aestronglyMeasurable, hstep]
  unfold alcoveSupStepENN
  rw [lintegral_tsum (fun t ↦ (measurable_const.indicator (measurableSet_alcoveCell d hd ε t)).aemeasurable)]
  have hterm (t : AlcoveTile d) :
      (∫⁻ u : FloorSpace (Fin d), (alcoveCell d ε t).indicator
        (fun _ ↦ ENNReal.ofReal (alcoveWeightSup σ ε t ^ p)) u) =
      ENNReal.ofReal (alcoveWeightSup σ ε t ^ p) *
        (ENNReal.ofReal ε ^ (d - 1) * floorVolume (referenceSimplex d)) := by
    rw [lintegral_indicator (measurableSet_alcoveCell d hd ε t), lintegral_const,
      Measure.restrict_apply_univ, volume_alcoveCell d hd H hε t]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right, ENNReal.toReal_mul, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (alcoveWeightSup_pos hd σ ε _).le p)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le, mul_comm]

/-- Continuity and the proved vanishing tile diameter give pointwise convergence
for every point, including points lying on tile boundaries at arbitrarily many
scales. The canonical cells assign those boundary points to actual tiles. -/
theorem tendsto_alcoveSupStep (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (σ : FloorSpace (Fin d) →ᵇ ℝ) {p : ℝ} (hp : 0 < p) (u : FloorSpace (Fin d)) :
    Tendsto (fun ε : ℝ ↦ alcoveSupStep σ p ε u) (𝓝[>] (0 : ℝ))
      (𝓝 (weightedFloorDensity σ u ^ p)) := by
  have hf : Continuous (fun v : FloorSpace (Fin d) ↦ weightedFloorDensity σ v ^ p) :=
    (Real.continuous_rpow_const hp.le).comp (weightedFloorDensity_continuous σ)
  have hD : (0 : ℝ) < 2 * (d : ℝ) := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp hf.continuousAt δ hδ
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < η / (2 * (d : ℝ)) :=
    (eventually_lt_nhds (div_pos hη hD)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmall
  have hεpos : 0 < ε := hε
  have hu : u ∈ ⋃ t : AlcoveTile d, alcoveCell d ε t := by
    rw [alcoveCell_covers d H hεpos]
    exact Set.mem_univ u
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hu
  obtain ⟨v, hv, heq, _⟩ := alcoveWeightSup_attained hd σ ε t
  rw [alcoveSupStep_eq_on_cell hd σ p ε t ht, heq]
  apply hcont
  rw [dist_comm]
  exact (scaledAlcove_dist_le d hd hεpos t (alcoveCell_subset d ε t ht) hv).trans_lt
    ((lt_div_iff₀ hD).mp hsmall)

/-- The source Gaussian tile Riemann approximation, derived by dominated
convergence using the actual weight, actual tiles, and actual Euclidean volume. -/
theorem tendsto_scaled_alcoveWeightSup_sum (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (σ : FloorSpace (Fin d) →ᵇ ℝ) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ ↦ ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal *
      ∑' t : AlcoveTile d, alcoveWeightSup σ ε t ^ p) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ u : FloorSpace (Fin d), weightedFloorDensity σ u ^ p)) := by
  let M : FloorSpace (Fin d) → ℝ := fun u ↦ gaussianTileMajorantConstant σ p *
    Real.exp (-(p / 4) * ‖u‖ ^ 2)
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (alcoveSupStep σ p ε) :=
    Eventually.of_forall (fun ε ↦ (measurable_alcoveSupStep hd σ p ε).aestronglyMeasurable)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ u : FloorSpace (Fin d),
      ‖alcoveSupStep σ p ε u‖ ≤ M u := by
    have hε1 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 :=
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hε1] with ε hε hε1
    exact Eventually.of_forall (fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (alcoveSupStep_nonneg σ p ε u)]
      exact alcoveSupStep_le_majorant hd H σ hp hε hε1 u)
  have hlim := tendsto_integral_filter_of_dominated_convergence M hmeas hbound
    (integrable_gaussianTileMajorant σ hp)
    (Eventually.of_forall (tendsto_alcoveSupStep hd H σ hp))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact integral_alcoveSupStep hd H σ p hε

end Antichain
