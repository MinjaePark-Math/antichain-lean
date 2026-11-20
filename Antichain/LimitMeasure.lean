import Antichain.SurfaceClosure
import Antichain.GaussianSample
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FunProp

/-! The actual projected/rescaled Gaussian limiting law and its support. -/

namespace Antichain

open Set Filter MeasureTheory ProbabilityTheory Finset
open scoped Topology ENNReal NNReal

section ContinuousPushforward

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- A continuous image of a measure positive on every open set has support
exactly the closure of the actual range of the map. -/
theorem support_map_eq_closure_range (μ : Measure X) [μ.IsOpenPosMeasure]
    (f : X → Y) (hf : Continuous f) : (μ.map f).support = closure (range f) := by
  have hmeas : Measurable f := hf.measurable
  have hrange : range f ⊆ (μ.map f).support := by
    rintro y ⟨x, rfl⟩
    rw [Measure.support_eq_forall_isOpen]
    intro U hx hU
    rw [Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage hf).measure_pos μ ⟨x, hx⟩
  apply subset_antisymm
  · apply Measure.support_subset_of_isClosed isClosed_closure
    apply (mem_ae_map_iff hmeas.aemeasurable isClosed_closure.measurableSet).mpr
    exact Filter.Eventually.of_forall (fun x => subset_closure (mem_range_self x))
  · exact closure_minimal hrange Measure.isClosed_support

end ContinuousPushforward

instance standardGaussian_isOpenPosMeasure :
    (gaussianReal (0 : ℝ) (1 : ℝ≥0)).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero).isOpenPosMeasure

/-- Independent standard normal coordinates, before orthogonal projection. -/
noncomputable def standardGaussianProduct (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

instance standardGaussianProduct_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (standardGaussianProduct ι) := by
  unfold standardGaussianProduct
  infer_instance

instance standardGaussianProduct_isOpenPosMeasure (ι : Type*) [Fintype ι] :
    (standardGaussianProduct ι).IsOpenPosMeasure := by
  unfold standardGaussianProduct
  infer_instance

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The exact inverse-normal surface formula used to state the paper's results. -/
def normalQuantileSurface (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, x i ∈ Set.Ioo 0 1) ∧ ∑ i, normalQuantile (x i) = 0}

theorem normalCDF_surface_eq_quantileSurface :
    coordinateImageSurface (ι := ι) normalCDF = normalQuantileSurface ι := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨fun i => normalCDF_mem_Ioo (g i), by simp only [normalQuantile_normalCDF, hg]⟩
  · rintro ⟨hx, hsum⟩
    refine ⟨fun i => normalQuantile (x i), hsum, ?_⟩
    funext i
    exact (normalCDF_normalQuantile (x i) (hx i)).symm

/-- The scale in the paper's definition of `F*`. -/
noncomputable def floorGaussianScale (ι : Type*) [Fintype ι] : ℝ :=
  Real.sqrt ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1))

/-- Exactly `F*_i = sqrt(d/(d-1)) (Y_i - average Y)` from (2.1). -/
noncomputable def scaledCenteredCoordinates (y : ι → ℝ) : ι → ℝ :=
  fun i => floorGaussianScale ι * (y i - (∑ j, y j) / (Fintype.card ι : ℝ))

/-- Applying the actual standard-normal CDF to `F*`, coordinate by coordinate. -/
noncomputable def limitingCubeMap (y : ι → ℝ) : ι → ℝ :=
  fun i => normalCDF (scaledCenteredCoordinates y i)

/-- The limiting measure `μ*`, defined by its actual Gaussian construction. -/
noncomputable def limitingAntichainMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  (standardGaussianProduct ι).map limitingCubeMap

theorem scaledCenteredCoordinates_sum_zero (y : ι → ℝ) :
    ∑ i, scaledCenteredCoordinates y i = 0 := by
  simp only [scaledCenteredCoordinates, ← Finset.mul_sum, sum_sub_mean_eq_zero, mul_zero]

omit [Nonempty ι] in
theorem limitingCubeMap_continuous : Continuous (limitingCubeMap (ι := ι)) := by
  apply continuous_pi
  intro i
  apply normalCDF_continuous.comp
  unfold scaledCenteredCoordinates
  fun_prop

omit [Nonempty ι] in
theorem floorGaussianScale_pos (hd : 2 ≤ Fintype.card ι) : 0 < floorGaussianScale ι := by
  have hcard : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  apply Real.sqrt_pos.mpr
  exact div_pos (by linarith) (by linarith)

theorem limitingCubeMap_range (hd : 2 ≤ Fintype.card ι) :
    range (limitingCubeMap (ι := ι)) = coordinateImageSurface normalCDF := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨scaledCenteredCoordinates y, scaledCenteredCoordinates_sum_zero y, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    let y : ι → ℝ := fun i => g i / floorGaussianScale ι
    have hy : ∑ i, y i = 0 := by simp [y, ← Finset.sum_div, hg]
    refine ⟨y, ?_⟩
    funext i
    have hs := (floorGaussianScale_pos hd).ne'
    simp only [limitingCubeMap, scaledCenteredCoordinates, hy, zero_div, sub_zero]
    congr 1
    dsimp [y]
    field_simp

instance limitingAntichainMeasure_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (limitingAntichainMeasure ι) := by
  unfold limitingAntichainMeasure
  exact Measure.isProbabilityMeasure_map limitingCubeMap_continuous.measurable.aemeasurable

/-- The support identity in Lemma 2.2, for the actual projected Gaussian law. -/
theorem limitingAntichainMeasure_support (hd : 2 ≤ Fintype.card ι) :
    (limitingAntichainMeasure ι).support = closure (coordinateImageSurface normalCDF) := by
  unfold limitingAntichainMeasure
  rw [support_map_eq_closure_range _ _ limitingCubeMap_continuous, limitingCubeMap_range hd]

/-- All conclusions of Lemma 2.2, including the actual measure support,
the boundary closure formula, and a strictly comparable interior witness. -/
theorem limitingAntichainMeasure_support_spec (hd : 2 ≤ Fintype.card ι) :
    (limitingAntichainMeasure ι).support = candidateClosedSurface normalCDF ∧
    closure (coordinateImageSurface (ι := ι) normalCDF) = candidateClosedSurface normalCDF ∧
    (∀ x : ι → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      x ∉ closure (coordinateImageSurface normalCDF) →
      ∃ y ∈ coordinateImageSurface normalCDF, StrictBelow x y ∨ StrictBelow y x) := by
  exact ⟨(limitingAntichainMeasure_support hd).trans normalCDF_surface_closure,
    normalCDF_surface_closure, normalCDF_cube_outside_closure_exists_comparable⟩

/-- The complete printed support/closure formula with the inverse-normal surface. -/
theorem limitingAntichainMeasure_support_quantile_formula (hd : 2 ≤ Fintype.card ι) :
    (limitingAntichainMeasure ι).support = closure (normalQuantileSurface ι) ∧
    closure (normalQuantileSurface ι) = normalQuantileSurface ι ∪
      {x : ι → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∃ i, x i = 0) ∧ (∃ i, x i = 1)} := by
  rw [← normalCDF_surface_eq_quantileSurface]
  exact ⟨limitingAntichainMeasure_support hd, normalCDF_surface_closure⟩

end Antichain
