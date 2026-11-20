import Antichain.Geometry
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual Euclidean zero-sum floor and its induced Euclidean volume.
The submodule carries its inherited inner product, rather than a measure from
an arbitrary choice of the first d-1 coordinates. -/

noncomputable section

namespace Antichain

open Finset Module MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- Sum of coordinates on the ambient Euclidean space. -/
def coordinateSum : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

/-- The paper's floor hyperplane as a native Euclidean subspace. -/
abbrev FloorSpace (ι : Type*) [Fintype ι] :=
  LinearMap.ker (coordinateSum (ι := ι))

@[simp] theorem mem_floorSpace (x : EuclideanSpace ℝ ι) :
    x ∈ FloorSpace ι ↔ ∑ i, x i = 0 := Iff.rfl

/-- Native floor points and the finite-coordinate floor used by the height lemmas
are exactly the same vectors. -/
def floorCoordinatesEquiv : FloorSpace ι ≃ ZeroSumFloor ι where
  toFun x := ⟨fun i => x.val i, x.property⟩
  invFun x := ⟨WithLp.toLp 2 x.val, x.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

@[simp] theorem floorCoordinatesEquiv_apply (x : FloorSpace ι) (i : ι) :
    (floorCoordinatesEquiv x).val i = x.val i := rfl

theorem coordinateSum_surjective [Nonempty ι] :
    Function.Surjective (coordinateSum (ι := ι)) := by
  classical
  intro t
  let j : ι := Classical.arbitrary ι
  refine ⟨WithLp.toLp 2 (Pi.single j t), ?_⟩
  simp [coordinateSum]

/-- The induced Euclidean dimension is d-1. -/
theorem finrank_floorSpace [Nonempty ι] :
    finrank ℝ (FloorSpace ι) = Fintype.card ι - 1 := by
  have h := (coordinateSum (ι := ι)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr coordinateSum_surjective] at h
  simp only [finrank_top, finrank_self, finrank_euclideanSpace] at h
  change 1 + finrank ℝ (FloorSpace ι) = Fintype.card ι at h
  omega

/-- The canonical Euclidean volume on the floor. -/
def floorVolume : Measure (FloorSpace ι) := volume

/-- This normalization is independent of the orthonormal coordinates chosen. -/
theorem floorVolume_orthonormalBasis (b : OrthonormalBasis (Fin (finrank ℝ (FloorSpace ι)))
    ℝ (FloorSpace ι)) :
    floorVolume (parallelepiped b) = 1 := b.volume_parallelepiped

/-- Every orthogonal symmetry of the floor preserves the actual floor measure. -/
theorem floorVolume_preserving_isometry (e : FloorSpace ι ≃ₗᵢ[ℝ] FloorSpace ι) :
    MeasurePreserving e floorVolume floorVolume := e.measurePreserving

/-- Subtract the coordinate average: the explicit orthogonal projection formula. -/
def centeredFloor [Nonempty ι] (x : EuclideanSpace ℝ ι) : FloorSpace ι :=
  ⟨WithLp.toLp 2 (fun i => x i - (∑ j, x j) / (Fintype.card ι : ℝ)),
    sum_sub_mean_eq_zero (fun i => x i)⟩

theorem centeredFloor_eq_starProjection [Nonempty ι] (x : EuclideanSpace ℝ ι) :
    (centeredFloor x).val = (FloorSpace ι).starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (centeredFloor x).property
  intro w hw
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [mul_comm (w _) ((x - (centeredFloor x).val) _)]
  change (∑ i, (x - (centeredFloor x).val) i * w i) = 0
  have heq (i : ι) : (x - (centeredFloor x).val) i =
      (∑ j, x j) / (Fintype.card ι : ℝ) := by
    simp [centeredFloor]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change (∑ j, x j) / (Fintype.card ι : ℝ) * (coordinateSum w) = 0
  rw [hw, mul_zero]

/-- Coordinate permutations, restricted to the actual zero-sum Euclidean floor. -/
def floorPermutation (e : ι ≃ ι) : FloorSpace ι ≃ₗᵢ[ℝ] FloorSpace ι where
  toFun x := ⟨WithLp.toLp 2 (fun i => x.val (e i)), by
    change ∑ i, x.val (e i) = 0
    rw [e.sum_comp]
    exact x.property⟩
  invFun x := ⟨WithLp.toLp 2 (fun i => x.val (e.symm i)), by
    change ∑ i, x.val (e.symm i) = 0
    rw [e.symm.sum_comp]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    change x.val (e (e.symm i)) = x.val i
    rw [e.apply_symm_apply]
  right_inv x := by
    apply Subtype.ext
    ext i
    change x.val (e.symm (e i)) = x.val i
    rw [e.symm_apply_apply]
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' a x := by apply Subtype.ext; rfl
  norm_map' x := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm).norm_map' x.val

@[simp] theorem floorPermutation_apply (e : ι ≃ ι) (x : FloorSpace ι) (i : ι) :
    (floorPermutation e x).val i = x.val (e i) := rfl

theorem floorPermutation_measurePreserving (e : ι ≃ ι) :
    MeasurePreserving (floorPermutation e) floorVolume floorVolume :=
  (floorPermutation e).measurePreserving

end Antichain
