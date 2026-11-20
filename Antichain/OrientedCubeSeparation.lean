import Antichain.CubeSeparation

noncomputable section

namespace Antichain.OrientedCube

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction ENNReal

variable {d J : ℕ} [NeZero d]

omit [NeZero d] in
theorem shrunkenCubes_pairwise_disjoint
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j => Disjoint (interior (orthonormalFloorCube (b i) (a i) (L i)))
      (interior (orthonormalFloorCube (b j) (a j) (L j)))))
    {t : ℝ} (ht : 0 < t) :
    Pairwise (fun i j =>
      Disjoint (orthonormalFloorCube (b i) (shrunkenCubeOrigin (a i) (L i) t) ((1 - t) * L i))
        (orthonormalFloorCube (b j) (shrunkenCubeOrigin (a j) (L j) t) ((1 - t) * L j))) := by
  intro i j hij
  exact (hdis hij).mono (shrunkenCube_subset_interior (b i) (a i) (hL i) ht)
    (shrunkenCube_subset_interior (b j) (a j) (hL j) ht)

omit [NeZero d] in
theorem shrunkenCubes_positive_separation
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j => Disjoint (interior (orthonormalFloorCube (b i) (a i) (L i)))
      (interior (orthonormalFloorCube (b j) (a j) (L j)))))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ∃ sep : ℝ, 0 < sep ∧ ∀ i j, i ≠ j →
      ∀ x ∈ orthonormalFloorCube (b i) (shrunkenCubeOrigin (a i) (L i) t) ((1 - t) * L i),
      ∀ y ∈ orthonormalFloorCube (b j) (shrunkenCubeOrigin (a j) (L j) t) ((1 - t) * L j), sep ≤ dist x y := by
  exact finite_compact_disjoint_separation J _
    (fun j => isCompact_orthonormalFloorCube (b j) _ _)
    (fun j => orthonormalFloorCube_nonempty (b j) _ (mul_pos (sub_pos.mpr ht.2) (hL j)).le)
    (shrunkenCubes_pairwise_disjoint b a L hL hdis ht.1)


omit [NeZero d] in
/-- Shrinking touching cubes loses at most the explicit volume factor;
their true infimum weights can only increase. No regularity of a minimizer
or unproved convergence of optimized weights is assumed. -/
theorem shrunkenCube_lower_weight_sum
    (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    {p t : ℝ} (hp : 0 ≤ p) (ht : t ∈ Set.Ioo 0 1) :
    (1 - t) ^ (d - 1) *
      (∑ j, L j ^ (d - 1) * floorCubeWeightInf sigma (b j) (a j) (L j) ^ p) ≤
    ∑ j, ((1 - t) * L j) ^ (d - 1) *
      floorCubeWeightInf sigma (b j) (shrunkenCubeOrigin (a j) (L j) t) ((1 - t) * L j) ^ p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hL' : 0 ≤ (1 - t) * L j := (mul_pos (sub_pos.mpr ht.2) (hL j)).le
  have hweight := floorCubeWeightInf_mono_subcube sigma (b j) (a j)
    (shrunkenCubeOrigin (a j) (L j) t) (hL j).le hL'
    ((shrunkenCube_subset_interior (b j) (a j) (hL j) ht.1).trans interior_subset)
  have hpow := Real.rpow_le_rpow (floorCubeWeightInf_pos sigma (b j) (a j) (hL j).le).le hweight hp
  rw [mul_pow]
  calc
    _ = ((1 - t) ^ (d - 1) * L j ^ (d - 1)) *
        floorCubeWeightInf sigma (b j) (a j) (L j) ^ p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (pow_nonneg (sub_pos.mpr ht.2).le _) (pow_nonneg (hL j).le _))


end Antichain.OrientedCube
