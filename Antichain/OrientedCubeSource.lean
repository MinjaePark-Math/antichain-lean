import Antichain.OrientedCubeLower
import Antichain.UpperBound
import Antichain.DirectAlcoveInput

/-! Source Lemma 5.4 for a finite family of cubes with independent rotations.
The lower estimate uses matching, replication and size selection. The real
liminf wrapper obtains boundedness from the independently proved upper bound,
without appealing to the weighted-limit theorem. -/

noncomputable section

namespace Antichain.OrientedCube

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

variable {d J : ℕ} [NeZero d]

omit [NeZero d] in
/-- The sum in the endpoint is literally the paper's cube volumes multiplied
by the powers of the true floor-weight infima, in each cube's own frame. -/
theorem cubeLowerSum_eq_volume (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 ≤ L j) :
    cubeLowerSum sigma b a L =
      ∑ j, ((volume : Measure (FloorSpace (Fin d)))
        (orthonormalFloorCube (b j) (a j) (L j))).toReal *
          floorCubeWeightInf sigma (b j) (a j) (L j) ^
            (((d : ℝ) - 1) / (d : ℝ)) := by
  unfold cubeLowerSum
  apply Finset.sum_congr rfl
  intro j _
  rw [volume_orthonormalFloorCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal (hL j)]

theorem cube_lower_liminf_source (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (hJ : 0 < J) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j =>
      Disjoint (interior (orthonormalFloorCube (b i) (a i) (L i)))
        (interior (orthonormalFloorCube (b j) (a j) (L j))))) :
    localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log (cubeLowerSum sigma b a L) ≤
      Filter.liminf (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop := by
  change _ ≤ Filter.liminf (fun n : ℕ => normalizedPartitionLog n sigma c) atTop
  have hupper := isBoundedUnder_of_eventually_le
    (normalizedPartitionLog_upper hd H sigma c hc (by norm_num : (0 : ℝ) < 1))
  have hlower := isBoundedUnder_of_eventually_ge
    (normalizedPartitionLog_cubes_lower hd H sigma c hc b hJ a L hL hdis
      (by norm_num : (0 : ℝ) < 1))
  apply (le_liminf_iff' hupper.isCobounded_flip hlower).mpr
  intro y hy
  have he := normalizedPartitionLog_cubes_lower hd H sigma c hc b hJ a L hL hdis
    (sub_pos.mpr hy)
  filter_upwards [he] with n hn
  linarith

/-- Full independently rotated-cube source endpoint, without external
geometric or asymptotic assumptions. -/
theorem cube_lower_liminf_source_direct (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (hJ : 0 < J) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j =>
      Disjoint (interior (orthonormalFloorCube (b i) (a i) (L i)))
        (interior (orthonormalFloorCube (b j) (a j) (L j))))) :
    localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log (cubeLowerSum sigma b a L) ≤
      Filter.liminf (fun n : ℕ => Real.log (weightedPartition n sigma c) / (n : ℝ) +
        Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop :=
  cube_lower_liminf_source hd (humphreysAlcoveInput_direct hd) sigma c hc b hJ a L hL hdis

end Antichain.OrientedCube
