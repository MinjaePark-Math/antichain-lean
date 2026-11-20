import Antichain.PinnedVolumeBounds
import Antichain.OneTileGaussian
import Antichain.SeriesGrowth

/-! Actual one-tile coefficients, with their positivity and a coarse volume bound.
The sharp local entropy rate is a separate theorem and is not assumed here. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal Pointwise

/-- Coarse exponential upper bound, used independently of the sharp local rate. -/
theorem pinnedMass_referenceSimplex_coarse_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    pinnedMass (referenceSimplex d) r ≤
      (floorVolume (referenceSimplex d)) ^ (r + 1) * ENNReal.ofReal (4 * Real.sqrt (d : ℝ)) ^ r := by
  let floors : Set (Fin (r + 1) → FloorSpace (Fin d)) :=
    univ.pi (fun _ => referenceSimplex d)
  let heights : Set (Fin r → ℝ) :=
    univ.pi (fun _ => Icc (-(2 * Real.sqrt (d : ℝ))) (2 * Real.sqrt (d : ℝ)))
  have hsub : pinnedAntichainSet (referenceSimplex d) r ⊆ floors ×ˢ heights := by
    intro x hx
    constructor
    · exact fun j _ => hx.1 j
    · intro k _
      exact abs_le.mp (pinned_height_bounds_referenceSimplex hd hx k)
  calc
    pinnedMass (referenceSimplex d) r ≤ volume (floors ×ˢ heights) := measure_mono hsub
    _ = _ := by
      change ((volume : Measure (Fin (r + 1) → FloorSpace (Fin d))).prod
        (volume : Measure (Fin r → ℝ))) (floors ×ˢ heights) = _
      rw [Measure.prod_prod]
      simp only [floors, heights, volume_pi_pi, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Real.volume_Icc]
      have hw : 2 * Real.sqrt (d : ℝ) - -(2 * Real.sqrt (d : ℝ)) =
          4 * Real.sqrt (d : ℝ) := by ring
      simp only [hw, floorVolume]

theorem pinnedVolume_referenceSimplex_coarse_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    pinnedVolume (referenceSimplex d) r ≤
      (floorVolume (referenceSimplex d)).toReal ^ (r + 1) * (4 * Real.sqrt (d : ℝ)) ^ r := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (floorVolume_referenceSimplex_lt_top hd).ne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (pinnedMass_referenceSimplex_coarse_bound hd r)
  simpa [pinnedVolume, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.sqrt (d : ℝ))] using h

/-- Equation (4.4), including the explicitly prescribed degree-zero term. -/
def tileCoefficient (d : ℕ) (epsilon c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else commonHeightGaussianCoefficient n c *
    epsilon ^ (d * n - 1) * pinnedVolume (referenceSimplex d) (n - 1)

@[simp] theorem tileCoefficient_zero (d : ℕ) (epsilon c : ℝ) :
    tileCoefficient d epsilon c 0 = 1 := by simp [tileCoefficient]

theorem tileCoefficient_succ (d : ℕ) (epsilon c : ℝ) (r : ℕ) :
    tileCoefficient d epsilon c (r + 1) =
      commonHeightGaussianCoefficient (r + 1) c *
        epsilon ^ (d * (r + 1) - 1) * pinnedVolume (referenceSimplex d) r := by
  simp [tileCoefficient]

theorem commonHeightGaussianCoefficient_pos {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : c < 1 / 2) :
    0 < commonHeightGaussianCoefficient n c := by
  unfold commonHeightGaussianCoefficient
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply div_pos (Real.rpow_pos_of_pos (by positivity) _)
  exact Real.sqrt_pos.mpr (mul_pos hnR (by linarith))

theorem tileCoefficient_pos {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (n : ℕ) :
    0 < tileCoefficient d epsilon c n := by
  cases n with
  | zero => simp
  | succ r =>
      rw [tileCoefficient_succ]
      exact mul_pos (mul_pos (commonHeightGaussianCoefficient_pos (by omega) hc)
        (pow_pos hepsilon _)) (pinnedVolume_referenceSimplex_pos hd r)

end Antichain
