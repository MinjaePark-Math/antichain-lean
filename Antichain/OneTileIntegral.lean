import Antichain.HeightGaussianBound
import Antichain.TileCoefficients
import Antichain.TileSymmetries

/-! Integrating the actual one-tile height-fiber estimate over floor positions. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal Pointwise

variable {ι : Type*} [Fintype ι]

/-- The literal nonnegative one-tile integral, in actual floor/height coordinates. -/
def oneTileIntegral (B : Set (FloorSpace ι)) (w : FloorSpace ι → ℝ) (c : ℝ) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ f in univ.pi (fun _ : Fin (r + 1) => B),
    (∏ j, ENNReal.ofReal (w (f j))) *
      ∫⁻ h in antichainHeightFiber f, normalizedHeightGaussianWeight (r + 1) c h

theorem oneTileIntegral_one (B : Set (FloorSpace ι)) (c : ℝ) (r : ℕ) :
    oneTileIntegral B (fun _ => 1) c r =
      ∫⁻ f in univ.pi (fun _ : Fin (r + 1) => B),
        ∫⁻ h in antichainHeightFiber f, normalizedHeightGaussianWeight (r + 1) c h := by
  simp [oneTileIntegral]

/-- The first inequality of Lemma 4.1, bounding every floor weight by its tile supremum. -/
theorem oneTileIntegral_le_weightBound {B : Set (FloorSpace ι)} (hB : MeasurableSet B)
    (w : FloorSpace ι → ℝ) (M c : ℝ) (r : ℕ)
    (hw : ∀ f ∈ B, w f ≤ M) :
    oneTileIntegral B w c r ≤ ENNReal.ofReal M ^ (r + 1) *
      oneTileIntegral B (fun _ => 1) c r := by
  rw [oneTileIntegral_one]
  unfold oneTileIntegral
  calc
    _ ≤ ∫⁻ f in univ.pi (fun _ : Fin (r + 1) => B), ENNReal.ofReal M ^ (r + 1) *
        ∫⁻ h in antichainHeightFiber f, normalizedHeightGaussianWeight (r + 1) c h := by
      apply setLIntegral_mono' (MeasurableSet.univ_pi (fun _ => hB))
      intro f hf
      apply mul_le_mul_right'
      calc
        (∏ j, ENNReal.ofReal (w (f j))) ≤ ∏ _j : Fin (r + 1), ENNReal.ofReal M := by
          exact Finset.prod_le_prod' (fun j _ => ENNReal.ofReal_le_ofReal (hw _ (hf j (mem_univ j))))
        _ = _ := by simp
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- The second inequality of Lemma 4.1, with the actual pinned volume S_(r+1)(B). -/
theorem oneTileIntegral_one_le_pinnedMass {B : Set (FloorSpace ι)} (hB : MeasurableSet B)
    (c : ℝ) (hc : c < 1 / 2) (r : ℕ) :
    oneTileIntegral B (fun _ => 1) c r ≤
      ENNReal.ofReal (commonHeightGaussianCoefficient (r + 1) c) * pinnedMass B r := by
  rw [oneTileIntegral_one, pinnedMass_eq_lintegral_pinnedHeightFiber hB r]
  calc
    _ ≤ ∫⁻ f in univ.pi (fun _ : Fin (r + 1) => B),
        ENNReal.ofReal (commonHeightGaussianCoefficient (r + 1) c) *
          (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) :=
      lintegral_mono (fun f => antichainHeightFiber_gaussian_lintegral_le f c hc)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem oneTileIntegral_le {B : Set (FloorSpace ι)} (hB : MeasurableSet B)
    (w : FloorSpace ι → ℝ) (M c : ℝ) (hc : c < 1 / 2) (r : ℕ)
    (hw : ∀ f ∈ B, w f ≤ M) :
    oneTileIntegral B w c r ≤ ENNReal.ofReal M ^ (r + 1) *
      (ENNReal.ofReal (commonHeightGaussianCoefficient (r + 1) c) * pinnedMass B r) :=
  (oneTileIntegral_le_weightBound hB w M c r hw).trans
    (mul_le_mul_left' (oneTileIntegral_one_le_pinnedMass hB c hc r) _)

end Antichain
