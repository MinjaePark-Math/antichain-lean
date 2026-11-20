import Antichain.HeightCoordinates
import Antichain.OneTileGaussian
import Mathlib.Tactic.FunProp

/-!
The actual normalized Gaussian height integral over an antichain fiber is
bounded by the paper's common-height coefficient times its pinned fiber volume.
The coordinate disintegration and common-height integral bound are proved inputs.
-/

noncomputable section

namespace Antichain

open MeasureTheory Set
open scoped ENNReal

/-- The normalized Gaussian height weight occurring in equation (4.1). -/
def normalizedHeightGaussianWeight (n : ℕ) (c : ℝ) (h : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
    Real.exp (-((1 / 2 : ℝ) - c) * ∑ j, h j ^ 2))

theorem normalizedHeightGaussianWeight_measurable (n : ℕ) (c : ℝ) :
    Measurable (normalizedHeightGaussianWeight n c) := by
  unfold normalizedHeightGaussianWeight
  fun_prop

/-- The uniform common-height bound, for the literal pinned-coordinate map. -/
theorem normalizedHeightGaussianWeight_common_integral_le (r : ℕ) (c : ℝ)
    (hc : c < 1 / 2) (delta : Fin r → ℝ) :
    (∫⁻ s : ℝ, normalizedHeightGaussianWeight (r + 1) c
      (heightCoordinates r (s, delta))) ≤
        ENNReal.ofReal (commonHeightGaussianCoefficient (r + 1) c) := by
  simpa only [normalizedHeightGaussianWeight, heightCoordinates_eq_shift_cons_zero,
    Fintype.card_fin] using
    normalized_common_height_lintegral_le
      (Fin.cons (0 : ℝ) delta : Fin (r + 1) → ℝ) c hc

/-- The complete fixed-floor estimate used by Lemma 4.1. No boundedness,
Jacobian, or fiber-integrability assumption is imposed on the floor positions. -/
theorem antichainHeightFiber_gaussian_lintegral_le
    {ι : Type*} [Fintype ι] {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (c : ℝ) (hc : c < 1 / 2) :
    (∫⁻ h in antichainHeightFiber f, normalizedHeightGaussianWeight (r + 1) c h) ≤
      ENNReal.ofReal (commonHeightGaussianCoefficient (r + 1) c) *
        (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) := by
  rw [antichainHeightFiber_lintegral f _ (normalizedHeightGaussianWeight_measurable _ _)]
  calc
    (∫⁻ delta in pinnedHeightFiber f, ∫⁻ s : ℝ,
        normalizedHeightGaussianWeight (r + 1) c (heightCoordinates r (s, delta))) ≤
        ∫⁻ _delta in pinnedHeightFiber f,
          ENNReal.ofReal (commonHeightGaussianCoefficient (r + 1) c) :=
      lintegral_mono (fun delta => normalizedHeightGaussianWeight_common_integral_le r c hc delta)
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ]

end Antichain
