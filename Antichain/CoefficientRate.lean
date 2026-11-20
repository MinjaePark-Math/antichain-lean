import Antichain.LocalRate
import Antichain.TileCoefficients
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The actual logarithmic one-tile coefficient rate. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Filter
open scoped ENNReal Topology Pointwise

def normalizedTileLog (d : ℕ) (epsilon c : ℝ) (n : ℕ) : ℝ :=
  Real.log (tileCoefficient d epsilon c n) / (n : ℝ) +
    Real.log (n : ℝ) / ((d : ℝ) - 1)

def scaledSimplexVolume (d : ℕ) (epsilon : ℝ) : ℝ :=
  (floorVolume (epsilon • referenceSimplex d)).toReal

theorem scaledSimplexVolume_eq {d : ℕ} (hd : 2 ≤ d) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    scaledSimplexVolume d epsilon =
      epsilon ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal := by
  letI : NeZero d := ⟨by omega⟩
  unfold scaledSimplexVolume floorVolume
  rw [Measure.addHaar_smul_of_nonneg volume hepsilon.le, finrank_floorSpace]
  simp only [Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hepsilon.le _)]

theorem scaledSimplexVolume_pos {d : ℕ} (hd : 2 ≤ d) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < scaledSimplexVolume d epsilon := by
  rw [scaledSimplexVolume_eq hd hepsilon]
  exact mul_pos (pow_pos hepsilon _) (floorVolume_referenceSimplex_toReal_pos hd)

def tileRateOffset (d : ℕ) (epsilon : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (2 * Real.pi) + (d : ℝ) * Real.log epsilon +
    (d : ℝ) / ((d : ℝ) - 1) * Real.log (floorVolume (referenceSimplex d)).toReal

def tileLogCorrection (epsilon c : ℝ) (r : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) / 2 - Real.log epsilon - Real.log (1 - 2 * c) / 2) /
      ((r : ℝ) + 1) - (Real.log ((r : ℝ) + 1) / ((r : ℝ) + 1)) / 2

theorem tileCoefficient_log_succ {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (r : ℕ) :
    Real.log (tileCoefficient d epsilon c (r + 1)) =
      -(r : ℝ) / 2 * Real.log (2 * Real.pi) -
        (Real.log ((r : ℝ) + 1) + Real.log (1 - 2 * c)) / 2 +
        ((d : ℝ) * ((r : ℝ) + 1) - 1) * Real.log epsilon +
        Real.log (pinnedVolume (referenceSimplex d) r) := by
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hbase : 0 < 2 * Real.pi := by positivity
  have hheight : 0 < 1 - 2 * c := by linarith
  have hcoef := commonHeightGaussianCoefficient_pos (show 0 < r + 1 by omega) hc
  have hpin := pinnedVolume_referenceSimplex_pos hd r
  rw [tileCoefficient_succ,
    Real.log_mul (mul_pos hcoef (pow_pos hepsilon _)).ne' hpin.ne',
    Real.log_mul hcoef.ne' (pow_pos hepsilon _).ne', Real.log_pow,
    commonHeightGaussianCoefficient,
    Real.log_div (Real.rpow_pos_of_pos hbase _).ne'
      (Real.sqrt_pos.mpr (mul_pos (by simpa only [Nat.cast_add, Nat.cast_one] using hN) hheight)).ne',
    Real.log_rpow hbase, Real.log_sqrt (by positivity),
    Real.log_mul (by simpa only [Nat.cast_add, Nat.cast_one] using hN.ne') hheight.ne']
  have hdimpos : 0 < d * (r + 1) := Nat.mul_pos (by omega) (by omega)
  rw [Nat.cast_sub (Nat.succ_le_iff.mpr hdimpos)]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem normalizedTileLog_succ_eq {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (r : ℕ) :
    normalizedTileLog d epsilon c (r + 1) = localGammaSequence d r +
      tileRateOffset d epsilon + tileLogCorrection epsilon c r := by
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hV := floorVolume_referenceSimplex_toReal_pos hd
  unfold normalizedTileLog
  rw [tileCoefficient_log_succ hd hepsilon hc]
  unfold localGammaSequence tileRateOffset tileLogCorrection
  rw [Real.log_div hN.ne' (pow_pos hV _).ne', Real.log_pow]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem tileLogCorrection_tendsto (epsilon c : ℝ) :
    Tendsto (tileLogCorrection epsilon c) atTop (𝓝 0) := by
  have hN : Tendsto (fun r : ℕ => (r : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun r : ℕ =>
      (Real.log (2 * Real.pi) / 2 - Real.log epsilon - Real.log (1 - 2 * c) / 2) /
        ((r : ℝ) + 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hN
  have hlog : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + 1) / ((r : ℝ) + 1)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hN
  simpa only [tileLogCorrection, zero_div, sub_zero] using hconst.sub (hlog.div_const 2)

theorem tileRateOffset_eq_scaledVolume {d : ℕ} (hd : 2 ≤ d) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    tileRateOffset d epsilon = -(1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log (scaledSimplexVolume d epsilon) := by
  rw [scaledSimplexVolume_eq hd hepsilon,
    Real.log_mul (pow_pos hepsilon _).ne' (floorVolume_referenceSimplex_toReal_pos hd).ne',
    Real.log_pow, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  unfold tileRateOffset
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : (d : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hm]
  ring

/-- A convergent additive correction transports a genuine bounded real limsup. -/
theorem real_limsup_add_of_tendsto (u v : ℕ → ℝ) (a : ℝ)
    (hu : IsBoundedUnder (· ≤ ·) atTop u) (hl : IsBoundedUnder (· ≥ ·) atTop u)
    (hv : Tendsto v atTop (𝓝 a)) :
    Filter.limsup (fun n => u n + v n) atTop = Filter.limsup u atTop + a := by
  have hupper := limsup_add_le (f := atTop) (u := u) (v := v)
    hl hu hv.isCoboundedUnder_le hv.isBoundedUnder_le
  have hlower := le_limsup_add (f := atTop) (u := u) (v := v)
    hu hl.isCobounded_flip hv.isBoundedUnder_le hv.isBoundedUnder_ge
  rw [hv.limsup_eq] at hupper
  rw [hv.liminf_eq] at hlower
  exact le_antisymm hupper hlower

/-- The actual normalized coefficient sequence is bounded on both sides,
including its explicitly defined degree-zero term. -/
theorem normalizedTileLog_bounded {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    BddAbove (Set.range (normalizedTileLog d epsilon c)) ∧
      BddBelow (Set.range (normalizedTileLog d epsilon c)) := by
  obtain ⟨U, hU⟩ := localGammaSequence_bddAbove hd
  obtain ⟨L, hL⟩ := localGammaSequence_bddBelow hd
  obtain ⟨E, hE⟩ := (tileLogCorrection_tendsto epsilon c).bddAbove_range
  obtain ⟨F, hF⟩ := (tileLogCorrection_tendsto epsilon c).bddBelow_range
  constructor
  · refine ⟨max (normalizedTileLog d epsilon c 0) (U + tileRateOffset d epsilon + E), ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => exact le_max_left _ _
    | succ r =>
        rw [normalizedTileLog_succ_eq hd hepsilon hc]
        exact (add_le_add (add_le_add_right (hU (mem_range_self r)) _) (hE (mem_range_self r))).trans
          (le_max_right _ _)
  · refine ⟨min (normalizedTileLog d epsilon c 0) (L + tileRateOffset d epsilon + F), ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => exact min_le_left _ _
    | succ r =>
        rw [normalizedTileLog_succ_eq hd hepsilon hc]
        exact (min_le_right _ _).trans
          (add_le_add (add_le_add_right (hL (mem_range_self r)) _) (hF (mem_range_self r)))

theorem normalizedTileLog_limsup_eq_offset {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    Filter.limsup (normalizedTileLog d epsilon c) atTop =
      localGammaConstant d hd + tileRateOffset d epsilon := by
  have hcorr : Tendsto (fun r => tileRateOffset d epsilon + tileLogCorrection epsilon c r)
      atTop (𝓝 (tileRateOffset d epsilon)) := by
    simpa only [add_zero] using (tileLogCorrection_tendsto epsilon c).const_add (tileRateOffset d epsilon)
  calc
    Filter.limsup (normalizedTileLog d epsilon c) atTop =
        Filter.limsup (fun r => localGammaSequence d r +
          (tileRateOffset d epsilon + tileLogCorrection epsilon c r)) atTop := by
      rw [← Filter.limsup_nat_add (normalizedTileLog d epsilon c) 1]
      apply Filter.limsup_congr
      exact Filter.Eventually.of_forall (fun r => by
        rw [normalizedTileLog_succ_eq hd hepsilon hc]
        ring)
    _ = _ := real_limsup_add_of_tendsto _ _ _
      (localGammaSequence_isBoundedUnder_le hd) (localGammaSequence_isBoundedUnder_ge hd) hcorr

/-- The literal b_epsilon in Lemma 4.2, with actual induced Euclidean tile volume. -/
def tileCoefficientRate (d : ℕ) (hd : 2 ≤ d) (epsilon : ℝ) : ℝ :=
  localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
    (d : ℝ) / ((d : ℝ) - 1) * Real.log (scaledSimplexVolume d epsilon)

/-- Full Lemma 4.2 for the actual coefficients, including their exact limsup.
No coefficient-rate or local-volume asymptotic assumption remains. -/
theorem tileCoefficient_log_limsup {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    Filter.limsup (fun n : ℕ => Real.log (tileCoefficient d epsilon c n) / (n : ℝ) +
      Real.log (n : ℝ) / ((d : ℝ) - 1)) atTop = tileCoefficientRate d hd epsilon := by
  change Filter.limsup (normalizedTileLog d epsilon c) atTop = _
  rw [normalizedTileLog_limsup_eq_offset hd hepsilon hc, tileRateOffset_eq_scaledVolume hd hepsilon]
  unfold tileCoefficientRate
  ring

end Antichain
