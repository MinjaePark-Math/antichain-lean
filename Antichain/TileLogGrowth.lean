import Antichain.TileSeriesLocal
import Antichain.TileGaussianSums
import Antichain.CountableRate

/-! Actual summable logarithmic bounds and upper rates for all floor tiles. -/

noncomputable section

namespace Antichain

open Filter
open scoped Topology BoundedContinuousFunction

theorem tileGeneratingFunction_log_nonneg {d : ℕ} (hd : 2 ≤ d)
    {epsilon c t : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (ht : 0 ≤ t) :
    0 ≤ Real.log (tileGeneratingFunction d epsilon c t) :=
  Real.log_nonneg (tileGeneratingFunction_one_le hd hepsilon hc ht)

/-- The source's all-argument logarithmic majorant, including the near-zero
regime needed when infinitely many tile weights tend to zero. -/
theorem tileSeries_log_uniform_bound {d : ℕ} (hd : 2 ≤ d)
    {epsilon c : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Real.log (tileGeneratingFunction d epsilon c t) ≤
        C * t ^ (((d : ℝ) - 1) / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
  have hp : 0 < p := by dsimp [p]; exact div_pos (by linarith) (by linarith)
  have hp1 : p ≤ 1 := by dsimp [p]; apply (div_le_one (by linarith)).mpr; linarith
  obtain ⟨A, hA, hbound⟩ := tileSeries_uniform_bound hd hepsilon hc (by norm_num : (0 : ℝ) < 1)
  let K : ℝ := (d : ℝ) / ((d : ℝ) - 1) *
    Real.exp (p * (tileCoefficientRate d hd epsilon + 1) - 1 / (d : ℝ))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.exp_nonneg _)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hV1 : 0 ≤ tileGeneratingFunction d epsilon c 1 - 1 :=
    sub_nonneg.mpr (tileGeneratingFunction_one_le hd hepsilon hc (by norm_num))
  let C : ℝ := (tileGeneratingFunction d epsilon c 1 - 1) + Real.log A + K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht
  change Real.log (tileGeneratingFunction d epsilon c t) ≤ C * t ^ p
  by_cases ht1 : t ≤ 1
  · have hs := tileGeneratingFunction_small_argument hd hepsilon hc ht.le ht1
    have htmax : t ≤ t ^ p := Real.self_le_rpow_of_le_one ht.le ht1 hp1
    have hCC : tileGeneratingFunction d epsilon c 1 - 1 ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ t * (tileGeneratingFunction d epsilon c 1 - 1) := hs
      _ ≤ t ^ p * (tileGeneratingFunction d epsilon c 1 - 1) :=
        mul_le_mul_of_nonneg_right htmax hV1
      _ ≤ C * t ^ p := by nlinarith [Real.rpow_nonneg ht.le p]
  · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    have hpos : 0 < tileGeneratingFunction d epsilon c t :=
      lt_of_lt_of_le zero_lt_one (tileGeneratingFunction_one_le hd hepsilon hc ht.le)
    have hlarge := (Real.log_le_log hpos (hbound t ht.le).2)
    rw [Real.log_mul (by linarith : A ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlarge
    have htmax : 1 ≤ t ^ p := Real.one_le_rpow ht1' hp.le
    have hCC : Real.log A + K ≤ C := by dsimp [C]; linarith
    change Real.log (tileGeneratingFunction d epsilon c t) ≤ Real.log A + K * t ^ p at hlarge
    calc
      _ ≤ Real.log A + K * t ^ p := hlarge
      _ ≤ (Real.log A + K) * t ^ p := by nlinarith
      _ ≤ C * t ^ p := mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg ht.le p)

theorem tileSeries_normalized_log_uniform_bound {d : ℕ} (hd : 2 ≤ d)
    {epsilon c : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      0 ≤ t ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
          Real.log (tileGeneratingFunction d epsilon c t) ∧
        t ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
          Real.log (tileGeneratingFunction d epsilon c t) ≤ C := by
  obtain ⟨C, hC, hb⟩ := tileSeries_log_uniform_bound hd hepsilon hc
  refine ⟨C, hC, ?_⟩
  intro t ht
  refine ⟨mul_nonneg (Real.rpow_nonneg ht.le _) (tileGeneratingFunction_log_nonneg hd hepsilon hc ht.le), ?_⟩
  have h := mul_le_mul_of_nonneg_left (hb t ht) (Real.rpow_nonneg ht.le
    (-(((d : ℝ) - 1) / (d : ℝ))))
  have heq : t ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
      (C * t ^ (((d : ℝ) - 1) / (d : ℝ))) = C := by
    rw [mul_left_comm, ← Real.rpow_add ht]
    simp
  exact h.trans_eq heq

theorem weighted_rpow_normalization {t w : ℝ} (ht : 0 < t) (hw : 0 < w)
    (p a : ℝ) :
    t ^ (-p) * a = w ^ p * ((t * w) ^ (-p) * a) := by
  rw [Real.mul_rpow ht.le hw.le]
  have hcancel : w ^ p * w ^ (-p) = 1 := by
    rw [← Real.rpow_add hw]
    simp
  calc
    _ = t ^ (-p) * 1 * a := by ring
    _ = _ := by rw [← hcancel]; ring

/-- A shared summable majorant constant and the precise individual weighted
upper rate, with every series input supplied by the actual coefficient model. -/
theorem tileSeries_weighted_log_rates {d : ℕ} (hd : 2 ≤ d)
    {epsilon c : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
    let K : ℝ := (d : ℝ) / ((d : ℝ) - 1) *
      Real.exp (p * tileCoefficientRate d hd epsilon - 1 / (d : ℝ))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 0 < w →
      (∀ t : ℝ, 0 < t →
        0 ≤ t ^ (-p) * Real.log (tileGeneratingFunction d epsilon c (t * w)) ∧
          t ^ (-p) * Real.log (tileGeneratingFunction d epsilon c (t * w)) ≤ C * w ^ p) ∧
      (∀ e : ℝ, 0 < e → ∀ᶠ t : ℝ in atTop,
        t ^ (-p) * Real.log (tileGeneratingFunction d epsilon c (t * w)) ≤ K * w ^ p + e) := by
  intro p K
  obtain ⟨C, hC, hb⟩ := tileSeries_normalized_log_uniform_bound hd hepsilon hc
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (fun t : ℝ => t ^ (-p) * Real.log (tileGeneratingFunction d epsilon c t)) :=
    isBoundedUnder_of_eventually_le ((eventually_gt_atTop (0 : ℝ)).mono
      (fun t ht => (hb t ht).2))
  have hrate : ∀ e : ℝ, 0 < e → ∀ᶠ t : ℝ in atTop,
      t ^ (-p) * Real.log (tileGeneratingFunction d epsilon c t) ≤ K + e := by
    intro e he
    exact (eventually_lt_add_pos_of_limsup_le hbounded
      (tileSeries_log_limsup hd hepsilon hc) he).mono (fun _ h => h.le)
  refine ⟨C, hC, ?_⟩
  intro w hw
  have hwp : 0 < w ^ p := Real.rpow_pos_of_pos hw p
  constructor
  · intro t ht
    rw [weighted_rpow_normalization ht hw p]
    exact ⟨mul_nonneg hwp.le (hb (t * w) (mul_pos ht hw)).1,
      (mul_le_mul_of_nonneg_left (hb (t * w) (mul_pos ht hw)).2 hwp.le).trans_eq
        (mul_comm _ _)⟩
  · intro e he
    have hscale : Tendsto (fun t : ℝ => t * w) atTop atTop :=
      Tendsto.atTop_mul_const hw tendsto_id
    have hev := hscale.eventually (hrate (e / w ^ p) (div_pos he hwp))
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    rw [weighted_rpow_normalization ht0 hw p]
    have hm := mul_le_mul_of_nonneg_left ht hwp.le
    calc
      _ ≤ w ^ p * (K + e / w ^ p) := hm
      _ = _ := by field_simp

theorem tileSeries_weighted_logs_summable {ι : Type*} {d : ℕ} (hd : 2 ≤ d)
    {epsilon c : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hws : Summable (fun i => w i ^ (((d : ℝ) - 1) / (d : ℝ))))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun i => Real.log (tileGeneratingFunction d epsilon c (t * w i))) := by
  obtain ⟨C, hC, hb⟩ := tileSeries_log_uniform_bound hd hepsilon hc
  apply Summable.of_nonneg_of_le
    (fun i => tileGeneratingFunction_log_nonneg hd hepsilon hc (mul_pos ht (hw i)).le)
    (fun i => ?_) (hws.mul_left (C * t ^ (((d : ℝ) - 1) / (d : ℝ))))
  have h := hb (t * w i) (mul_pos ht (hw i))
  rw [Real.mul_rpow ht.le (hw i).le] at h
  exact h.trans_eq (mul_assoc _ _ _).symm

/-- The countably many actual one-tile logarithmic upper rates can be summed.
The proof keeps a finite head and bounds the remaining tail uniformly. -/
theorem tileSeries_countable_log_upper_rate {ι : Type*} {d : ℕ} (hd : 2 ≤ d)
    {epsilon c : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hws : Summable (fun i => w i ^ (((d : ℝ) - 1) / (d : ℝ))))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop,
      t ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
          (∑' i, Real.log (tileGeneratingFunction d epsilon c (t * w i))) ≤
        ((d : ℝ) / ((d : ℝ) - 1) * Real.exp ((((d : ℝ) - 1) / (d : ℝ)) *
          tileCoefficientRate d hd epsilon - 1 / (d : ℝ))) *
          (∑' i, w i ^ (((d : ℝ) - 1) / (d : ℝ))) + δ := by
  let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
  let K : ℝ := (d : ℝ) / ((d : ℝ) - 1) *
    Real.exp (p * tileCoefficientRate d hd epsilon - 1 / (d : ℝ))
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.exp_nonneg _)
  obtain ⟨C, hC, hweighted⟩ := tileSeries_weighted_log_rates hd hepsilon hc
  let G : ℝ → ι → ℝ := fun t i => (max t 1) ^ (-p) *
    Real.log (tileGeneratingFunction d epsilon c (max t 1 * w i))
  have hpos (t : ℝ) : 0 < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hnonneg : ∀ t i, 0 ≤ G t i := fun t i => (hweighted (w i) (hw i)).1 _ (hpos t) |>.1
  have hmajor : ∀ t i, G t i ≤ C * w i ^ p :=
    fun t i => (hweighted (w i) (hw i)).1 _ (hpos t) |>.2
  have hrate : ∀ i, ∀ e : ℝ, 0 < e → ∀ᶠ t : ℝ in atTop, G t i ≤ K * w i ^ p + e := by
    intro i e he
    filter_upwards [(hweighted (w i) (hw i)).2 e he, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    simpa only [G, max_eq_left ht1] using ht
  have hev := eventually_tsum_le_of_summable_majorant G (fun i => w i ^ p) hws
    (fun i => Real.rpow_nonneg (hw i).le p) hC hK hnonneg hmajor hrate hδ
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  simpa only [G, max_eq_left ht1, tsum_mul_left] using ht

variable {d : ℕ} [NeZero d]

/-- The full Gaussian summation step in Lemma 4.5. Its sole external input is
the explicitly cited geometric alcove package. -/
theorem alcoveTile_log_upper_rate (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop,
      t ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
        (∑' B : AlcoveTile d, Real.log
          (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B))) ≤
      ((d : ℝ) / ((d : ℝ) - 1) * Real.exp ((((d : ℝ) - 1) / (d : ℝ)) *
        tileCoefficientRate d hd epsilon - 1 / (d : ℝ))) *
        (∑' B : AlcoveTile d, alcoveWeightSup sigma epsilon B ^
          (((d : ℝ) - 1) / (d : ℝ))) + δ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < ((d : ℝ) - 1) / (d : ℝ) := div_pos (by linarith) (by linarith)
  exact tileSeries_countable_log_upper_rate hd hepsilon hc _
    (fun B => alcoveWeightSup_pos hd sigma epsilon B)
    (alcoveWeightSup_rpow_summable hd H sigma hp hepsilon hepsilon1) hδ

end Antichain
