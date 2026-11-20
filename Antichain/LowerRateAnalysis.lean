import Antichain.LocalRate
import Antichain.PartitionInterpolation
import Antichain.SeriesGrowth

/-! Scalar normalization and vanishing local errors in the weighted lower bound. -/

noncomputable section

namespace Antichain

open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

def matchingStirlingError (M : ℝ) (r : ℕ) : ℝ :=
  Real.log (M / 2) / ((r : ℝ) + 1) +
    Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1) - Real.log ((r : ℝ) + 1) + 1

theorem matchingStirlingError_tendsto (M : ℝ) :
    Tendsto (matchingStirlingError M) atTop (𝓝 0) := by
  have hN : Tendsto (fun r : ℕ => (r : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun r : ℕ => Real.log (M / 2) / ((r : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hStirling := tendsto_log_factorial_remainder.comp (tendsto_add_atTop_nat 1)
  have h := hconst.add hStirling
  have h' : Tendsto (fun r : ℕ => Real.log (M / 2) / ((r : ℝ) + 1) +
      (Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1) - Real.log ((r : ℝ) + 1) + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_zero] using h
  convert h' using 1
  funext r
  unfold matchingStirlingError
  ring

theorem matching_volume_log_lower {d : ℕ} (hd : 2 ≤ d) (r : ℕ)
    {M eta lam V : ℝ} (hM : 0 < M) (heta : eta < 1) (hlam : lam < 1)
    (hV : (2 / M) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
      pinnedVolume (referenceSimplex d) r ≤ V) :
    localGammaSequence d r - (d : ℝ) / ((d : ℝ) - 1) * Real.log ((r : ℝ) + 1) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log (floorVolume (referenceSimplex d)).toReal + 1 +
      (d : ℝ) * Real.log (1 - eta) + Real.log (1 - lam) - matchingStirlingError M r ≤
      Real.log (V / ((r + 1).factorial : ℝ)) / ((r : ℝ) + 1) := by
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hpin := pinnedVolume_referenceSimplex_pos hd r
  have hf : (0 : ℝ) < (r + 1).factorial := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hvol := floorVolume_referenceSimplex_toReal_pos hd
  have hEta : 0 < 1 - eta := sub_pos.mpr heta
  have hLam : 0 < 1 - lam := sub_pos.mpr hlam
  have hbase : 0 < (2 / M) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
      pinnedVolume (referenceSimplex d) r := by positivity
  have hVpos : 0 < V := lt_of_lt_of_le hbase hV
  have hlog := Real.log_le_log hbase hV
  rw [Real.log_mul (mul_pos (mul_pos (div_pos (by norm_num) hM) (pow_pos hEta _))
      (pow_pos hLam _)).ne' hpin.ne',
    Real.log_mul (mul_pos (div_pos (by norm_num) hM) (pow_pos hEta _)).ne' (pow_pos hLam _).ne',
    Real.log_mul (div_pos (by norm_num) hM).ne' (pow_pos hEta _).ne',
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hM.ne', Real.log_pow, Real.log_pow] at hlog
  have h := div_le_div_of_nonneg_right hlog hN.le
  rw [Real.log_div hVpos.ne' hf.ne']
  unfold localGammaSequence matchingStirlingError
  rw [Real.log_div hN.ne' (pow_pos hvol _).ne', Real.log_pow,
    Real.log_div hM.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h ⊢
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) - 1 ≠ 0 := by linarith
  have h' := sub_le_sub_right h (Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1))
  convert h' using 1
  · field_simp
    ring
  · field_simp

/-- Normalize the literal finite-scale replication bound, retaining its exact
factorial, Gaussian, label and spatial-scale constants. -/
theorem replicated_weight_log_lower {d m q N : ℕ} (hd : 2 ≤ d)
    (hm : 0 < m) (hq : 0 < q) (hN : N = q * m)
    {epsilon V kappa Z : ℝ} (hepsilon : 0 < epsilon) (hV : 0 < V)
    (hLower : (N.factorial : ℝ) * Real.exp (-(N : ℝ) * kappa) *
      (2 * Real.pi) ^ (-(N : ℝ) / 2) * (V / (m.factorial : ℝ)) ^ q *
        epsilon ^ (d * N) ≤ Z) :
    (Real.log (N.factorial : ℝ) / (N : ℝ) - Real.log (N : ℝ) + 1) +
      Real.log (V / (m.factorial : ℝ)) / (m : ℝ) - 1 -
      (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log ((N : ℝ) * epsilon ^ (d - 1)) - kappa ≤
      Real.log Z / (N : ℝ) + Real.log (N : ℝ) / ((d : ℝ) - 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (hN ▸ Nat.mul_pos hq hm)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfN : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hfm : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hpi : 0 < 2 * Real.pi := by positivity
  have hbase : 0 < (N.factorial : ℝ) * Real.exp (-(N : ℝ) * kappa) *
      (2 * Real.pi) ^ (-(N : ℝ) / 2) * (V / (m.factorial : ℝ)) ^ q *
        epsilon ^ (d * N) := by positivity
  have hlog := Real.log_le_log hbase hLower
  rw [Real.log_mul (by positivity) (pow_pos hepsilon _).ne',
    Real.log_mul (by positivity) (pow_pos (div_pos hV hfm) _).ne',
    Real.log_mul (mul_pos hfN (Real.exp_pos _)).ne' (Real.rpow_pos_of_pos hpi _).ne',
    Real.log_mul hfN.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_rpow hpi, Real.log_pow, Real.log_pow] at hlog
  have hdiv := add_le_add_right (div_le_div_of_nonneg_right hlog hNR.le)
    (Real.log (N : ℝ) / ((d : ℝ) - 1))
  apply le_trans _ hdiv
  apply le_of_eq
  rw [Real.log_mul hNR.ne' (pow_pos hepsilon _).ne', Real.log_pow]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) - 1 ≠ 0 := by linarith
  simp only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, Nat.cast_mul]
  have hNreal : (N : ℝ) = (q : ℝ) * (m : ℝ) := by exact_mod_cast hN
  rw [hNreal]
  field_simp
  ring

/-- Recover the actual finite gamma limsup from the matched-family estimates,
while making the local Stirling error small at the same index. -/
theorem lower_rate_from_local_gamma {d : ℕ} (hd : 2 ≤ d)
    (A : ℕ → ℝ) (M C : ℝ)
    (hA : ∀ r : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
      localGammaSequence d r + C - matchingStirlingError M r - e ≤ A n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, localGammaConstant d hd + C - δ ≤ A n := by
  have he : 0 < δ / 3 := by positivity
  have hgamma : ∃ᶠ r : ℕ in atTop,
      localGammaConstant d hd - δ / 3 < localGammaSequence d r :=
    frequently_lt_of_lt_limsup
      (localGammaSequence_isBoundedUnder_ge hd).isCobounded_flip
      (sub_lt_self (localGammaConstant d hd) he)
  have herr : ∀ᶠ r : ℕ in atTop, matchingStirlingError M r < δ / 3 :=
    (matchingStirlingError_tendsto M).eventually (Iio_mem_nhds he)
  obtain ⟨r, hr, herror⟩ := (hgamma.and_eventually herr).exists
  filter_upwards [hA r (δ / 3) he] with n hn
  linarith

/-- Let the two contraction parameters decrease to zero after all preceding
sample-size and local-configuration limits. -/
theorem lower_rate_remove_contractions (A : ℕ → ℝ) (d C : ℝ)
    (hA : ∀ eta lam : ℝ, eta ∈ Set.Ioo 0 (1 / 2 : ℝ) →
      lam ∈ Set.Ioo 0 (1 / 2 : ℝ) → ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
        C + d * Real.log (1 - eta) + Real.log (1 - lam) - e ≤ A n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, C - δ ≤ A n := by
  have hlog : Tendsto (fun eta : ℝ => Real.log (1 - eta)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 - (0 : ℝ)) ≠ 0)).comp
      (continuousAt_const.sub continuousAt_id)
    have h' : Tendsto (fun eta : ℝ => Real.log (1 - eta)) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [Function.comp_apply, sub_zero, Real.log_one] using h.tendsto
    exact h'.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun eta : ℝ => d * Real.log (1 - eta) + Real.log (1 - eta))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (hlog.const_mul d).add hlog
  have hev : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧
      -δ / 2 < d * Real.log (1 - eta) + Real.log (1 - eta) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds,
      hlim.eventually (Ioi_mem_nhds (show -δ / 2 < (0 : ℝ) by linarith))]
      with eta h0 h1 hs
    exact ⟨⟨h0, h1⟩, hs⟩
  obtain ⟨eta, heta, hsmall⟩ := hev.exists
  filter_upwards [hA eta eta heta heta (δ / 2) (half_pos hδ)] with n hn
  linarith

theorem replicated_partition_rate_of_scaling {d m : ℕ} [NeZero d]
    (hd : 2 ≤ d) (hm : 0 < m) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (N Q : ℕ → ℕ) (hN : ∀ n, N n = Q n * m)
    (epsilon kappa : ℕ → ℝ) (hepsilon : ∀ᶠ n : ℕ in atTop, 0 < epsilon n)
    {V A : ℝ} (hV : 0 < V) (hA : 0 < A)
    (hNlim : Tendsto N atTop atTop)
    (hscale : Tendsto (fun n => (N n : ℝ) * epsilon n ^ (d - 1)) atTop (𝓝 A))
    (hkappa : Tendsto kappa atTop (𝓝 0))
    (hLower : ∀ᶠ n : ℕ in atTop,
      ((N n).factorial : ℝ) * Real.exp (-(N n : ℝ) * kappa n) *
        (2 * Real.pi) ^ (-(N n : ℝ) / 2) * (V / (m.factorial : ℝ)) ^ (Q n) *
          epsilon n ^ (d * N n) ≤ weightedPartition (N n) sigma c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (V / (m.factorial : ℝ)) / (m : ℝ) - 1 -
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log A - δ ≤
          normalizedPartitionLog (N n) sigma c := by
  let C : ℝ := Real.log (V / (m.factorial : ℝ)) / (m : ℝ) - 1 -
    (1 / 2 : ℝ) * Real.log (2 * Real.pi)
  let q : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  have hStirling := tendsto_log_factorial_remainder.comp hNlim
  have hlog := (Real.continuousAt_log hA.ne').tendsto.comp hscale
  have hlim := ((hStirling.add_const C).add (hlog.const_mul q)).sub hkappa
  have hev : ∀ᶠ n : ℕ in atTop,
      C + q * Real.log A - δ <
        (Real.log ((N n).factorial : ℝ) / (N n : ℝ) - Real.log (N n : ℝ) + 1) +
          C + q * Real.log ((N n : ℝ) * epsilon n ^ (d - 1)) - kappa n := by
    have hlim' : Tendsto (fun n =>
        (Real.log ((N n).factorial : ℝ) / (N n : ℝ) - Real.log (N n : ℝ) + 1) +
          C + q * Real.log ((N n : ℝ) * epsilon n ^ (d - 1)) - kappa n)
        atTop (𝓝 (C + q * Real.log A)) := by
      simpa only [Function.comp_apply, zero_add, sub_zero] using hlim
    exact hlim'.eventually (Ioi_mem_nhds (sub_lt_self _ hδ))
  filter_upwards [hepsilon, hLower, hev, hNlim.eventually (eventually_gt_atTop 0)]
    with n hε hlow hn hNpos
  have hQpos : 0 < Q n := by
    by_contra hq
    have hq0 : Q n = 0 := Nat.eq_zero_of_not_pos hq
    rw [hN n, hq0, zero_mul] at hNpos
    exact Nat.not_lt_zero 0 hNpos
  have hb := replicated_weight_log_lower hd hm hQpos (hN n) hε hV hlow
  change _ ≤ normalizedPartitionLog (N n) sigma c at hb
  dsimp only [C, q] at hn
  exact hn.le.trans (by convert hb using 1; ring)

theorem matched_local_scale_rate_lower {d : ℕ} (hd : 2 ≤ d) (r : ℕ)
    {M eta lam V S : ℝ} (hM : 0 < M) (heta : eta < 1) (hlam : lam < 1) (hS : 0 < S)
    (hV : (2 / M) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
      pinnedVolume (referenceSimplex d) r ≤ V) :
    localGammaSequence d r - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log S + (d : ℝ) * Real.log (1 - eta) +
      Real.log (1 - lam) - matchingStirlingError M r ≤
    Real.log (V / ((r + 1).factorial : ℝ)) / ((r : ℝ) + 1) - 1 -
      (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log
        (((r : ℝ) + 1) * S / (floorVolume (referenceSimplex d)).toReal) := by
  have h := matching_volume_log_lower hd r hM heta hlam hV
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hvol := floorVolume_referenceSimplex_toReal_pos hd
  rw [Real.log_div (mul_pos hN hS).ne' hvol.ne', Real.log_mul hN.ne' hS.ne']
  linarith

end Antichain
