import Antichain.WeightedCubeLower
import Antichain.CubeSeparation
import Antichain.TileSizeSelection
import Antichain.LowerRateAnalysis

/-! The complete lower rate, from the actual copied Gaussian configurations
through prescribed sample sizes and actual finite cube approximations. -/

noncomputable section

namespace Antichain

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def cubeLowerSum (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) : ℝ :=
  ∑ j, L j ^ (d - 1) * floorCubeWeightInf sigma b (a j) (L j) ^
    (((d : ℝ) - 1) / (d : ℝ))

omit [NeZero d] in
theorem cubeLowerSum_pos (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (hJ : 0 < J) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 < L j) : 0 < cubeLowerSum sigma b J a L := by
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (pow_pos (hL j) _) (Real.rpow_pos_of_pos
      (floorCubeWeightInf_pos sigma b (a j) (hL j).le) _)
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hJ⟩⟩

/-- The all-size lower bound for the actual separated cubes, with all local
family, factorial, Gaussian, scale-selection and deletion steps proved. -/
theorem normalizedPartitionLog_separated_cubes_lower (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (hJ : 0 < J) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 < L j) (sep : ℝ) (hsep0 : 0 < sep)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ orthonormalFloorCube b (a i) (L i),
      ∀ y ∈ orthonormalFloorCube b (a j) (L j), sep ≤ dist x y)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log (cubeLowerSum sigma b J a L) - δ ≤
          normalizedPartitionLog n sigma c := by
  let S := cubeLowerSum sigma b J a L
  have hS : 0 < S := cubeLowerSum_pos sigma b J hJ a L hL
  obtain ⟨C, hC, cutoff, hcutoff, hfamily⟩ := matching_weighted_cubes_finite_scale
    hd H sigma c hc b J a L hL sep hsep0 hsep
  apply lower_rate_remove_contractions (fun n => normalizedPartitionLog n sigma c) (d : ℝ)
    (localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
      (d : ℝ) / ((d : ℝ) - 1) * Real.log S) ?_ hδ
  intro eta lam heta hlam e he
  obtain ⟨M, hM, hlocal⟩ := hfamily eta lam heta hlam
  let D : ℝ := -(1 / 2 : ℝ) * Real.log (2 * Real.pi) +
    (d : ℝ) / ((d : ℝ) - 1) * Real.log S +
      (d : ℝ) * Real.log (1 - eta) + Real.log (1 - lam)
  have hgamma : ∀ r : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
      localGammaSequence d r + D - matchingStirlingError (M : ℝ) r - e ≤
        normalizedPartitionLog n sigma c := by
    intro r e he
    obtain ⟨V, hV, hVmatching, hfinite⟩ := hlocal r
    let w : Fin J → ℝ := fun j => floorCubeWeightInf sigma b (a j) (L j)
    have hw : ∀ j, 0 < w j := fun j => floorCubeWeightInf_pos sigma b (a j) (hL j).le
    let A := weightedCubeCountConstant (d := d) (r + 1) L w
    let ε := tileSizeScale (d - 1) A
    let N : ℕ → ℕ := fun n => weightedCubeCompleteCount (r + 1) b a L w (ε n)
    let Q : ℕ → ℕ := fun n => weightedCubeTileCount sigma b J a L (ε n)
    have hA : 0 < A := weightedCubeCountConstant_pos hd hJ (Nat.succ_pos r) hL hw
    have hN : ∀ n, N n = Q n * (r + 1) := by
      intro n
      dsimp [N, Q, weightedCubeCompleteCount, weightedCubeTileCount, cubeScaleMultiplier, w]
      exact Nat.mul_comm _ _
    obtain ⟨hεlim, hNsandwich, hRatio, hGap, hscale⟩ :=
      weightedCube_size_selection hd H hJ (Nat.succ_pos r) b a L w hL hw
    change Tendsto ε atTop (𝓝[>] (0 : ℝ)) at hεlim
    change (∀ᶠ n : ℕ in atTop, n ≤ N n ∧ _) at hNsandwich
    change Tendsto (fun n => (N n : ℝ) / (n : ℝ)) atTop (𝓝 1) at hRatio
    change Tendsto (fun n => ((N n - n : ℕ) : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) at hGap
    change Tendsto (fun n => (N n : ℝ) * ε n ^ (d - 1)) atTop (𝓝 A) at hscale
    have hNle : ∀ᶠ n : ℕ in atTop, n ≤ N n := hNsandwich.mono (fun _ hn => hn.1)
    have hNlim : Tendsto N atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro k
      filter_upwards [hNle, eventually_ge_atTop k] with n hn hk
      exact hk.trans hn
    have hεpos : ∀ᶠ n : ℕ in atTop, 0 < ε n := hεlim.eventually self_mem_nhdsWithin
    have hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)) := hεlim.mono_right nhdsWithin_le_nhds
    have hεsmall : ∀ᶠ n : ℕ in atTop, ε n ≤ cutoff :=
      (hεzero.eventually (Iio_mem_nhds hcutoff)).mono (fun _ hn => hn.le)
    let κ : ℕ → ℝ := fun n => ((1 / 2 : ℝ) - c) *
      (C * (ε n * cubeScaleBound sigma b J a L)) ^ 2
    have hκ : Tendsto κ atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), κ] using
        (((hεzero.mul_const (cubeScaleBound sigma b J a L)).const_mul C).pow 2).const_mul
          ((1 / 2 : ℝ) - c)
    have hLower : ∀ᶠ n : ℕ in atTop,
        ((N n).factorial : ℝ) * Real.exp (-(N n : ℝ) * κ n) *
          (2 * Real.pi) ^ (-(N n : ℝ) / 2) * (V / ((r + 1).factorial : ℝ)) ^ Q n *
            ε n ^ (d * N n) ≤ weightedPartition (N n) sigma c := by
      filter_upwards [hεpos, hεsmall] with n hn hnsmall
      have h := hfinite (ε n) hn hnsmall
      dsimp only at h
      rw [← hN n] at h
      exact h
    let R : ℝ := Real.log (V / ((r + 1).factorial : ℝ)) / ((r + 1 : ℕ) : ℝ) - 1 -
      (1 / 2 : ℝ) * Real.log (2 * Real.pi) + (d : ℝ) / ((d : ℝ) - 1) * Real.log A
    have hConstructed : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
        R - e ≤ normalizedPartitionLog (N n) sigma c := by
      intro e he
      exact replicated_partition_rate_of_scaling hd (Nat.succ_pos r) sigma c N Q hN ε κ
        hεpos hV hA hNlim hscale hκ hLower he
    have hAll := normalizedPartitionLog_interpolate_lower hd sigma c hc N hNle hRatio hGap hConstructed he
    have hAeq : A = ((r : ℝ) + 1) * S / (floorVolume (referenceSimplex d)).toReal := by
      simp only [A, weightedCubeCountConstant, weightedCubeTileMass, w, S, cubeLowerSum,
        tileDimensionRatio_eq_source hd, Nat.cast_add, Nat.cast_one]
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
    have hloc := matched_local_scale_rate_lower hd r hMpos
      (heta.2.trans (by norm_num : (1 / 2 : ℝ) < 1))
      (hlam.2.trans (by norm_num : (1 / 2 : ℝ) < 1)) hS hVmatching
    rw [← hAeq] at hloc
    filter_upwards [hAll] with n hn
    dsimp only [R, D] at hn ⊢
    simp only [Nat.cast_add, Nat.cast_one] at hn
    linarith
  have h := lower_rate_from_local_gamma hd (fun n => normalizedPartitionLog n sigma c) (M : ℝ) D hgamma he
  filter_upwards [h] with n hn
  dsimp only [D] at hn
  linarith

/-- Full Lemma 5.4, including cubes whose boundaries meet. The last passage
uses actual concentric subcubes and their proved increasing weight infima. -/
theorem normalizedPartitionLog_cubes_lower (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (hJ : 0 < J) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j => Disjoint (interior (orthonormalFloorCube b (a i) (L i)))
      (interior (orthonormalFloorCube b (a j) (L j)))))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log (cubeLowerSum sigma b J a L) - δ ≤
          normalizedPartitionLog n sigma c := by
  let S := cubeLowerSum sigma b J a L
  let C := localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi)
  let q : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  have hS : 0 < S := cubeLowerSum_pos sigma b J hJ a L hL
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 < q := div_pos (by linarith) (by linarith)
  have hp : 0 ≤ ((d : ℝ) - 1) / (d : ℝ) := div_nonneg (by linarith) (by linarith)
  have hfactor : Tendsto (fun t : ℝ => (1 - t) ^ (d - 1) * S)
      (𝓝[>] (0 : ℝ)) (𝓝 S) := by
    have h : Tendsto (fun t : ℝ => (1 - t) ^ (d - 1) * S) (𝓝 (0 : ℝ)) (𝓝 S) := by
      simpa only [sub_zero, one_pow, one_mul] using
        (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 (0 : ℝ)) (𝓝 1)).sub
          tendsto_id).pow (d - 1)).mul_const S
    exact h.mono_left nhdsWithin_le_nhds
  have hlim := (((Real.continuousAt_log hS.ne').tendsto.comp hfactor).const_mul q).const_add C
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 ∧
      C + q * Real.log S - δ / 2 < C + q * Real.log ((1 - t) ^ (d - 1) * S) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,
      hlim.eventually (Ioi_mem_nhds (sub_lt_self _ (half_pos hδ)))] with t ht0 ht1 ht
    exact ⟨⟨ht0, ht1⟩, ht⟩
  obtain ⟨t, ht, hclose⟩ := hevent.exists
  let a' := fun j => shrunkenCubeOrigin (a j) (L j) t
  let L' := fun j => (1 - t) * L j
  have hL' : ∀ j, 0 < L' j := fun j => mul_pos (sub_pos.mpr ht.2) (hL j)
  obtain ⟨sep, hsep, hsepbound⟩ := shrunkenCubes_positive_separation b J a L hL hdis ht
  have hlower := normalizedPartitionLog_separated_cubes_lower hd H sigma c hc b J hJ a' L' hL'
    sep hsep hsepbound (half_pos hδ)
  have hweight : (1 - t) ^ (d - 1) * S ≤ cubeLowerSum sigma b J a' L' :=
    shrunkenCube_lower_weight_sum sigma b J a L hL hp ht
  have hbase : 0 < (1 - t) ^ (d - 1) * S := mul_pos (pow_pos (sub_pos.mpr ht.2) _) hS
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_log hbase hweight) hq.le
  filter_upwards [hlower] with n hn
  change C + q * Real.log S - δ ≤ normalizedPartitionLog n sigma c
  change C + q * Real.log (cubeLowerSum sigma b J a' L') - δ / 2 ≤ _ at hn
  linarith

/-- Complete source Lemma 5.5 for the actual weighted Gaussian partition
function. The cube approximation uses the genuine floor density and actual
Euclidean measure; no rate or integral approximation is assumed. -/
theorem normalizedPartitionLog_lower (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (d : ℝ) / ((d : ℝ) - 1) * Real.log
          (∫ u : FloorSpace (Fin d), weightedFloorDensity sigma u ^
            (((d : ℝ) - 1) / (d : ℝ))) - δ ≤ normalizedPartitionLog n sigma c := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let p : ℝ := ((d : ℝ) - 1) / (d : ℝ)
  let q : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  let C := localGammaConstant d hd - (1 / 2 : ℝ) * Real.log (2 * Real.pi)
  let I := ∫ u : FloorSpace (Fin d), weightedFloorDensity sigma u ^ p
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  have hq : 0 < q := div_pos (by linarith) (by linarith)
  have hI : 0 < I := weightedFloorDensity_rpow_integral_pos sigma hp
  let b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)) :=
    (stdOrthonormalBasis ℝ (FloorSpace (Fin d))).reindex
      (finCongr (by simpa only [Fintype.card_fin] using
        (finrank_floorSpace (ι := Fin d))))
  have hfactor : Tendsto (fun η : ℝ => I - η) (𝓝[>] (0 : ℝ)) (𝓝 I) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds :
        Tendsto (fun η : ℝ => I - η) (𝓝[>] (0 : ℝ)) (𝓝 (I - 0)))
  have hlim := (((Real.continuousAt_log hI.ne').tendsto.comp hfactor).const_mul q).const_add C
  have hevent : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η ∧ η < I ∧
      C + q * Real.log I - δ / 2 < C + q * Real.log (I - η) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hI).filter_mono nhdsWithin_le_nhds,
      hlim.eventually (Ioi_mem_nhds (sub_lt_self _ (half_pos hδ)))] with η hη hηI hclose
    exact ⟨hη, hηI, hclose⟩
  obtain ⟨η, hη, hηI, hclose⟩ := hevent.exists
  obtain ⟨J, hJ, a, L, hL, hdis, _, happrox⟩ := exists_floorCube_lower_approximation sigma hp b hη
  have hS : I - η < cubeLowerSum sigma b J a (fun _ => L) := happrox
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_log (sub_pos.mpr hηI) hS.le) hq.le
  have h := normalizedPartitionLog_cubes_lower hd H sigma c hc b J hJ a (fun _ => L)
    (fun _ => hL) (fun i j hij => (hdis hij).mono interior_subset interior_subset) (half_pos hδ)
  filter_upwards [h] with n hn
  change C + q * Real.log I - δ ≤ normalizedPartitionLog n sigma c
  change C + q * Real.log (cubeLowerSum sigma b J a (fun _ => L)) - δ / 2 ≤ _ at hn
  linarith

end Antichain
