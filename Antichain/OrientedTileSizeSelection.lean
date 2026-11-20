import Antichain.TileSizeSelection

noncomputable section

namespace Antichain.OrientedCube

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction ENNReal

variable {d J : ℕ} [NeZero d]

def weightedCubeCompleteCount {q : ℕ} (m : ℕ)
    (b : Fin q → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ) (ε : ℝ) : ℕ :=
  m * ∑ j, completeCubeTileCount (b j) (a j) (L j) (ε * w j ^ (-(1 : ℝ) / d))


theorem weightedCubeCompleteCount_linear_error (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (b : Fin q → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ)
    (hL : ∀ j, 0 < L j) (hw : ∀ j, 0 < w j) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ weightedCubeCountConstant (d := d) m L w -
        (weightedCubeCompleteCount m b a L w ε : ℝ) * ε ^ (d - 1) ∧
      weightedCubeCountConstant (d := d) m L w -
        (weightedCubeCompleteCount m b a L w ε : ℝ) * ε ^ (d - 1) ≤ C * ε := by
  let V := (floorVolume (referenceSimplex d)).toReal
  have hV : 0 < V := floorVolume_referenceSimplex_toReal_pos hd
  let c : Fin q → ℝ := fun j ↦ w j ^ (-(1 : ℝ) / d)
  let P : Fin q → ℝ := fun j ↦ w j ^ (((d - 1 : ℕ) : ℝ) / d)
  let B : Fin q → ℝ := fun j ↦
    4 * (d : ℝ) * ((d - 1 : ℕ) : ℝ) * L j ^ (d - 2) * c j * P j
  have hc : ∀ j, 0 < c j := fun j ↦ Real.rpow_pos_of_pos (hw j) _
  have hP : ∀ j, 0 < P j := fun j ↦ Real.rpow_pos_of_pos (hw j) _
  have hB : ∀ j, 0 < B j := by
    intro j
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    have := hc j
    have := hP j
    have := hL j
    dsimp [B]
    positivity
  let C : ℝ := (m : ℝ) / V * ∑ j, B j
  have hC : 0 < C := by
    apply mul_pos (div_pos (by exact_mod_cast hm) hV)
    exact Finset.sum_pos (fun j _ ↦ hB j) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hq⟩⟩)
  refine ⟨C, hC, ?_⟩
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ j, ε * c j ≤ L j / (4 * (d : ℝ)) := by
    rw [Filter.eventually_all]
    intro j
    have hlim : Tendsto (fun ε : ℝ ↦ ε * c j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ((tendsto_id.mul_const (c j)).mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ ↦ ε * c j) (𝓝[>] (0 : ℝ)) (𝓝 (0 * c j)))
    exact (hlim.eventually_lt_const (div_pos (hL j) (by positivity))).mono (fun _ h ↦ h.le)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmall
  have hε : 0 < ε := hε
  have hterm (j : Fin q) :
      0 ≤ L j ^ (d - 1) * P j -
        (completeCubeTileCount (b j) (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V ∧
      L j ^ (d - 1) * P j -
        (completeCubeTileCount (b j) (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V ≤ B j * ε := by
    obtain ⟨h0, hb⟩ := completeCubeTile_boundary_layer_bound hd H (b j) (a j) (hL j)
      (mul_pos hε (hc j)) (hsmall j)
    have heq := cube_scale_power_cancel hd (ε := ε) (hw j)
    change (ε * c j) ^ (d - 1) * P j = ε ^ (d - 1) at heq
    have h0 := mul_nonneg h0 (hP j).le
    have hb := mul_le_mul_of_nonneg_right hb (hP j).le
    have hn : (L j ^ (d - 1) -
          (completeCubeTileCount (b j) (a j) (L j) (ε * c j) : ℝ) * (ε * c j) ^ (d - 1) * V) * P j =
        L j ^ (d - 1) * P j -
          (completeCubeTileCount (b j) (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V := by
      calc
        _ = L j ^ (d - 1) * P j -
          (completeCubeTileCount (b j) (a j) (L j) (ε * c j) : ℝ) *
            ((ε * c j) ^ (d - 1) * P j) * V := by ring
        _ = _ := by rw [heq]
    constructor
    · exact hn ▸ h0
    · calc
        _ = (L j ^ (d - 1) -
          (completeCubeTileCount (b j) (a j) (L j) (ε * c j) : ℝ) * (ε * c j) ^ (d - 1) * V) * P j := by
            exact hn.symm
        _ ≤ _ := hb.trans_eq (by dsimp [B]; ring)
  have hs0 := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) ↦ (hterm j).1)
  have hsb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) ↦ (hterm j).2)
  have heq : weightedCubeCountConstant (d := d) m L w -
      (weightedCubeCompleteCount m b a L w ε : ℝ) * ε ^ (d - 1) =
      (m : ℝ) / V * ∑ j, (L j ^ (d - 1) * P j -
        (completeCubeTileCount (b j) (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V) := by
    unfold weightedCubeCountConstant weightedCubeTileMass weightedCubeCompleteCount
    simp only [Nat.cast_mul, Nat.cast_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
    dsimp [V, c, P] at *
    field_simp
  rw [heq]
  constructor
  · exact mul_nonneg (div_pos (by exact_mod_cast hm) hV).le hs0
  · apply (mul_le_mul_of_nonneg_left hsb (div_pos (by exact_mod_cast hm) hV).le).trans_eq
    dsimp [C]
    rw [← Finset.sum_mul]
    ring

theorem weightedCubeCompleteCount_normalized_tendsto (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (b : Fin q → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ)
    (hL : ∀ j, 0 < L j) (hw : ∀ j, 0 < w j) :
    Tendsto (fun ε : ℝ ↦ (weightedCubeCompleteCount m b a L w ε : ℝ) * ε ^ (d - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (weightedCubeCountConstant (d := d) m L w)) := by
  obtain ⟨C, _, herr⟩ := weightedCubeCompleteCount_linear_error hd H hq hm b a L w hL hw
  have he : Tendsto (fun ε : ℝ ↦ weightedCubeCountConstant (d := d) m L w -
      (weightedCubeCompleteCount m b a L w ε : ℝ) * ε ^ (d - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (herr.mono (fun _ h ↦ h.1)) (herr.mono (fun _ h ↦ h.2))
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul C)
  simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ weightedCubeCountConstant (d := d) m L w)
    (𝓝[>] (0 : ℝ)) (𝓝 (weightedCubeCountConstant (d := d) m L w))).sub he)


theorem weightedCubeCompleteCount_normalized_isBigO (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (b : Fin q → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ)
    (hL : ∀ j, 0 < L j) (hw : ∀ j, 0 < w j) :
    (fun ε : ℝ ↦ (weightedCubeCompleteCount m b a L w ε : ℝ) * ε ^ (d - 1) -
      weightedCubeCountConstant (d := d) m L w) =O[𝓝[>] (0 : ℝ)] (fun ε : ℝ ↦ ε) := by
  obtain ⟨C, _, herr⟩ := weightedCubeCompleteCount_linear_error hd H hq hm b a L w hL hw
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin, herr] with ε hε he
  have hεpos : 0 < ε := hε
  simpa only [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg he.1, abs_of_pos hεpos] using he.2

@[simp] theorem weightedCubeCompleteCount_eq_unweighted_mul {q : ℕ} (m : ℕ)
    (b : Fin q → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ) (ε : ℝ) :
    weightedCubeCompleteCount m b a L w ε =
      (∑ j, completeCubeTileCount (b j) (a j) (L j) (ε * w j ^ (-(1 : ℝ) / d))) * m :=
  Nat.mul_comm _ _


theorem weightedCube_size_selection (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (b : Fin q → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ)
    (hL : ∀ j, 0 < L j) (hw : ∀ j, 0 < w j) :
    let A := weightedCubeCountConstant (d := d) m L w
    let ε := tileSizeScale (d - 1) A
    let N := fun n : ℕ ↦ weightedCubeCompleteCount m b a L w (ε n)
    Tendsto ε atTop (𝓝[>] (0 : ℝ)) ∧
    (∀ᶠ n : ℕ in atTop, n ≤ N n ∧ (N n : ℝ) ≤ (n : ℝ) + (n : ℝ) ^ tileSelectionExponent (d - 1)) ∧
    Tendsto (fun n : ℕ ↦ (N n : ℝ) / n) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ ↦ ((N n - n : ℕ) : ℝ) * Real.log n / n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ (N n : ℝ) * ε n ^ (d - 1)) atTop (𝓝 A) := by
  dsimp only
  have hk : 0 < d - 1 := by omega
  have hA := weightedCubeCountConstant_pos hd hq hm hL hw
  obtain ⟨C, hC, herr⟩ := weightedCubeCompleteCount_linear_error hd H hq hm b a L w hL hw
  have hsel := count_selection_sandwich hk hA hC (weightedCubeCompleteCount m b a L w) herr
  refine ⟨tileSizeScale_tendsto_nhdsGT hk hA, hsel,
    count_selection_ratio_tendsto hk _ hsel, count_selection_gap_log_tendsto hk _ hsel, ?_⟩
  exact (weightedCubeCompleteCount_normalized_tendsto hd H hq hm b a L w hL hw).comp
    (tileSizeScale_tendsto_nhdsGT hk hA)

end Antichain.OrientedCube
