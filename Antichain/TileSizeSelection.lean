import Antichain.CubeTileCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Actual complete-tile counts and their selection at prescribed sample sizes. -/

noncomputable section

namespace Antichain

open Set Filter Finset MeasureTheory Asymptotics
open scoped Topology ENNReal

variable {d : ℕ} [NeZero d]

def weightedCubeTileMass {q : ℕ} (L w : Fin q → ℝ) : ℝ :=
  ∑ j, L j ^ (d - 1) * w j ^ (((d - 1 : ℕ) : ℝ) / d)

def weightedCubeCompleteCount {q : ℕ} (m : ℕ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ) (ε : ℝ) : ℕ :=
  m * ∑ j, completeCubeTileCount b (a j) (L j) (ε * w j ^ (-(1 : ℝ) / d))

def weightedCubeCountConstant {q : ℕ} (m : ℕ) (L w : Fin q → ℝ) : ℝ :=
  m * weightedCubeTileMass (d := d) L w / (floorVolume (referenceSimplex d)).toReal

omit [NeZero d] in
theorem cube_scale_power_cancel (_hd : 2 ≤ d) {w ε : ℝ} (hw : 0 < w) :
    (ε * w ^ (-(1 : ℝ) / d)) ^ (d - 1) * w ^ (((d - 1 : ℕ) : ℝ) / d) =
      ε ^ (d - 1) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hw.le, mul_assoc, ← Real.rpow_add hw]
  have he : -(1 : ℝ) / d * (d - 1 : ℕ) + ((d - 1 : ℕ) : ℝ) / d = 0 := by ring
  rw [he, Real.rpow_zero, mul_one]

omit [NeZero d] in
theorem weightedCubeCountConstant_pos (hd : 2 ≤ d) {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    {L w : Fin q → ℝ} (hL : ∀ j, 0 < L j) (hw : ∀ j, 0 < w j) :
    0 < weightedCubeCountConstant (d := d) m L w := by
  unfold weightedCubeCountConstant weightedCubeTileMass
  apply div_pos _ (floorVolume_referenceSimplex_toReal_pos hd)
  apply mul_pos (by exact_mod_cast hm)
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (pow_pos (hL j) _) (Real.rpow_pos_of_pos (hw j) _)
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hq⟩⟩

/-- The actual finite sum of complete-tile counts has a one-sided linear error. -/
theorem weightedCubeCompleteCount_linear_error (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
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
        (completeCubeTileCount b (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V ∧
      L j ^ (d - 1) * P j -
        (completeCubeTileCount b (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V ≤ B j * ε := by
    obtain ⟨h0, hb⟩ := completeCubeTile_boundary_layer_bound hd H b (a j) (hL j)
      (mul_pos hε (hc j)) (hsmall j)
    have heq := cube_scale_power_cancel hd (ε := ε) (hw j)
    change (ε * c j) ^ (d - 1) * P j = ε ^ (d - 1) at heq
    have h0 := mul_nonneg h0 (hP j).le
    have hb := mul_le_mul_of_nonneg_right hb (hP j).le
    have hn : (L j ^ (d - 1) -
          (completeCubeTileCount b (a j) (L j) (ε * c j) : ℝ) * (ε * c j) ^ (d - 1) * V) * P j =
        L j ^ (d - 1) * P j -
          (completeCubeTileCount b (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V := by
      calc
        _ = L j ^ (d - 1) * P j -
          (completeCubeTileCount b (a j) (L j) (ε * c j) : ℝ) *
            ((ε * c j) ^ (d - 1) * P j) * V := by ring
        _ = _ := by rw [heq]
    constructor
    · exact hn ▸ h0
    · calc
        _ = (L j ^ (d - 1) -
          (completeCubeTileCount b (a j) (L j) (ε * c j) : ℝ) * (ε * c j) ^ (d - 1) * V) * P j := by
            exact hn.symm
        _ ≤ _ := hb.trans_eq (by dsimp [B]; ring)
  have hs0 := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) ↦ (hterm j).1)
  have hsb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) ↦ (hterm j).2)
  have heq : weightedCubeCountConstant (d := d) m L w -
      (weightedCubeCompleteCount m b a L w ε : ℝ) * ε ^ (d - 1) =
      (m : ℝ) / V * ∑ j, (L j ^ (d - 1) * P j -
        (completeCubeTileCount b (a j) (L j) (ε * c j) : ℝ) * ε ^ (d - 1) * V) := by
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
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
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

/-- A surplus strictly larger than the boundary-layer exponent, and smaller than one. -/
def tileSelectionExponent (k : ℕ) : ℝ := 1 - 1 / (2 * (k : ℝ))

def tileSizeScale (k : ℕ) (A : ℝ) (n : ℕ) : ℝ :=
  (A / ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k)) ^ (1 / (k : ℝ))

omit [NeZero d] in
theorem tileSelectionExponent_bounds {k : ℕ} (hk : 0 < k) :
    0 < tileSelectionExponent k ∧ tileSelectionExponent k < 1 ∧
      1 - 1 / (k : ℝ) < tileSelectionExponent k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hhalf : (0 : ℝ) < 1 / (2 * (k : ℝ)) := by positivity
  have hhalf1 : (1 : ℝ) / (2 * k) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have heq : (1 : ℝ) / k = 2 * (1 / (2 * k)) := by field_simp
  dsimp [tileSelectionExponent]
  constructor
  · linarith
  constructor <;> linarith

omit [NeZero d] in
theorem tileSizeScale_pos {k : ℕ} (_hk : 0 < k) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 0 < n) : 0 < tileSizeScale k A n := by
  unfold tileSizeScale
  apply Real.rpow_pos_of_pos
  exact div_pos hA (add_pos (by exact_mod_cast hn)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _))

omit [NeZero d] in
theorem tileSizeScale_pow {k : ℕ} (hk : 0 < k) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 0 < n) :
    tileSizeScale k A n ^ k = A / ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) := by
  unfold tileSizeScale
  rw [one_div]
  exact Real.rpow_inv_natCast_pow (div_pos hA (add_pos (by exact_mod_cast hn)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _))).le (ne_of_gt hk)

omit [NeZero d] in
theorem tileSizeScale_tendsto {k : ℕ} (hk : 0 < k) (A : ℝ) :
    Tendsto (tileSizeScale k A) atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ ↦ A / ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hkR : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  simpa only [tileSizeScale, Real.zero_rpow hkR.ne'] using
    (Real.continuous_rpow_const hkR.le).continuousAt.tendsto.comp hdiv

omit [NeZero d] in
theorem tileSizeScale_tendsto_nhdsGT {k : ℕ} (hk : 0 < k) {A : ℝ} (hA : 0 < A) :
    Tendsto (tileSizeScale k A) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_inf.mpr
  constructor
  · exact tileSizeScale_tendsto hk A
  · apply tendsto_principal.mpr
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact tileSizeScale_pos hk hA hn

omit [NeZero d] in
theorem tileSelection_surplus_ratio_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ tileSelectionExponent k / (n : ℝ)) atTop (𝓝 0) := by
  have hkR : (0 : ℝ) < 1 / (2 * (k : ℝ)) := by positivity
  have h := (tendsto_rpow_neg_atTop hkR).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ) ^ (-(1 / (2 * (k : ℝ)))) = (n : ℝ) ^ tileSelectionExponent k / n
  calc
    _ = (n : ℝ) ^ (tileSelectionExponent k - 1) := by congr 1; unfold tileSelectionExponent; ring
    _ = (n : ℝ) ^ tileSelectionExponent k / (n : ℝ) ^ (1 : ℝ) := Real.rpow_sub hnR _ _
    _ = _ := by rw [Real.rpow_one]

omit [NeZero d] in
theorem tileSizeScale_lossRatio_tendsto {k : ℕ} (hk : 0 < k) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun n : ℕ ↦ tileSizeScale k A n *
      ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) /
        (n : ℝ) ^ tileSelectionExponent k) atTop (𝓝 0) := by
  have hkR : (0 : ℝ) < 1 / (2 * (k : ℝ)) := by positivity
  have hlim : Tendsto (fun n : ℕ ↦ (2 * A ^ (1 / (k : ℝ))) *
      (n : ℝ) ^ (-(1 / (2 * (k : ℝ))))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hkR).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2 * A ^ (1 / (k : ℝ)))
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_nonneg (mul_nonneg (tileSizeScale_pos hk hA hn).le
      (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnp : 0 < (n : ℝ) ^ tileSelectionExponent k := Real.rpow_pos_of_pos hnR _
    have hζ := (tileSelectionExponent_bounds hk).2.1.le
    have hden : (n : ℝ) + (n : ℝ) ^ tileSelectionExponent k ≤ 2 * n := by
      linarith [Real.rpow_le_self_of_one_le hn1 hζ]
    have hbase : A / ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) ≤ A / n :=
      div_le_div_of_nonneg_left hA.le hnR (le_add_of_nonneg_right hnp.le)
    have heps : tileSizeScale k A n ≤ A ^ (1 / (k : ℝ)) * (n : ℝ) ^ (-(1 / (k : ℝ))) := by
      have hr := Real.rpow_le_rpow (div_pos hA (add_pos hnR hnp)).le hbase (by positivity : 0 ≤ 1 / (k : ℝ))
      calc
        _ ≤ (A / (n : ℝ)) ^ (1 / (k : ℝ)) := hr
        _ = _ := by rw [Real.div_rpow hA.le hnR.le, Real.rpow_neg hnR.le, div_eq_mul_inv]
    have hpower : (n : ℝ) ^ (-(1 / (k : ℝ))) * n / (n : ℝ) ^ tileSelectionExponent k =
        (n : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := by
      calc
        _ = ((n : ℝ) ^ (-(1 / (k : ℝ))) * (n : ℝ) ^ (1 : ℝ)) /
            (n : ℝ) ^ tileSelectionExponent k := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ (-(1 / (k : ℝ)) + 1) / (n : ℝ) ^ tileSelectionExponent k := by
          rw [Real.rpow_add hnR]
        _ = (n : ℝ) ^ (-(1 / (k : ℝ)) + 1 - tileSelectionExponent k) :=
          (Real.rpow_sub hnR _ _).symm
        _ = _ := by congr 1; unfold tileSelectionExponent; field_simp; ring
    calc
      _ ≤ (A ^ (1 / (k : ℝ)) * (n : ℝ) ^ (-(1 / (k : ℝ)))) * (2 * n) /
          (n : ℝ) ^ tileSelectionExponent k :=
        div_le_div_of_nonneg_right
          (mul_le_mul heps hden (by positivity) (by positivity)) hnp.le
      _ = (2 * A ^ (1 / (k : ℝ))) *
          ((n : ℝ) ^ (-(1 / (k : ℝ))) * n / (n : ℝ) ^ tileSelectionExponent k) := by ring
      _ = _ := by rw [hpower]

/- An elementary inversion lemma for a count with a one-sided boundary error.
The actual cube-count theorem below supplies this intermediate hypothesis. -/
omit [NeZero d] in
theorem count_selection_sandwich {k : ℕ} (hk : 0 < k) {A C : ℝ} (hA : 0 < A) (_hC : 0 < C)
    (N : ℝ → ℕ)
    (herr : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ A - (N ε : ℝ) * ε ^ k ∧ A - (N ε : ℝ) * ε ^ k ≤ C * ε) :
    ∀ᶠ n : ℕ in atTop, n ≤ N (tileSizeScale k A n) ∧
      (N (tileSizeScale k A n) : ℝ) ≤ (n : ℝ) + (n : ℝ) ^ tileSelectionExponent k := by
  have hcounts := (tileSizeScale_tendsto_nhdsGT hk hA).eventually herr
  have hlosslim : Tendsto (fun n : ℕ ↦ C * (tileSizeScale k A n *
      ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) / (n : ℝ) ^ tileSelectionExponent k))
      atTop (𝓝 0) := by simpa using (tileSizeScale_lossRatio_tendsto hk hA).const_mul C
  have hsmall := hlosslim.eventually_lt_const hA
  filter_upwards [hcounts, hsmall, eventually_gt_atTop (0 : ℕ)] with n he hsmall hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) ^ tileSelectionExponent k := Real.rpow_pos_of_pos hnR _
  have hB : 0 < (n : ℝ) + (n : ℝ) ^ tileSelectionExponent k := add_pos hnR hnp
  rw [tileSizeScale_pow hk hA hn] at he
  have hu := mul_nonneg he.1 hB.le
  have hl := mul_le_mul_of_nonneg_right he.2 hB.le
  rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hB.ne'] at hu hl
  have hloss : C * tileSizeScale k A n *
      ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) ≤ A * (n : ℝ) ^ tileSelectionExponent k := by
    have hh : C * tileSizeScale k A n *
        ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) /
          (n : ℝ) ^ tileSelectionExponent k < A := by
      convert hsmall using 1; ring
    exact ((div_lt_iff₀ hnp).mp hh).le
  have hrealLower : (n : ℝ) ≤ N (tileSizeScale k A n) := by nlinarith
  exact ⟨by exact_mod_cast hrealLower, by nlinarith⟩

omit [NeZero d] in
theorem count_selection_ratio_tendsto {k : ℕ} (hk : 0 < k) (M : ℕ → ℕ)
    (hM : ∀ᶠ n : ℕ in atTop, n ≤ M n ∧ (M n : ℝ) ≤ (n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) :
    Tendsto (fun n : ℕ ↦ (M n : ℝ) / n) atTop (𝓝 1) := by
  have hz : Tendsto (fun n : ℕ ↦ (M n : ℝ) / n - 1) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (tileSelection_surplus_ratio_tendsto hk)
    · filter_upwards [hM, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hle : (n : ℝ) ≤ M n := by exact_mod_cast hn.1
      exact sub_nonneg.mpr ((le_div_iff₀ hnR).mpr (by simpa using hle))
    · filter_upwards [hM, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hh := div_le_div_of_nonneg_right hn.2 hnR.le
      have heq : ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) / n =
          1 + (n : ℝ) ^ tileSelectionExponent k / n := by field_simp
      rw [heq] at hh
      linarith
  simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add hz)

omit [NeZero d] in
theorem count_selection_gap_log_tendsto {k : ℕ} (hk : 0 < k) (M : ℕ → ℕ)
    (hM : ∀ᶠ n : ℕ in atTop, n ≤ M n ∧ (M n : ℝ) ≤ (n : ℝ) + (n : ℝ) ^ tileSelectionExponent k) :
    Tendsto (fun n : ℕ ↦ ((M n - n : ℕ) : ℝ) * Real.log n / n) atTop (𝓝 0) := by
  have hβ : 0 < 1 - tileSelectionExponent k := sub_pos.mpr (tileSelectionExponent_bounds hk).2.1
  have hlog := (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupper : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ tileSelectionExponent k * Real.log n / n)
      atTop (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    change Real.log (n : ℝ) / (n : ℝ) ^ (1 - tileSelectionExponent k) = _
    rw [Real.rpow_sub hnR, Real.rpow_one]
    field_simp
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hnR)) (Nat.cast_nonneg n)
  · filter_upwards [hM, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [Nat.cast_sub hn.1]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hnR)
    linarith [hn.2]

omit [NeZero d] in
theorem tileDimensionRatio_eq_source (hd : 2 ≤ d) :
    ((d - 1 : ℕ) : ℝ) / d = ((d : ℝ) - 1) / d := by
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]

theorem weightedCubeCompleteCount_normalized_isBigO (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
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
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin q → Fin (d - 1) → ℝ) (L w : Fin q → ℝ) (ε : ℝ) :
    weightedCubeCompleteCount m b a L w ε =
      (∑ j, completeCubeTileCount b (a j) (L j) (ε * w j ^ (-(1 : ℝ) / d))) * m :=
  Nat.mul_comm _ _

omit [NeZero d] in
theorem weightedCube_selected_scale_formula {q : ℕ} (m : ℕ) (L w : Fin q → ℝ) (n : ℕ) :
    tileSizeScale (d - 1) (weightedCubeCountConstant (d := d) m L w) n =
      ((m : ℝ) * weightedCubeTileMass (d := d) L w /
        ((floorVolume (referenceSimplex d)).toReal *
          ((n : ℝ) + (n : ℝ) ^ tileSelectionExponent (d - 1)))) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  rw [tileSizeScale, weightedCubeCountConstant, div_div]

/-- Actual source size selection, with no assumed count asymptotic or selection premise. -/
theorem weightedCube_size_selection (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
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

end Antichain
