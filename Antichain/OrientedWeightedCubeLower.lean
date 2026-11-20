import Antichain.WeightedCubeLower

noncomputable section

namespace Antichain.OrientedCube

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction ENNReal

variable {d J : ℕ} [NeZero d]

def cubeScaleMultiplier (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (j : Fin J) : ℝ :=
  floorCubeWeightInf sigma (b j) (a j) (L j) ^ (-1 / (d : ℝ))

def cubeScaleBound (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) : ℝ :=
  1 + ∑ j, cubeScaleMultiplier sigma b a L j

def weightedCubeTileCount (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (ε : ℝ) : ℕ :=
  ∑ j, completeCubeTileCount (b j) (a j) (L j) (ε * cubeScaleMultiplier sigma b a L j)

omit [NeZero d] in
theorem cubeScaleMultiplier_pos (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (j : Fin J) : 0 < cubeScaleMultiplier sigma b a L j :=
  Real.rpow_pos_of_pos (floorCubeWeightInf_pos sigma (b j) (a j) (hL j)) _

omit [NeZero d] in
theorem cubeScaleBound_pos (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 ≤ L j) :
    0 < cubeScaleBound sigma b a L := by
  unfold cubeScaleBound
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun j _ => (cubeScaleMultiplier_pos sigma b a L hL j).le))

omit [NeZero d] in
theorem cubeScaleMultiplier_le_bound (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (j : Fin J) :
    cubeScaleMultiplier sigma b a L j ≤ cubeScaleBound sigma b a L := by
  exact (Finset.single_le_sum (fun i _ => (cubeScaleMultiplier_pos sigma b a L hL i).le)
    (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

theorem cubeScaleMultiplier_cancellation (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (ε : ℝ) (j : Fin J) :
    floorCubeWeightInf sigma (b j) (a j) (L j) *
      (ε * cubeScaleMultiplier sigma b a L j) ^ d = ε ^ d := by
  let w := floorCubeWeightInf sigma (b j) (a j) (L j)
  have hw : 0 < w := floorCubeWeightInf_pos sigma (b j) (a j) (hL j)
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hpow : (w ^ (-1 / (d : ℝ))) ^ d = w⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    rw [div_mul_cancel₀ _ hdR, Real.rpow_neg_one]
  change w * (ε * w ^ (-1 / (d : ℝ))) ^ d = ε ^ d
  rw [mul_pow, hpow]
  field_simp

theorem weightedCubeTileCount_eq_regions (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (ε : ℝ) (hε : 0 < ε) :
    weightedCubeTileCount sigma b a L ε =
      completeRegionTileCount hd H J (fun j => orthonormalFloorCube (b j) (a j) (L j))
        (fun j => isCompact_orthonormalFloorCube (b j) (a j) (L j))
        (fun j => ε * cubeScaleMultiplier sigma b a L j)
        (fun j => mul_pos hε (cubeScaleMultiplier_pos sigma b a L hL j)) := by
  rw [completeRegionTileCount_eq_sum]
  unfold weightedCubeTileCount
  apply Finset.sum_congr rfl
  intro j _
  exact completeCubeTileCount_eq_card hd H (b j) (a j) (L j) _
    (mul_pos hε (cubeScaleMultiplier_pos sigma b a L hL j))

/-- The exact finite-scale lower bound for the paper's actual complete cubes,
using their true infimum floor weights and their prescribed weight-dependent
tile scales. This is the geometric/integral step of Lemma 5.4. -/
theorem weighted_cubes_partition_lower (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (m : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (sep C : ℝ) (hsep0 : 0 < sep) (hC : 0 ≤ C)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ orthonormalFloorCube (b i) (a i) (L i),
      ∀ y ∈ orthonormalFloorCube (b j) (a j) (L j), sep ≤ dist x y)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧ (∀ v : SimplexBoundary d, E v.val = boundary v) ∧
      (∀ u v, E u - E v ≤ nativeFloorCost u v))
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : 2 * C * (ε * cubeScaleBound sigma b a L) ≤
      sep / Real.sqrt ((d : ℝ) - 1)) :
    let Q := weightedCubeTileCount sigma b a L ε
    let N := Q * m
    (Nat.factorial N : ℝ) *
      Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * (ε * cubeScaleBound sigma b a L)) ^ 2)) *
        (2 * Real.pi) ^ (-(N : ℝ) / 2) * ((volume B).toReal / (Nat.factorial m : ℝ)) ^ Q *
          ε ^ (d * N) ≤ weightedPartition N sigma c := by
  have hL0 : ∀ j, 0 ≤ L j := fun j => (hL j).le
  have hscalepos : ∀ j, 0 < ε * cubeScaleMultiplier sigma b a L j :=
    fun j => mul_pos hε (cubeScaleMultiplier_pos sigma b a L hL0 j)
  have hbound : ∀ j, ε * cubeScaleMultiplier sigma b a L j ≤ ε * cubeScaleBound sigma b a L :=
    fun j => mul_le_mul_of_nonneg_left (cubeScaleMultiplier_le_bound sigma b a L hL0 j) hε.le
  have hweight : ∀ j x, x ∈ orthonormalFloorCube (b j) (a j) (L j) →
      floorCubeWeightInf sigma (b j) (a j) (L j) ≤ weightedFloorDensity sigma x := by
    intro j x hx
    exact (floorCubeWeightInf_attained sigma (b j) (a j) (hL0 j)).choose_spec.2.2 x hx
  have hb := complete_regions_weighted_lower hd H J m
    (fun j => orthonormalFloorCube (b j) (a j) (L j))
    (fun j => isCompact_orthonormalFloorCube (b j) (a j) (L j))
    (fun j => ε * cubeScaleMultiplier sigma b a L j) hscalepos ε sep C
    (ε * cubeScaleBound sigma b a L) hsep0 hC
    (mul_nonneg hε.le (cubeScaleBound_pos sigma b a L hL0).le) hbound hsep hsmall
    hB boundary hf hh hext sigma c hc (fun j => floorCubeWeightInf sigma (b j) (a j) (L j))
    (fun j => (floorCubeWeightInf_pos sigma (b j) (a j) (hL0 j)).le) hweight
    (cubeScaleMultiplier_cancellation sigma b a L hL0 ε)
  dsimp only at hb ⊢
  rw [weightedCubeTileCount_eq_regions hd H sigma b a L hL0 ε hε]
  exact hb

/-- The source local family and the complete-cube construction composed,
ready for the scalar size-selection and limiting arguments. V is the actual
ordinary volume of the proved measurable matched family, not an assumed
coefficient. The scale cutoff is fixed before the local sample count. -/
theorem matching_weighted_cubes_finite_scale (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (b : Fin J → OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (sep : ℝ) (hsep0 : 0 < sep)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ orthonormalFloorCube (b i) (a i) (L i),
      ∀ y ∈ orthonormalFloorCube (b j) (a j) (L j), sep ≤ dist x y) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ eta lam : ℝ, eta ∈ Ioo 0 (1 / 2 : ℝ) → lam ∈ Ioo 0 (1 / 2 : ℝ) →
      ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ, ∃ V : ℝ, 0 < V ∧
        (2 / (M : ℝ)) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
          pinnedVolume (referenceSimplex d) r ≤ V ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          let Q := weightedCubeTileCount sigma b a L ε
          let N := Q * (r + 1)
          (Nat.factorial N : ℝ) *
            Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) *
              (C * (ε * cubeScaleBound sigma b a L)) ^ 2)) *
            (2 * Real.pi) ^ (-(N : ℝ) / 2) * (V / (Nat.factorial (r + 1) : ℝ)) ^ Q *
              ε ^ (d * N) ≤ weightedPartition N sigma c := by
  obtain ⟨C, hC, hCM⟩ := boundary_matching_source hd
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hL0 : ∀ j, 0 ≤ L j := fun j => (hL j).le
  let A := cubeScaleBound sigma b a L
  have hA : 0 < A := cubeScaleBound_pos sigma b a L hL0
  have hsqrt : 0 < Real.sqrt ((d : ℝ) - 1) := by
    apply Real.sqrt_pos.mpr
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let δ := (sep / Real.sqrt ((d : ℝ) - 1)) / (2 * C * A)
  have hδ : 0 < δ := div_pos (div_pos hsep0 hsqrt) (by positivity)
  refine ⟨C, hC, δ, hδ, fun eta lam heta hlam => ?_⟩
  obtain ⟨M, hM, hMB⟩ := hCM eta lam heta hlam
  refine ⟨M, hM, fun r => ?_⟩
  obtain ⟨B, boundary, hB, hBevent, hBbound, hBext, hBvolume⟩ := hMB r
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have heta1 : eta < 1 := heta.2.trans (by norm_num)
  have hlam1 : lam < 1 := hlam.2.trans (by norm_num)
  have hbase : 0 < (2 / (M : ℝ)) * (1 - eta) ^ (d * (r + 1)) *
      (1 - lam) ^ (r + 1) * pinnedVolume (referenceSimplex d) r :=
    mul_pos (mul_pos (mul_pos (div_pos (by norm_num) hMpos)
      (pow_pos (sub_pos.mpr heta1) _)) (pow_pos (sub_pos.mpr hlam1) _))
      (pinnedVolume_referenceSimplex_pos hd r)
  refine ⟨(volume B).toReal, hbase.trans_le hBvolume, hBvolume, ?_⟩
  intro ε hε hεδ
  have hsmall : 2 * C * (ε * cubeScaleBound sigma b a L) ≤
      sep / Real.sqrt ((d : ℝ) - 1) := by
    have hm := (le_div_iff₀ (show 0 < 2 * C * A by positivity)).mp hεδ
    nlinarith
  have hfloor : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d) := by
    intro p hp j
    by_contra hn
    have hfront : p.1 j ∈ frontier (referenceSimplex d) :=
      ⟨subset_closure ((hBevent p hp).1 j), hn⟩
    have hm := (hBbound p hp j).2
    rw [Metric.infDist_zero_of_mem hfront] at hm
    have hpos : 0 < eta / C := div_pos heta.1 hCp
    linarith
  exact weighted_cubes_partition_lower hd H sigma c hc b (r + 1) a L hL sep C hsep0 hCp.le
    hsep hB boundary hfloor (fun p hp j => (hBbound p hp j).1) hBext ε hε hsmall


end Antichain.OrientedCube
