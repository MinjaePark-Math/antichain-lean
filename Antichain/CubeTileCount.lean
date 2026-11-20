import Antichain.AlcoveTiling
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

/-! Quantitative complete-cube tile counting from actual vanishing-diameter tiles. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset Filter
open scoped Topology ENNReal Pointwise Asymptotics

variable {d : ℕ} [NeZero d]

def orthonormalFloorCube
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) : Set (FloorSpace (Fin d)) :=
  {x | ∀ i, a i ≤ b.repr x i ∧ b.repr x i ≤ a i + L}

omit [NeZero d] in
theorem isCompact_orthonormalFloorCube
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) : IsCompact (orthonormalFloorCube b a L) := by
  let f : (Fin (d - 1) → ℝ) → FloorSpace (Fin d) := fun v ↦ b.repr.symm (WithLp.toLp 2 v)
  have heq : orthonormalFloorCube b a L = f '' Icc a (fun i ↦ a i + L) := by
    ext x
    constructor
    · intro hx
      refine ⟨fun i ↦ b.repr x i, ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩, ?_⟩
      change b.repr.symm (b.repr x) = x
      exact b.repr.symm_apply_apply x
    · rintro ⟨v, hv, rfl⟩
      intro i
      change a i ≤ b.repr (b.repr.symm (WithLp.toLp 2 v)) i ∧
        b.repr (b.repr.symm (WithLp.toLp 2 v)) i ≤ a i + L
      rw [b.repr.apply_symm_apply]
      exact ⟨hv.1 i, hv.2 i⟩
  rw [heq]
  exact isCompact_Icc.image (b.repr.symm.continuous.comp (PiLp.continuous_toLp 2 (fun _ ↦ ℝ)))

omit [NeZero d] in
theorem volume_orthonormalFloorCube
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) :
    (volume : Measure (FloorSpace (Fin d))) (orthonormalFloorCube b a L) =
      ENNReal.ofReal L ^ (d - 1) := by
  let f : FloorSpace (Fin d) → (Fin (d - 1) → ℝ) := fun x ↦ WithLp.ofLp (b.repr x)
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (ι := Fin (d - 1))).comp b.measurePreserving_repr
  have heq : f ⁻¹' Icc a (fun i ↦ a i + L) = orthonormalFloorCube b a L := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, Pi.le_def, orthonormalFloorCube, mem_setOf_eq, forall_and]
    rfl
  rw [← heq, hf.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem completeAlcoves_finite (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    {ε : ℝ} (hε : 0 < ε) {K : Set (FloorSpace (Fin d))} (hK : IsCompact K) :
    {t : AlcoveTile d | scaledAlcove d ε t ⊆ K}.Finite := by
  apply ((scaledAlcove_locallyFinite d H hε).finite_nonempty_inter_compact hK).subset
  intro t ht
  exact (scaledAlcove_nonempty d hd ε t).mono (fun _ hx ↦ ⟨hx, ht hx⟩)

def completeAlcoves (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) (ε : ℝ) (hε : 0 < ε)
    (K : Set (FloorSpace (Fin d))) (hK : IsCompact K) : Finset (AlcoveTile d) :=
  (completeAlcoves_finite hd H hε hK).toFinset

@[simp] theorem mem_completeAlcoves (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (ε : ℝ) (hε : 0 < ε) (K : Set (FloorSpace (Fin d))) (hK : IsCompact K) (t : AlcoveTile d) :
    t ∈ completeAlcoves hd H ε hε K hK ↔ scaledAlcove d ε t ⊆ K := Set.Finite.mem_toFinset _

theorem volume_union_completeAlcoves (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (ε : ℝ) (hε : 0 < ε) (K : Set (FloorSpace (Fin d))) (hK : IsCompact K) :
    (volume : Measure (FloorSpace (Fin d))) (⋃ t ∈ completeAlcoves hd H ε hε K hK, scaledAlcove d ε t) =
      ((completeAlcoves hd H ε hε K hK).card : ℝ≥0∞) *
        (ENNReal.ofReal ε ^ (d - 1) * floorVolume (referenceSimplex d)) := by
  rw [measure_biUnion_finset₀ (fun _ _ _ _ htu ↦ scaledAlcove_aedisjoint d H hε htu)
    (fun t _ ↦ (measurableSet_scaledAlcove d hd ε t).nullMeasurableSet)]
  simp only [volume_scaledAlcove d hd hε, Finset.sum_const, nsmul_eq_mul]

/-- Any point in the coordinatewise inner cube belongs to a complete tile.
This is the actual boundary-layer geometric step of Proposition 3.4. -/
theorem innerCube_subset_completeAlcoves (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    orthonormalFloorCube b (fun i ↦ a i + ε * (2 * (d : ℝ))) (L - 2 * (ε * (2 * (d : ℝ)))) ⊆
      ⋃ t ∈ completeAlcoves hd H ε hε (orthonormalFloorCube b a L) (isCompact_orthonormalFloorCube b a L),
        scaledAlcove d ε t := by
  intro x hx
  have hcover : x ∈ ⋃ t : AlcoveTile d, scaledAlcove d ε t := by
    rw [scaledAlcove_covers d H hε]
    exact Set.mem_univ x
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hcover
  have hfull : scaledAlcove d ε t ⊆ orthonormalFloorCube b a L := by
    intro y hy i
    have hdxy := scaledAlcove_dist_le d hd hε t hy ht
    have hn := PiLp.norm_apply_le (b.repr y - b.repr x) i
    rw [← map_sub, b.repr.norm_map] at hn
    have habs : |b.repr y i - b.repr x i| ≤ dist y x := by
      simpa only [map_sub, Real.norm_eq_abs, PiLp.sub_apply, dist_eq_norm] using hn
    have hb := abs_le.mp (habs.trans hdxy)
    have hx' := hx i
    constructor <;> linarith
  exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨(mem_completeAlcoves hd H ε hε _ _ t).mpr hfull, ht⟩⟩

/-- The actual number of distinct complete tiles. It is finite at every positive
scale by the proved local-finiteness/compactness argument. -/
def completeCubeTileCount
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L ε : ℝ) : ℕ :=
  {t : AlcoveTile d | scaledAlcove d ε t ⊆ orthonormalFloorCube b a L}.ncard

theorem completeCubeTileCount_eq_card (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L ε : ℝ) (hε : 0 < ε) :
    completeCubeTileCount b a L ε =
      (completeAlcoves hd H ε hε (orthonormalFloorCube b a L) (isCompact_orthonormalFloorCube b a L)).card :=
  Set.ncard_eq_toFinset_card _ (completeAlcoves_finite hd H hε (isCompact_orthonormalFloorCube b a L))

/-- The complete tiles fill the cube up to its elementary inner coordinate layer. -/
theorem completeCubeTile_volume_sandwich (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε)
    (hmargin : 2 * (ε * (2 * (d : ℝ))) ≤ L) :
    (L - 2 * (ε * (2 * (d : ℝ)))) ^ (d - 1) ≤
      (completeCubeTileCount b a L ε : ℝ) * ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal ∧
    (completeCubeTileCount b a L ε : ℝ) * ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal ≤
      L ^ (d - 1) := by
  let T := completeAlcoves hd H ε hε (orthonormalFloorCube b a L) (isCompact_orthonormalFloorCube b a L)
  let U := ⋃ t ∈ T, scaledAlcove d ε t
  have hsubset : U ⊆ orthonormalFloorCube b a L := by
    intro x hx
    obtain ⟨t, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ht, hx⟩ := Set.mem_iUnion.mp hx
    exact (mem_completeAlcoves hd H ε hε _ _ t).mp ht hx
  have hupper := measure_mono (μ := (volume : Measure (FloorSpace (Fin d)))) hsubset
  have hKtop : (volume : Measure (FloorSpace (Fin d))) (orthonormalFloorCube b a L) ≠ ⊤ :=
    (isCompact_orthonormalFloorCube b a L).measure_ne_top
  have hUtop := ne_top_of_le_ne_top hKtop hupper
  have hlower := measure_mono (μ := (volume : Measure (FloorSpace (Fin d))))
    (innerCube_subset_completeAlcoves hd H b a L hε)
  have hupperR := ENNReal.toReal_mono hKtop hupper
  have hlowerR := ENNReal.toReal_mono hUtop hlower
  have hUvol : (volume : Measure (FloorSpace (Fin d))) U =
      ((T.card : ℝ≥0∞)) * (ENNReal.ofReal ε ^ (d - 1) * floorVolume (referenceSimplex d)) :=
    volume_union_completeAlcoves hd H ε hε _ _
  have hUreal : ((volume : Measure (FloorSpace (Fin d))) U).toReal =
      (completeCubeTileCount b a L ε : ℝ) * ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal := by
    rw [hUvol]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le]
    rw [completeCubeTileCount_eq_card hd H b a L ε hε]
    ring
  rw [hUreal, volume_orthonormalFloorCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL] at hupperR
  change ((volume : Measure (FloorSpace (Fin d)))
      (orthonormalFloorCube b (fun i ↦ a i + ε * (2 * (d : ℝ))) (L - 2 * (ε * (2 * (d : ℝ)))))).toReal ≤
    ((volume : Measure (FloorSpace (Fin d))) U).toReal at hlowerR
  rw [hUreal, volume_orthonormalFloorCube, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hmargin)] at hlowerR
  exact ⟨hlowerR, hupperR⟩

/-- Quantitative actual cube boundary-layer error O(ε), with an explicit constant. -/
theorem completeCubeTile_boundary_layer_bound (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hsmall : ε ≤ L / (4 * (d : ℝ))) :
    0 ≤ L ^ (d - 1) - (completeCubeTileCount b a L ε : ℝ) * ε ^ (d - 1) *
      (floorVolume (referenceSimplex d)).toReal ∧
    L ^ (d - 1) - (completeCubeTileCount b a L ε : ℝ) * ε ^ (d - 1) *
      (floorVolume (referenceSimplex d)).toReal ≤
        (4 * (d : ℝ) * ((d - 1 : ℕ) : ℝ) * L ^ (d - 2)) * ε := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hmargin : 2 * (ε * (2 * (d : ℝ))) ≤ L := by
    have h := (le_div_iff₀ (show 0 < 4 * (d : ℝ) by positivity)).mp hsmall
    nlinarith
  obtain ⟨hlo, hup⟩ := completeCubeTile_volume_sandwich hd H b a hL.le hε hmargin
  have hinner : 0 ≤ L - 2 * (ε * (2 * (d : ℝ))) := sub_nonneg.mpr hmargin
  have hinnerL : L - 2 * (ε * (2 * (d : ℝ))) ≤ L := by
    linarith [mul_pos hε (show (0 : ℝ) < 2 * (d : ℝ) by positivity)]
  have habs := abs_pow_sub_pow_le (a := L) (b := L - 2 * (ε * (2 * (d : ℝ)))) (n := d - 1)
  rw [abs_of_pos hL, abs_of_nonneg hinner, max_eq_left hinnerL,
    show L - (L - 2 * (ε * (2 * (d : ℝ)))) = 2 * (ε * (2 * (d : ℝ))) by ring,
    abs_of_nonneg (by positivity : 0 ≤ 2 * (ε * (2 * (d : ℝ)))),
    show d - 1 - 1 = d - 2 by omega] at habs
  refine ⟨sub_nonneg.mpr hup, ?_⟩
  have hdiff := (le_abs_self (L ^ (d - 1) - (L - 2 * (ε * (2 * (d : ℝ)))) ^ (d - 1))).trans habs
  calc
    _ ≤ L ^ (d - 1) - (L - 2 * (ε * (2 * (d : ℝ)))) ^ (d - 1) := by linarith
    _ ≤ _ := hdiff.trans_eq (by ring)

/-- Explicit quantitative form of the source complete-tile counting error. -/
theorem completeCubeTile_count_error_bound (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hsmall : ε ≤ L / (4 * (d : ℝ))) :
    |(completeCubeTileCount b a L ε : ℝ) -
      L ^ (d - 1) / (ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal)| ≤
      (4 * (d : ℝ) * ((d - 1 : ℕ) : ℝ) * L ^ (d - 2) /
        (floorVolume (referenceSimplex d)).toReal) * ε ^ ((2 : ℝ) - (d : ℝ)) := by
  have hV := floorVolume_referenceSimplex_toReal_pos hd
  have hden : 0 < ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal :=
    mul_pos (pow_pos hε _) hV
  obtain ⟨h0, hbound⟩ := completeCubeTile_boundary_layer_bound hd H b a hL hε hsmall
  have hcount : (completeCubeTileCount b a L ε : ℝ) ≤
      L ^ (d - 1) / (ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hcount)]
  have heq : -((completeCubeTileCount b a L ε : ℝ) -
      L ^ (d - 1) / (ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal)) =
      (L ^ (d - 1) - (completeCubeTileCount b a L ε : ℝ) * ε ^ (d - 1) *
        (floorVolume (referenceSimplex d)).toReal) /
          (ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal) := by field_simp; ring
  rw [heq]
  apply (div_le_div_of_nonneg_right hbound hden.le).trans_eq
  have hexp : (2 : ℝ) - (d : ℝ) = 1 - ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    ring
  rw [hexp, Real.rpow_sub hε, Real.rpow_one, Real.rpow_natCast]
  ring

/-- Proposition 3.4's quantitative count for any fixed cube in orthonormal
coordinates, conditional only on the explicitly cited Coxeter geometry. -/
theorem completeCubeTile_count_isBigO (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    (fun ε : ℝ ↦ (completeCubeTileCount b a L ε : ℝ) -
      L ^ (d - 1) / (ε ^ (d - 1) * (floorVolume (referenceSimplex d)).toReal))
        =O[𝓝[>] (0 : ℝ)] (fun ε : ℝ ↦ ε ^ ((2 : ℝ) - (d : ℝ))) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨4 * (d : ℝ) * ((d - 1 : ℕ) : ℝ) * L ^ (d - 2) /
    (floorVolume (referenceSimplex d)).toReal, ?_⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ L / (4 * (d : ℝ)) :=
    (eventually_le_nhds (div_pos hL (by positivity))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmall
  have hεpos : 0 < ε := hε
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hεpos _)] using
    completeCubeTile_count_error_bound hd H b a hL hεpos hsmall

/-- The complete-tile volume converges to the actual cube volume. -/
theorem tendsto_completeCubeTile_volume (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun ε : ℝ ↦ (completeCubeTileCount b a L ε : ℝ) * ε ^ (d - 1) *
      (floorVolume (referenceSimplex d)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 (L ^ (d - 1))) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let C : ℝ := 4 * (d : ℝ) * ((d - 1 : ℕ) : ℝ) * L ^ (d - 2)
  have hC : 0 < C := by
    dsimp [C]
    have hm : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ L / (4 * (d : ℝ)) :=
    (eventually_le_nhds (div_pos hL (by positivity))).filter_mono nhdsWithin_le_nhds
  have hδsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < δ / C :=
    (eventually_lt_nhds (div_pos hδ hC)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall, hδsmall] with ε hε hsmall hδsmall
  have hεpos : 0 < ε := hε
  obtain ⟨h0, hb⟩ := completeCubeTile_boundary_layer_bound hd H b a hL hεpos hsmall
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg h0]
  exact hb.trans_lt (by simpa only [C, mul_comm ε] using ((lt_div_iff₀ hC).mp hδsmall))

end Antichain
