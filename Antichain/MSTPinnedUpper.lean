import Antichain.MSTGaugeBound
import Antichain.LocalRate

/-! The written minimum-spanning-tree proof of the actual pinned-volume upper
bound and the source's finite local gamma constant. -/

noncomputable section

namespace Antichain

open MeasureTheory SimpleGraph Set Finset Filter
open scoped ENNReal Topology

def mstReferenceRadius (d : ℕ) : ℝ := 4 * (d : ℝ) * Real.sqrt ((d : ℝ) - 1)
def mstPinnedUpperConstant (d : ℕ) : ℝ := 3 * mstReferenceRadius d

theorem mstPinnedUpperConstant_nonneg (d : ℕ) : 0 ≤ mstPinnedUpperConstant d := by
  unfold mstPinnedUpperConstant mstReferenceRadius
  positivity

theorem mstPinnedUpperConstant_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < mstPinnedUpperConstant d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  unfold mstPinnedUpperConstant mstReferenceRadius
  positivity

theorem symmetricFloorGauge_reference_radius {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {p : FloorSpace (Fin d)} (hp : p ∈ referenceSimplex d) :
    symmetricFloorGauge p ≤ mstReferenceRadius d := by
  have h := symmetricFloorGauge_le_euclidean hd p
  have hn := norm_le_dimension_of_mem_referenceSimplex hd hp
  have hmul := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ 2 * Real.sqrt ((d : ℝ) - 1) by positivity)
  unfold mstReferenceRadius
  nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1)]

theorem symmetricFloorGauge_reference_pair_radius {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {p q : FloorSpace (Fin d)} (hp : p ∈ referenceSimplex d) (hq : q ∈ referenceSimplex d) :
    symmetricFloorGauge (p - q) ≤ mstReferenceRadius d := by
  have h := symmetricFloorGauge_le_euclidean hd (p - q)
  have hn : ‖p - q‖ ≤ 2 * (d : ℝ) := by
    have := norm_sub_le p q
    linarith [norm_le_dimension_of_mem_referenceSimplex hd hp,
      norm_le_dimension_of_mem_referenceSimplex hd hq]
  have hmul := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ 2 * Real.sqrt ((d : ℝ) - 1) by positivity)
  unfold mstReferenceRadius
  nlinarith

/-- The actual height-fiber bound proved by the written MST argument:
minimum tree, long-edge component separation, symmetric-norm packing and a
rooted triangular height-difference map with determinant one. -/
theorem pinnedHeightFiber_referenceSimplex_mst_bound {d r : ℕ}
    (hd : 2 ≤ d) (f : Fin (r + 1) → FloorSpace (Fin d))
    (hf : ∀ j, f j ∈ referenceSimplex d) :
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) ≤
      ENNReal.ofReal (mstPinnedUpperConstant d ^ r *
        ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  let w := symmetricGaugeEdgeWeight f
  obtain ⟨T, hT⟩ := exists_minimumSpanningTree w
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  obtain ⟨σ, hroot, parent, hparent, _, _⟩ := exists_rooted_tree_order T hT.1
  have hcard : T.edgeFinset.card = r := by
    have h := hT.1.card_edgeFinset
    simp only [Fintype.card_fin] at h
    omega
  have hprod := mst_edge_product_bound hd f hT
    (show 0 ≤ mstReferenceRadius d by unfold mstReferenceRadius; positivity)
    (fun j => symmetricFloorGauge_reference_radius hd (hf j))
    (fun j k => symmetricFloorGauge_reference_pair_radius hd (hf j) (hf k)) hcard
  have hbox := pinnedHeightFiber_volume_le_parentWidth (fun j => f (σ j)) parent
  simp_rw [parentEdgeWidth_eq_symmetric_weight f σ parent] at hbox
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun j _ => symmetricGaugeEdgeWeight_nonneg f (rootedParentEdge σ parent j)),
    prod_rootedParentEdge_eq T hT.1 σ parent hparent] at hbox
  calc
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) =
        volume (pinnedHeightFiber (fun j => f (σ j))) :=
      (pinnedHeightFiber_volume_anchor_reindex f σ hroot).symm
    _ ≤ ENNReal.ofReal (∏ e ∈ T.edgeFinset, symmetricGaugeEdgeWeight f e) := hbox
    _ ≤ _ := ENNReal.ofReal_le_ofReal hprod

theorem pinnedMass_referenceSimplex_mst_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    pinnedMass (referenceSimplex d) r ≤
      floorVolume (referenceSimplex d) ^ (r + 1) *
        ENNReal.ofReal (mstPinnedUpperConstant d ^ r *
          ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
  let B := Set.univ.pi (fun _ : Fin (r + 1) => referenceSimplex d)
  have hB : MeasurableSet B :=
    MeasurableSet.univ_pi (fun _ => measurableSet_referenceSimplex d)
  rw [pinnedMass_eq_lintegral_pinnedHeightFiber (measurableSet_referenceSimplex d) r]
  calc
    (∫⁻ f in B, (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f)) ≤
        ∫⁻ _f in B, ENNReal.ofReal (mstPinnedUpperConstant d ^ r *
          ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with f hf
      exact pinnedHeightFiber_referenceSimplex_mst_bound hd f (fun j => hf j (Set.mem_univ j))
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, B,
        volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, floorVolume]
      rw [mul_comm]

theorem pinnedVolume_referenceSimplex_mst_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    pinnedVolume (referenceSimplex d) r ≤
      (floorVolume (referenceSimplex d)).toReal ^ (r + 1) * mstPinnedUpperConstant d ^ r *
        ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) := by
  have hnonneg : 0 ≤ mstPinnedUpperConstant d ^ r *
      ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) :=
    mul_nonneg (pow_nonneg (mstPinnedUpperConstant_nonneg d) r)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (floorVolume_referenceSimplex_lt_top hd).ne)
      ENNReal.ofReal_ne_top) (pinnedMass_referenceSimplex_mst_bound hd r)
  simpa only [pinnedVolume, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hnonneg, mul_assoc] using h

theorem pinnedVolume_referenceSimplex_log_mst_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    Real.log (pinnedVolume (referenceSimplex d) r) ≤
      ((r : ℝ) + 1) * Real.log (floorVolume (referenceSimplex d)).toReal +
        (r : ℝ) * Real.log (mstPinnedUpperConstant d) -
        Real.log ((r + 1).factorial : ℝ) / ((d : ℝ) - 1) := by
  have hV := floorVolume_referenceSimplex_toReal_pos hd
  have hC := mstPinnedUpperConstant_pos hd
  have hF : 0 < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have h := Real.log_le_log (pinnedVolume_referenceSimplex_pos hd r)
    (pinnedVolume_referenceSimplex_mst_bound hd r)
  rw [Real.log_mul (mul_pos (pow_pos hV _) (pow_pos hC _)).ne'
    (Real.rpow_pos_of_pos hF _).ne',
    Real.log_mul (pow_pos hV _).ne' (pow_pos hC _).ne',
    Real.log_pow, Real.log_pow, Real.log_rpow hF] at h
  have hm : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  rw [hm] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  convert h using 1
  ring

/-- The actual source local entropy sequence is uniformly bounded above.
The factorial estimate is constructed geometrically and the bounded Stirling
remainder comes from Mathlib's proved factorial theorem. -/
theorem localGammaSequence_bddAbove_mst {d : ℕ} (hd : 2 ≤ d) :
    BddAbove (Set.range (localGammaSequence d)) := by
  obtain ⟨L, hL⟩ := tendsto_log_factorial_remainder.bddBelow_range
  let V : ℝ := (floorVolume (referenceSimplex d)).toReal
  let C : ℝ := mstPinnedUpperConstant d
  have hV : 0 < V := floorVolume_referenceSimplex_toReal_pos hd
  have hm : 0 < (d : ℝ) - 1 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨Real.log V + |Real.log C| + (1 - L) / ((d : ℝ) - 1) -
    (d : ℝ) * Real.log V / ((d : ℝ) - 1), ?_⟩
  rintro _ ⟨r, rfl⟩
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hlog := pinnedVolume_referenceSimplex_log_mst_bound hd r
  change Real.log (pinnedVolume (referenceSimplex d) r) ≤
    ((r : ℝ) + 1) * Real.log V + (r : ℝ) * Real.log C -
      Real.log ((r + 1).factorial : ℝ) / ((d : ℝ) - 1) at hlog
  have hdiv := div_le_div_of_nonneg_right hlog hN.le
  have hrem : L ≤ Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1) -
      Real.log ((r : ℝ) + 1) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hL (Set.mem_range_self (r + 1))
  have hfac : (Real.log ((r : ℝ) + 1) -
      Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1)) / ((d : ℝ) - 1) ≤
      (1 - L) / ((d : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  have hratio0 : 0 ≤ (r : ℝ) / ((r : ℝ) + 1) := div_nonneg (Nat.cast_nonneg _) hN.le
  have hratio1 : (r : ℝ) / ((r : ℝ) + 1) ≤ 1 := (div_le_one hN).mpr (by linarith)
  have hCbound : ((r : ℝ) / ((r : ℝ) + 1)) * Real.log C ≤ |Real.log C| := by
    by_cases hC0 : 0 ≤ Real.log C
    · exact (mul_le_mul_of_nonneg_right hratio1 hC0).trans_eq (by simp [abs_of_nonneg hC0])
    · exact (mul_nonpos_of_nonneg_of_nonpos hratio0 (le_of_not_ge hC0)).trans (abs_nonneg _)
  unfold localGammaSequence
  change Real.log (pinnedVolume (referenceSimplex d) r) / ((r : ℝ) + 1) +
    Real.log (((r : ℝ) + 1) / V ^ d) / ((d : ℝ) - 1) ≤ _
  rw [Real.log_div hN.ne' (pow_pos hV _).ne', Real.log_pow]
  calc
    _ ≤ (((r : ℝ) + 1) * Real.log V + (r : ℝ) * Real.log C -
          Real.log ((r + 1).factorial : ℝ) / ((d : ℝ) - 1)) / ((r : ℝ) + 1) +
          (Real.log ((r : ℝ) + 1) - (d : ℝ) * Real.log V) / ((d : ℝ) - 1) :=
      add_le_add_right hdiv _
    _ = Real.log V + ((r : ℝ) / ((r : ℝ) + 1)) * Real.log C +
          (Real.log ((r : ℝ) + 1) - Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1)) /
            ((d : ℝ) - 1) - (d : ℝ) * Real.log V / ((d : ℝ) - 1) := by
      field_simp
      ring
    _ ≤ _ := by linarith


/-- Complete source Lemma 3.6 using its written MST upper bound and its written
separated-grid lower bound. No greedy insertion-radius bound is used. -/
theorem localGammaSequence_bounded_mst_source {d : ℕ} (hd : 2 ≤ d) :
    BddAbove (Set.range (localGammaSequence d)) ∧
      BddBelow (Set.range (localGammaSequence d)) :=
  ⟨localGammaSequence_bddAbove_mst hd, localGammaSequence_bddBelow hd⟩

theorem localGammaConstant_bounded_mst_source (d : ℕ) (hd : 2 ≤ d) :
    ∃ L U : ℝ, (∀ r, L ≤ localGammaSequence d r ∧ localGammaSequence d r ≤ U) ∧
      L ≤ localGammaConstant d hd ∧ localGammaConstant d hd ≤ U := by
  obtain ⟨U, hU⟩ := localGammaSequence_bddAbove_mst hd
  obtain ⟨L, hL⟩ := localGammaSequence_bddBelow hd
  refine ⟨L, U, (fun r => ⟨hL (Set.mem_range_self r), hU (Set.mem_range_self r)⟩), ?_, ?_⟩
  · apply Filter.le_limsup_of_le (localGammaSequence_bddAbove_mst hd).isBoundedUnder_of_range
    intro b hb
    obtain ⟨r, hr⟩ := hb.exists
    exact (hL (Set.mem_range_self r)).trans hr
  · exact Filter.limsup_le_of_le
      (localGammaSequence_bddBelow hd).isBoundedUnder_of_range.isCobounded_flip
      (Filter.Eventually.of_forall (fun r => hU (Set.mem_range_self r)))

end Antichain
