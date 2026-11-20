import Antichain.ParentHeightCoordinates
import Antichain.GreedyPacking
import Antichain.PinnedVolumeBounds
import Antichain.SeriesGrowth
import Antichain.MSTGaugeBound
import Antichain.MSTLargestEdges
import Antichain.ParentHeightFubini

/-! Sharp actual pinned-volume upper bounds from the written minimum-spanning-tree argument. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset Filter
open scoped ENNReal Topology

def anchorFreePermutation {r : ℕ} (e : Fin (r + 1) ≃ Fin (r + 1)) (he : e 0 = 0) :
    Fin r ≃ Fin r where
  toFun j := (e j.succ).pred (by
    intro hz
    have h := e.injective (hz.trans he.symm)
    exact Fin.succ_ne_zero j h)
  invFun j := (e.symm j.succ).pred (by
    intro hz
    have h := congrArg e hz
    simp only [e.apply_symm_apply, he] at h
    exact Fin.succ_ne_zero j h)
  left_inv j := by
    apply Fin.succ_inj.mp
    simp only [Fin.succ_pred, e.symm_apply_apply]
  right_inv j := by
    apply Fin.succ_inj.mp
    simp only [Fin.succ_pred, e.apply_symm_apply]

@[simp] theorem anchorFreePermutation_succ {r : ℕ}
    (e : Fin (r + 1) ≃ Fin (r + 1)) (he : e 0 = 0) (j : Fin r) :
    (anchorFreePermutation e he j).succ = e j.succ :=
  Fin.succ_pred (e j.succ) (by
    intro hz
    exact Fin.succ_ne_zero j (e.injective (hz.trans he.symm)))

def anchorHeightReindex {r : ℕ} (e : Fin (r + 1) ≃ Fin (r + 1)) (he : e 0 = 0)
    (h : Fin r → ℝ) : Fin r → ℝ := fun j => h (anchorFreePermutation e he j)

theorem anchorHeightReindex_measurePreserving {r : ℕ}
    (e : Fin (r + 1) ≃ Fin (r + 1)) (he : e 0 = 0) :
    MeasurePreserving (anchorHeightReindex e he) (volume : Measure (Fin r → ℝ)) volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℝ)
    (anchorFreePermutation e he).symm
  convert h using 1
  funext h j
  simp only [anchorHeightReindex, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast, Equiv.symm_symm, cast_eq]

theorem isAntichain_labelEquiv_iff {κ η ι : Type*} (e : κ ≃ η) (x : η → ι → ℝ) :
    IsAntichain (fun j => x (e j)) ↔ IsAntichain x := by
  constructor
  · intro h j k hjk
    have hs := h (e.symm j) (e.symm k) (fun heq => hjk (e.symm.injective heq))
    simpa only [e.apply_symm_apply] using hs
  · intro h j k hjk
    exact h (e j) (e k) (fun heq => hjk (e.injective heq))

theorem zeroCons_anchorHeightReindex {r : ℕ}
    (e : Fin (r + 1) ≃ Fin (r + 1)) (he : e 0 = 0) (h : Fin r → ℝ) :
    (Fin.cons (0 : ℝ) (anchorHeightReindex e he h) : Fin (r + 1) → ℝ) =
      fun j => (Fin.cons (0 : ℝ) h : Fin (r + 1) → ℝ) (e j) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [he]
  · rw [← anchorFreePermutation_succ e he k]
    rfl

theorem anchorHeightReindex_mem_pinnedHeightFiber_iff
    {ι : Type*} [Fintype ι] {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (e : Fin (r + 1) ≃ Fin (r + 1)) (he : e 0 = 0) (h : Fin r → ℝ) :
    anchorHeightReindex e he h ∈ pinnedHeightFiber (fun j => f (e j)) ↔
      h ∈ pinnedHeightFiber f := by
  have hcloud : pinnedPointCloud ((fun j => f (e j)), anchorHeightReindex e he h) =
      fun j => pinnedPointCloud (f, h) (e j) := by
    funext j i
    simp only [pinnedPointCloud, pinnedHeights, zeroCons_anchorHeightReindex]
  change IsAntichain _ ↔ IsAntichain _
  rw [hcloud]
  exact isAntichain_labelEquiv_iff e _

theorem pinnedHeightFiber_volume_anchor_reindex
    {ι : Type*} [Fintype ι] {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (e : Fin (r + 1) ≃ Fin (r + 1)) (he : e 0 = 0) :
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber (fun j => f (e j))) =
      volume (pinnedHeightFiber f) := by
  have h := (anchorHeightReindex_measurePreserving e he).measure_preimage
    (measurableSet_pinnedHeightFiber (fun j => f (e j))).nullMeasurableSet
  have hpre : anchorHeightReindex e he ⁻¹' pinnedHeightFiber (fun j => f (e j)) =
      pinnedHeightFiber f := Set.ext (anchorHeightReindex_mem_pinnedHeightFiber_iff f e he)
  rw [hpre] at h
  exact h.symm

/-- A uniform edge constant for the proved minimum-spanning-tree packing bound. -/
def pinnedUpperEdgeConstant (d : ℕ) : ℝ := 8 * (d : ℝ) * Real.sqrt ((d : ℝ) - 1)

theorem pinnedUpperEdgeConstant_nonneg (d : ℕ) : 0 ≤ pinnedUpperEdgeConstant d := by
  unfold pinnedUpperEdgeConstant
  positivity

theorem pinnedUpperEdgeConstant_pos {d : ℕ} (hd : 2 ≤ d) : 0 < pinnedUpperEdgeConstant d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold pinnedUpperEdgeConstant
  exact mul_pos (by positivity) (Real.sqrt_pos.mpr (by linarith))

/-- The source local rate gamma_(d,r+1), indexed by the r free pinned heights. -/
def localGammaSequence (d r : ℕ) : ℝ :=
  Real.log (pinnedVolume (referenceSimplex d) r) / ((r : ℝ) + 1) +
    Real.log (((r : ℝ) + 1) / ((floorVolume (referenceSimplex d)).toReal ^ d)) / ((d : ℝ) - 1)

/-- The full factorial upper bound for every floor tuple in the actual
simplex, using an actual minimum spanning tree in the symmetric gauge norm,
its exact largest-edge component packing, and leaf-to-root Fubini integration.
Repeated floor positions are allowed. -/
theorem pinnedHeightFiber_referenceSimplex_factorial_bound {d r : ℕ}
    (hd : 2 ≤ d) (f : Fin (r + 1) → FloorSpace (Fin d))
    (hf : ∀ j, f j ∈ referenceSimplex d) :
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) ≤
      ENNReal.ofReal (pinnedUpperEdgeConstant d ^ r *
        ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  let w := symmetricGaugeEdgeWeight f
  obtain ⟨T, hT⟩ := exists_minimumSpanningTree w
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  obtain ⟨e, he, parent, hparent, _, _⟩ := exists_rooted_tree_order T hT.1
  have hcard : T.edgeFinset.card = r := by
    have h := hT.1.card_edgeFinset
    simp only [Fintype.card_fin] at h
    omega
  have hprod := mst_edge_product_bound_largest hd f hT
    (show 0 ≤ 2 * Real.sqrt (d : ℝ) by positivity)
    (fun j => (symmetricFloorGauge_le_sqrt_of_mem_reference (hf j)).trans
      (by linarith [Real.sqrt_nonneg (d : ℝ)]))
    (fun j k => symmetricFloorGauge_pair_le_two_sqrt (hf j) (hf k)) hcard
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : Real.sqrt (d : ℝ) ≤ d := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hK : 1 ≤ Real.sqrt ((d : ℝ) - 1) := Real.one_le_sqrt.mpr (by linarith)
  have hconstant : 3 * (2 * Real.sqrt (d : ℝ)) ≤ pinnedUpperEdgeConstant d := by
    have hmul := mul_le_mul_of_nonneg_left hK (show 0 ≤ 8 * (d : ℝ) by positivity)
    unfold pinnedUpperEdgeConstant
    nlinarith
  have hfull := hprod.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ 3 * (2 * Real.sqrt (d : ℝ))) hconstant r)
    (Real.rpow_nonneg (by positivity : 0 ≤ ((r + 1).factorial : ℝ)) _))
  have hbox := pinnedHeightFiber_volume_le_parentWidth_fubini (fun j => f (e j)) parent
  simp_rw [parentEdgeWidth_eq_symmetric_weight f e parent] at hbox
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun j _ => symmetricGaugeEdgeWeight_nonneg f (rootedParentEdge e parent j)),
    prod_rootedParentEdge_eq T hT.1 e parent hparent] at hbox
  calc
    (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) =
        volume (pinnedHeightFiber (fun j => f (e j))) :=
      (pinnedHeightFiber_volume_anchor_reindex f e he).symm
    _ ≤ ENNReal.ofReal (∏ a ∈ T.edgeFinset, symmetricGaugeEdgeWeight f a) := hbox
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfull

/-- The source's sharp local upper estimate for the actual pinned mass. -/
theorem pinnedMass_referenceSimplex_factorial_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    pinnedMass (referenceSimplex d) r ≤
      floorVolume (referenceSimplex d) ^ (r + 1) *
        ENNReal.ofReal (pinnedUpperEdgeConstant d ^ r *
          ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
  let B := Set.univ.pi (fun _ : Fin (r + 1) => referenceSimplex d)
  have hB : MeasurableSet B :=
    MeasurableSet.univ_pi (fun _ => measurableSet_referenceSimplex d)
  rw [pinnedMass_eq_lintegral_pinnedHeightFiber (measurableSet_referenceSimplex d) r]
  calc
    (∫⁻ f in B, (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f)) ≤
        ∫⁻ _f in B, ENNReal.ofReal (pinnedUpperEdgeConstant d ^ r *
          ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with f hf
      exact pinnedHeightFiber_referenceSimplex_factorial_bound hd f (fun j => hf j (Set.mem_univ j))
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, B,
        volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, floorVolume]
      rw [mul_comm]

theorem pinnedVolume_referenceSimplex_factorial_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    pinnedVolume (referenceSimplex d) r ≤
      (floorVolume (referenceSimplex d)).toReal ^ (r + 1) * pinnedUpperEdgeConstant d ^ r *
        ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) := by
  have hnonneg : 0 ≤ pinnedUpperEdgeConstant d ^ r *
      ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) :=
    mul_nonneg (pow_nonneg (pinnedUpperEdgeConstant_nonneg d) r)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (floorVolume_referenceSimplex_lt_top hd).ne)
      ENNReal.ofReal_ne_top) (pinnedMass_referenceSimplex_factorial_bound hd r)
  simpa only [pinnedVolume, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hnonneg, mul_assoc] using h

theorem pinnedVolume_referenceSimplex_log_factorial_bound {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    Real.log (pinnedVolume (referenceSimplex d) r) ≤
      ((r : ℝ) + 1) * Real.log (floorVolume (referenceSimplex d)).toReal +
        (r : ℝ) * Real.log (pinnedUpperEdgeConstant d) -
        Real.log ((r + 1).factorial : ℝ) / ((d : ℝ) - 1) := by
  have hV := floorVolume_referenceSimplex_toReal_pos hd
  have hC := pinnedUpperEdgeConstant_pos hd
  have hF : 0 < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have h := Real.log_le_log (pinnedVolume_referenceSimplex_pos hd r)
    (pinnedVolume_referenceSimplex_factorial_bound hd r)
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
theorem localGammaSequence_bddAbove {d : ℕ} (hd : 2 ≤ d) :
    BddAbove (Set.range (localGammaSequence d)) := by
  obtain ⟨L, hL⟩ := tendsto_log_factorial_remainder.bddBelow_range
  let V : ℝ := (floorVolume (referenceSimplex d)).toReal
  let C : ℝ := pinnedUpperEdgeConstant d
  have hV : 0 < V := floorVolume_referenceSimplex_toReal_pos hd
  have hm : 0 < (d : ℝ) - 1 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨Real.log V + |Real.log C| + (1 - L) / ((d : ℝ) - 1) -
    (d : ℝ) * Real.log V / ((d : ℝ) - 1), ?_⟩
  rintro _ ⟨r, rfl⟩
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hlog := pinnedVolume_referenceSimplex_log_factorial_bound hd r
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

end Antichain
