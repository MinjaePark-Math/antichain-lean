import Antichain.PinnedVolumeBounds
import Antichain.HeightCoordinates
import Antichain.GridBalls
import Antichain.PinnedVolumeUpper
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Lower bounds for actual pinned volumes from separated measurable floor sets.
The factorial multiplicity is a proved disjoint union over label permutations. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal Topology

variable {ι : Type*} [Fintype ι]

def assignedFloorBox {r : ℕ} (U : Fin (r + 1) → Set (FloorSpace ι))
    (σ : Equiv.Perm (Fin (r + 1))) : Set (Fin (r + 1) → FloorSpace ι) :=
  Set.univ.pi (fun j ↦ U (σ j))

def assignedFloorUnion {r : ℕ} (U : Fin (r + 1) → Set (FloorSpace ι)) :
    Set (Fin (r + 1) → FloorSpace ι) := ⋃ σ : Equiv.Perm (Fin (r + 1)), assignedFloorBox U σ

def centeredPinnedHeightBox (r : ℕ) (a : ℝ) : Set (Fin r → ℝ) :=
  Set.univ.pi (fun _ ↦ Icc (-a) a)

theorem measurableSet_assignedFloorBox {r : ℕ} (U : Fin (r + 1) → Set (FloorSpace ι))
    (hU : ∀ j, MeasurableSet (U j)) (σ : Equiv.Perm (Fin (r + 1))) :
    MeasurableSet (assignedFloorBox U σ) := MeasurableSet.univ_pi (fun j ↦ hU (σ j))

theorem volume_assignedFloorBox {r : ℕ} (U : Fin (r + 1) → Set (FloorSpace ι))
    (σ : Equiv.Perm (Fin (r + 1))) :
    volume (assignedFloorBox U σ) = ∏ j, (volume : Measure (FloorSpace ι)) (U j) := by
  rw [assignedFloorBox, volume_pi_pi]
  exact Equiv.prod_comp σ (fun j ↦ (volume : Measure (FloorSpace ι)) (U j))

theorem assignedFloorBox_pairwiseDisjoint {r : ℕ} (U : Fin (r + 1) → Set (FloorSpace ι))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j))) : Pairwise (fun σ τ : Equiv.Perm (Fin (r + 1)) ↦
      Disjoint (assignedFloorBox U σ) (assignedFloorBox U τ)) := by
  intro σ τ hστ
  apply Set.disjoint_left.mpr
  intro f hfσ hfτ
  apply hστ
  apply Equiv.ext
  intro j
  by_contra hneq
  exact Set.disjoint_left.mp (hdisj hneq) (hfσ j (mem_univ j)) (hfτ j (mem_univ j))

/-- The full N! label factor is exact, rather than an assumed entropy term. -/
theorem volume_assignedFloorUnion {r : ℕ} (U : Fin (r + 1) → Set (FloorSpace ι))
    (hU : ∀ j, MeasurableSet (U j))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j))) :
    volume (assignedFloorUnion U) =
      ((r + 1).factorial : ℝ≥0∞) * ∏ j, (volume : Measure (FloorSpace ι)) (U j) := by
  rw [assignedFloorUnion, measure_iUnion (assignedFloorBox_pairwiseDisjoint U hdisj)
    (measurableSet_assignedFloorBox U hU)]
  simp only [volume_assignedFloorBox, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem volume_centeredPinnedHeightBox (r : ℕ) (a : ℝ) :
    (volume : Measure (Fin r → ℝ)) (centeredPinnedHeightBox r a) =
      ENNReal.ofReal (2 * a) ^ r := by
  rw [centeredPinnedHeightBox, volume_pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable [Nonempty ι]

/-- Separated zero-sum floor points remain an antichain throughout a centered
height box. The sharp gauge lower bound supplies the actual geometric margin. -/
theorem antichain_of_separated_floors_height_box {r : ℕ}
    (hd : 2 ≤ Fintype.card ι) (f : Fin (r + 1) → FloorSpace ι) {ρ a : ℝ}
    (ha : 0 ≤ a) (hwidth : 2 * a ≤ ρ / Real.sqrt ((Fintype.card ι : ℝ) - 1))
    (hsep : Pairwise (fun j k ↦ ρ ≤ dist (f j) (f k)))
    {h : Fin r → ℝ} (hh : h ∈ centeredPinnedHeightBox r a) :
    IsAntichain (pinnedPointCloud (f, h)) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hdR : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hs : 0 < Real.sqrt ((Fintype.card ι : ℝ) - 1) :=
    Real.sqrt_pos.mpr (by linarith)
  have hb (j : Fin (r + 1)) :
      -a ≤ (Fin.cons (0 : ℝ) h : Fin (r + 1) → ℝ) j ∧
        (Fin.cons (0 : ℝ) h : Fin (r + 1) → ℝ) j ≤ a := by
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp only [Fin.cons_zero]
      exact ⟨by linarith, ha⟩
    · exact hh k (mem_univ k)
  apply (isAntichain_iff_height_constraints _ (Real.sqrt_pos.mpr hcard)
    (fun j i ↦ (f j).val i) (Fin.cons (0 : ℝ) h)).mpr
  intro j k
  by_cases hjk : j = k
  · subst k
    simp only [sub_self, heightGauge_zero]
    exact le_rfl
  · have hz : ∑ i, ((f j).val i - (f k).val i) = 0 := by
      have hj : ∑ i, (f j).val i = 0 := (f j).property
      have hk : ∑ i, (f k).val i = 0 := (f k).property
      rw [Finset.sum_sub_distrib, hj, hk, sub_self]
    have hg := (heightGauge_norm_bounds_euclidean hd _ hz).1
    change ‖f j - f k‖ / Real.sqrt ((Fintype.card ι : ℝ) - 1) ≤
      heightGauge (Real.sqrt (Fintype.card ι : ℝ))
        (fun i ↦ (f j).val i - (f k).val i) at hg
    have hρ := div_le_div_of_nonneg_right (hsep hjk) hs.le
    rw [dist_eq_norm] at hρ
    have hj := hb j
    have hk := hb k
    linarith

/-- A concrete product subset of the actual pinned event, after all permutations
of the separated floor regions have been included. -/
theorem separated_floor_product_subset_pinned {r : ℕ}
    (hd : 2 ≤ Fintype.card ι) (B : Set (FloorSpace ι))
    (U : Fin (r + 1) → Set (FloorSpace ι)) (hUB : ∀ j, U j ⊆ B)
    {ρ a : ℝ} (ha : 0 ≤ a) (hwidth : 2 * a ≤ ρ / Real.sqrt ((Fintype.card ι : ℝ) - 1))
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, ρ ≤ dist u v) :
    assignedFloorUnion U ×ˢ centeredPinnedHeightBox r a ⊆ pinnedAntichainSet B r := by
  rintro ⟨f, h⟩ ⟨hf, hh⟩
  obtain ⟨σ, hf⟩ := Set.mem_iUnion.mp hf
  refine ⟨fun j ↦ hUB (σ j) (hf j (mem_univ j)), ?_⟩
  apply antichain_of_separated_floors_height_box hd f ha hwidth ?_ hh
  intro j k hjk
  exact hsep (σ j) (σ k) (fun heq ↦ hjk (σ.injective heq))
    (f j) (hf j (mem_univ j)) (f k) (hf k (mem_univ k))

/-- A genuine lower bound for the actual pinned mass, including the exact
factorial label multiplicity and the r-dimensional height-box factor. -/
theorem pinnedMass_lower_of_separated_sets {r : ℕ}
    (hd : 2 ≤ Fintype.card ι) (B : Set (FloorSpace ι))
    (U : Fin (r + 1) → Set (FloorSpace ι)) (hU : ∀ j, MeasurableSet (U j))
    (hUB : ∀ j, U j ⊆ B) (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    {ρ a : ℝ} (ha : 0 ≤ a) (hwidth : 2 * a ≤ ρ / Real.sqrt ((Fintype.card ι : ℝ) - 1))
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, ρ ≤ dist u v) :
    ((r + 1).factorial : ℝ≥0∞) * (∏ j, (volume : Measure (FloorSpace ι)) (U j)) *
        ENNReal.ofReal (2 * a) ^ r ≤ pinnedMass B r := by
  have h := measure_mono (μ := (volume : Measure (PinnedConfiguration ι r)))
    (separated_floor_product_subset_pinned hd B U hUB ha hwidth hsep)
  change (volume : Measure (Fin (r + 1) → FloorSpace ι)).prod
      (volume : Measure (Fin r → ℝ)) (assignedFloorUnion U ×ˢ centeredPinnedHeightBox r a) ≤
        pinnedMass B r at h
  rw [Measure.prod_prod, volume_assignedFloorUnion U hU hdisj, volume_centeredPinnedHeightBox] at h
  exact h

/-- The actual simplex model has a uniform factorial-grid lower bound. Both
positive constants are constructed from its native interior ball and unit-ball
Euclidean volume, and are independent of the sample size. -/
theorem pinnedVolume_referenceSimplex_grid_lower {d : ℕ} (hd : 2 ≤ d) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ r : ℕ,
      ((r + 1).factorial : ℝ) * (A / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) *
        (B * (((r + 1 : ℕ) : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹))) ^ r ≤
          pinnedVolume (referenceSimplex d) r := by
  letI : NeZero d := ⟨by omega⟩
  have hm : 0 < d - 1 := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hdim : Module.finrank ℝ (FloorSpace (Fin d)) = d - 1 := by
    simpa only [Fintype.card_fin] using (finrank_floorSpace (ι := Fin d))
  obtain ⟨c, hc, hgrid⟩ := exists_referenceSimplex_grid_balls hd
  let V : ℝ≥0∞ := (volume : Measure (FloorSpace (Fin d))) (Metric.ball 0 1)
  have hVpos : 0 < V := Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self zero_lt_one⟩
  have hVtop : V ≠ ⊤ := ne_of_lt
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : FloorSpace (Fin d)) 1).measure_lt_top)
  let A : ℝ := V.toReal * c ^ (d - 1)
  let B : ℝ := 2 * c / Real.sqrt ((d : ℝ) - 1)
  have hA : 0 < A := mul_pos (ENNReal.toReal_pos hVpos.ne' hVtop) (pow_pos hc _)
  have hB : 0 < B := div_pos (by positivity) hq
  refine ⟨A, B, hA, hB, fun r ↦ ?_⟩
  obtain ⟨z, hinside, hcenters⟩ := hgrid (r + 1) (by omega)
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  let s : ℝ := c * N ^ (-((d - 1 : ℕ) : ℝ)⁻¹)
  have hs : 0 < s := mul_pos hc (Real.rpow_pos_of_pos hN _)
  let U : Fin (r + 1) → Set (FloorSpace (Fin d)) := fun i ↦ Metric.ball (z i) s
  have hUmeas : ∀ i, MeasurableSet (U i) := fun _ ↦ measurableSet_ball
  have hUsep : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, 4 * s ≤ dist u v := by
    intro i j hij u hu v hv
    have hcen : 8 * s ≤ dist (z i) (z j) := hcenters hij
    have htri := dist_triangle (z i) u (z j)
    have htri' := dist_triangle u v (z j)
    have hu' : dist (z i) u < s := by simpa only [dist_comm] using hu
    have hv' : dist v (z j) < s := hv
    linarith
  have hUdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro u hui huj
    have h := hUsep i j hij u hui u huj
    rw [dist_self] at h
    linarith
  let a : ℝ := s / Real.sqrt ((d : ℝ) - 1)
  have ha : 0 ≤ a := (div_pos hs hq).le
  have hwidth : 2 * a ≤ (4 * s) / Real.sqrt ((Fintype.card (Fin d) : ℝ) - 1) := by
    simp only [Fintype.card_fin]
    dsimp [a]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith : 2 * s ≤ 4 * s) hq.le
  have hlow := pinnedMass_lower_of_separated_sets (by simpa only [Fintype.card_fin] using hd)
    (referenceSimplex d) U hUmeas (fun i ↦ hinside i) hUdisj ha hwidth hUsep
  have hreal := ENNReal.toReal_mono (pinnedMass_referenceSimplex_lt_top hd r).ne hlow
  have hspow : s ^ (d - 1) = c ^ (d - 1) / N := by
    dsimp [s]
    rw [mul_pow, Real.rpow_neg hN.le, inv_pow, Real.rpow_inv_natCast_pow hN.le hm.ne']
    ring
  have hUreal (i : Fin (r + 1)) : ((volume : Measure (FloorSpace (Fin d))) (U i)).toReal = A / N := by
    dsimp [U]
    rw [Measure.addHaar_ball_of_pos volume _ hs, hdim,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le _), hspow]
    dsimp [A, V]
    ring
  have haeq : 2 * a = B * N ^ (-((d - 1 : ℕ) : ℝ)⁻¹) := by dsimp [a, B, s]; ring
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * a)] at hreal
  simp_rw [hUreal] at hreal
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, haeq] at hreal
  exact hreal

/-- Logarithmic form of the actual factorial-grid lower bound. -/
theorem pinnedVolume_referenceSimplex_log_grid_lower {d : ℕ} (hd : 2 ≤ d) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ r : ℕ,
      Real.log ((r + 1).factorial : ℝ) + ((r : ℝ) + 1) * Real.log A -
        ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) + (r : ℝ) * Real.log B -
        (r : ℝ) / ((d : ℝ) - 1) * Real.log ((r : ℝ) + 1) ≤
          Real.log (pinnedVolume (referenceSimplex d) r) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := pinnedVolume_referenceSimplex_grid_lower hd
  refine ⟨A, B, hA, hB, fun r ↦ ?_⟩
  have hN : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hF : (0 : ℝ) < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hpow : 0 < ((r + 1 : ℕ) : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hN _
  have h := Real.log_le_log (mul_pos (mul_pos hF (pow_pos (div_pos hA hN) _))
    (pow_pos (mul_pos hB hpow) _)) (hbound r)
  rw [Real.log_mul (mul_pos hF (pow_pos (div_pos hA hN) _)).ne'
      (pow_pos (mul_pos hB hpow) _).ne',
    Real.log_mul hF.ne' (pow_pos (div_pos hA hN) _).ne',
    Real.log_pow, Real.log_pow, Real.log_div hA.ne' hN.ne',
    Real.log_mul hB.ne' hpow.ne', Real.log_rpow hN] at h
  have hm : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  rw [hm] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  convert h using 1; ring

/-- The actual local entropy sequence is bounded below, completing the two-sided
finiteness needed before defining its real limsup gamma_d. -/
theorem localGammaSequence_bddBelow {d : ℕ} (hd : 2 ≤ d) :
    BddBelow (Set.range (localGammaSequence d)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := pinnedVolume_referenceSimplex_log_grid_lower hd
  obtain ⟨L, hL⟩ := tendsto_log_factorial_remainder.bddBelow_range
  let V : ℝ := (floorVolume (referenceSimplex d)).toReal
  have hV : 0 < V := floorVolume_referenceSimplex_toReal_pos hd
  have hm : 0 < (d : ℝ) - 1 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨Real.log A + L - 1 - |Real.log B| - (d : ℝ) * Real.log V / ((d : ℝ) - 1), ?_⟩
  rintro _ ⟨r, rfl⟩
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hlogN : 0 ≤ Real.log ((r : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) r])
  have hrem : L ≤ Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1) -
      Real.log ((r : ℝ) + 1) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hL (Set.mem_range_self (r + 1))
  have hratio0 : 0 ≤ (r : ℝ) / ((r : ℝ) + 1) := div_nonneg (Nat.cast_nonneg _) hN.le
  have hratio1 : (r : ℝ) / ((r : ℝ) + 1) ≤ 1 := (div_le_one hN).mpr (by linarith)
  have hBbound : -|Real.log B| ≤ ((r : ℝ) / ((r : ℝ) + 1)) * Real.log B := by
    have h1 := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log B)) hratio0
    have h2 := mul_le_mul_of_nonneg_right hratio1 (abs_nonneg (Real.log B))
    nlinarith
  have hnonneg : 0 ≤ Real.log ((r : ℝ) + 1) / (((d : ℝ) - 1) * ((r : ℝ) + 1)) :=
    div_nonneg hlogN (mul_nonneg hm.le hN.le)
  have hdiv := div_le_div_of_nonneg_right (hbound r) hN.le
  unfold localGammaSequence
  change _ ≤ Real.log (pinnedVolume (referenceSimplex d) r) / ((r : ℝ) + 1) +
    Real.log (((r : ℝ) + 1) / V ^ d) / ((d : ℝ) - 1)
  rw [Real.log_div hN.ne' (pow_pos hV _).ne', Real.log_pow]
  calc
    _ ≤ Real.log A + (Real.log ((r + 1).factorial : ℝ) / ((r : ℝ) + 1) -
          Real.log ((r : ℝ) + 1) + 1) - 1 +
          ((r : ℝ) / ((r : ℝ) + 1)) * Real.log B +
          Real.log ((r : ℝ) + 1) / (((d : ℝ) - 1) * ((r : ℝ) + 1)) -
          (d : ℝ) * Real.log V / ((d : ℝ) - 1) := by linarith
    _ = (Real.log ((r + 1).factorial : ℝ) + ((r : ℝ) + 1) * Real.log A -
          ((r : ℝ) + 1) * Real.log ((r : ℝ) + 1) + (r : ℝ) * Real.log B -
          (r : ℝ) / ((d : ℝ) - 1) * Real.log ((r : ℝ) + 1)) / ((r : ℝ) + 1) +
          (Real.log ((r : ℝ) + 1) - (d : ℝ) * Real.log V) / ((d : ℝ) - 1) := by
      field_simp
      ring
    _ ≤ _ := add_le_add_right hdiv _

/-- The source's local logarithmic lower entropy bound for every positive
sample size N=r+1, with a constant depending only on the dimension. -/
theorem pinnedVolume_referenceSimplex_log_lower {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      -(((r : ℝ) + 1) / ((d : ℝ) - 1)) * Real.log ((r : ℝ) + 1) -
        C * ((r : ℝ) + 1) ≤ Real.log (pinnedVolume (referenceSimplex d) r) := by
  obtain ⟨L, hL⟩ := localGammaSequence_bddBelow hd
  let V : ℝ := (floorVolume (referenceSimplex d)).toReal
  have hV : 0 < V := floorVolume_referenceSimplex_toReal_pos hd
  let K : ℝ := L + (d : ℝ) * Real.log V / ((d : ℝ) - 1)
  let C : ℝ := |K| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun r ↦ ?_⟩
  have hN : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hl := hL (Set.mem_range_self r)
  unfold localGammaSequence at hl
  change L ≤ Real.log (pinnedVolume (referenceSimplex d) r) / ((r : ℝ) + 1) +
    Real.log (((r : ℝ) + 1) / V ^ d) / ((d : ℝ) - 1) at hl
  rw [Real.log_div hN.ne' (pow_pos hV _).ne', Real.log_pow] at hl
  have hnorm : K - Real.log ((r : ℝ) + 1) / ((d : ℝ) - 1) ≤
      Real.log (pinnedVolume (referenceSimplex d) r) / ((r : ℝ) + 1) := by
    dsimp [K]
    simp only [sub_div] at hl
    linarith
  have hmul := (le_div_iff₀ hN).mp hnorm
  have hK : -C ≤ K := by dsimp [C]; linarith [neg_abs_le K]
  calc
    _ = (-C - Real.log ((r : ℝ) + 1) / ((d : ℝ) - 1)) * ((r : ℝ) + 1) := by ring
    _ ≤ (K - Real.log ((r : ℝ) + 1) / ((d : ℝ) - 1)) * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hN.le
    _ ≤ _ := hmul

end Antichain
