import Antichain.SourceGaugeCalculations
import Antichain.BoundaryMatching
import Antichain.GreedyPacking
import Antichain.TreeComponentCount

/-! Packing in the actual symmetrized gauge norm, as in the written MST proof. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset Metric
open scoped ENNReal Topology Pointwise

variable {d : ℕ} [NeZero d]

theorem symmetricFloorGauge_eq_costs (u : FloorSpace (Fin d)) :
    symmetricFloorGauge u = nativeFloorCost u 0 + nativeFloorCost 0 u := by
  simp [symmetricFloorGauge, nativeFloorCost]

theorem symmetricFloorGauge_continuous :
    Continuous (symmetricFloorGauge (d := d)) := by
  have h1 := (nativeFloorCost_continuous (d := d)).comp
    (continuous_id.prodMk (continuous_const : Continuous
      (fun _ : FloorSpace (Fin d) => (0 : FloorSpace (Fin d)))))
  have h2 := (nativeFloorCost_continuous (d := d)).comp
    ((continuous_const : Continuous
      (fun _ : FloorSpace (Fin d) => (0 : FloorSpace (Fin d)))).prodMk continuous_id)
  convert h1.add h2 using 1
  funext u
  exact symmetricFloorGauge_eq_costs u

theorem symmetricFloorGauge_le_euclidean (hd : 2 ≤ d) (u : FloorSpace (Fin d)) :
    symmetricFloorGauge u ≤ 2 * Real.sqrt ((d : ℝ) - 1) * ‖u‖ := by
  rw [symmetricFloorGauge_eq_costs]
  have h1 := nativeFloorCost_le_norm hd u 0
  have h2 := nativeFloorCost_le_norm hd 0 u
  simp only [sub_zero, zero_sub, norm_neg] at h1 h2
  linarith

theorem euclidean_le_symmetricFloorGauge (hd : 2 ≤ d) (u : FloorSpace (Fin d)) :
    ‖u‖ / Real.sqrt ((d : ℝ) - 1) ≤ symmetricFloorGauge u := by
  rw [symmetricFloorGauge_eq_costs]
  have hlo : ‖u‖ / Real.sqrt ((d : ℝ) - 1) ≤ nativeFloorCost u 0 := by
    simpa only [sub_zero] using norm_div_sqrt_le_nativeFloorCost hd u 0
  exact hlo.trans
    (le_add_of_nonneg_right (nativeFloorCost_nonneg 0 u))

def symmetricGaugeBall (u : FloorSpace (Fin d)) (r : ℝ) : Set (FloorSpace (Fin d)) :=
  {x | symmetricFloorGauge (x - u) < r}

theorem isOpen_symmetricGaugeBall (u : FloorSpace (Fin d)) (r : ℝ) :
    IsOpen (symmetricGaugeBall u r) :=
  isOpen_lt (symmetricFloorGauge_continuous.comp (continuous_id.sub continuous_const)) continuous_const

theorem symmetricGaugeBall_unit_pos :
    0 < (volume : Measure (FloorSpace (Fin d))) (symmetricGaugeBall 0 1) := by
  apply (isOpen_symmetricGaugeBall (d := d) 0 1).measure_pos volume
  exact ⟨0, by simp [symmetricGaugeBall]⟩

theorem symmetricGaugeBall_unit_lt_top (hd : 2 ≤ d) :
    (volume : Measure (FloorSpace (Fin d))) (symmetricGaugeBall 0 1) < ⊤ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  apply (measure_mono (show symmetricGaugeBall (0 : FloorSpace (Fin d)) 1 ⊆
      closedBall 0 (Real.sqrt ((d : ℝ) - 1)) from ?_)).trans_lt
    (isCompact_closedBall _ _).measure_lt_top
  intro u hu
  have hlow := euclidean_le_symmetricFloorGauge hd u
  have hhigh : symmetricFloorGauge u < 1 := by simpa only [symmetricGaugeBall, sub_zero] using hu
  rw [mem_closedBall, dist_zero_right]
  exact ((div_lt_iff₀ hK).mp (hlow.trans_lt hhigh)).le.trans_eq (by ring)

theorem symmetricGaugeBall_center_volume (u : FloorSpace (Fin d)) (r : ℝ) :
    (volume : Measure (FloorSpace (Fin d))) (symmetricGaugeBall u r) =
      volume (symmetricGaugeBall (0 : FloorSpace (Fin d)) r) := by
  have hset : symmetricGaugeBall (0 : FloorSpace (Fin d)) r =
      (fun x => u + x) ⁻¹' symmetricGaugeBall u r := by
    ext x
    simp [symmetricGaugeBall]
  rw [hset, measure_preimage_add]

theorem symmetricGaugeBall_zero_smul {r : ℝ} (hr : 0 < r) :
    symmetricGaugeBall (0 : FloorSpace (Fin d)) r =
      r • symmetricGaugeBall (0 : FloorSpace (Fin d)) 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨r⁻¹ • x, ?_, by simp [hr.ne']⟩
    change symmetricFloorGauge (r⁻¹ • x - 0) < 1
    rw [sub_zero, symmetricFloorGauge_smul_nonneg _ (inv_nonneg.mpr hr.le)]
    have hx' : symmetricFloorGauge x < r := by simpa only [symmetricGaugeBall, sub_zero] using hx
    simpa only [div_eq_mul_inv, mul_comm] using (div_lt_one hr).mpr hx'
  · rintro ⟨u, hu, rfl⟩
    change symmetricFloorGauge (r • u - 0) < r
    rw [sub_zero, symmetricFloorGauge_smul_nonneg r hr.le]
    have hu' : symmetricFloorGauge u < 1 := by simpa only [symmetricGaugeBall, sub_zero] using hu
    simpa only [mul_one] using mul_lt_mul_of_pos_left hu' hr

theorem volume_symmetricGaugeBall (u : FloorSpace (Fin d)) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (FloorSpace (Fin d))) (symmetricGaugeBall u r) =
      ENNReal.ofReal (r ^ (d - 1)) * volume (symmetricGaugeBall (0 : FloorSpace (Fin d)) 1) := by
  rw [symmetricGaugeBall_center_volume, symmetricGaugeBall_zero_smul hr,
    Measure.addHaar_smul_of_nonneg volume hr.le, finrank_floorSpace, Fintype.card_fin]

theorem symmetricGaugeBall_disjoint {u v : FloorSpace (Fin d)} {ell : ℝ}
    (hsep : ell ≤ symmetricFloorGauge (u - v)) :
    Disjoint (symmetricGaugeBall u (ell / 2)) (symmetricGaugeBall v (ell / 2)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : symmetricFloorGauge (x - u) < ell / 2 := hx
  have hy' : symmetricFloorGauge (x - v) < ell / 2 := hy
  have htri := symmetricFloorGauge_add_le (u - x) (x - v)
  rw [sub_add_sub_cancel] at htri
  have hneg : symmetricFloorGauge (u - x) = symmetricFloorGauge (x - u) := by
    rw [← neg_sub x u, symmetricFloorGauge_neg]
  rw [hneg] at htri
  linarith

/-- Exact norm-ball packing estimate used by the written MST proof. -/
theorem symmetricGauge_packing_power_bound {α : Type*} [DecidableEq α]
    (hd : 2 ≤ d) (s : Finset α) (p : α → FloorSpace (Fin d))
    {ell R : ℝ} (hell : 0 ≤ ell) (hR : 0 ≤ R) (hellR : ell ≤ R)
    (hp : ∀ a ∈ s, symmetricFloorGauge (p a) ≤ R)
    (hsep : (s : Set α).Pairwise (fun a b => ell ≤ symmetricFloorGauge (p a - p b))) :
    (s.card : ℝ) * (ell / 2) ^ (d - 1) ≤ (3 * R / 2) ^ (d - 1) := by
  by_cases hellpos : 0 < ell
  · have hRpos : 0 < R := hellpos.trans_le hellR
    have hdis : Set.PairwiseDisjoint (s : Set α) (fun a => symmetricGaugeBall (p a) (ell / 2)) :=
      fun a ha b hb hab => symmetricGaugeBall_disjoint (hsep ha hb hab)
    have hsub : (⋃ a ∈ s, symmetricGaugeBall (p a) (ell / 2)) ⊆
        symmetricGaugeBall (0 : FloorSpace (Fin d)) (3 * R / 2) := by
      intro x hx
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp hx
      have hx' : symmetricFloorGauge (x - p a) < ell / 2 := hx
      have htri := symmetricFloorGauge_add_le (x - p a) (p a)
      rw [sub_add_cancel] at htri
      change symmetricFloorGauge (x - 0) < 3 * R / 2
      rw [sub_zero]
      linarith [hp a ha]
    have hmeasure : (∑ a ∈ s, (volume : Measure (FloorSpace (Fin d)))
        (symmetricGaugeBall (p a) (ell / 2))) ≤
        volume (symmetricGaugeBall (0 : FloorSpace (Fin d)) (3 * R / 2)) := by
      rw [← measure_biUnion_finset hdis (fun _ _ => (isOpen_symmetricGaugeBall _ _).measurableSet)]
      exact measure_mono hsub
    simp_rw [volume_symmetricGaugeBall _ (half_pos hellpos)] at hmeasure
    rw [volume_symmetricGaugeBall _ (by positivity : 0 < 3 * R / 2)] at hmeasure
    simp only [Finset.sum_const, nsmul_eq_mul] at hmeasure
    have hunitTop := (symmetricGaugeBall_unit_lt_top hd).ne
    have hunitPos := ENNReal.toReal_pos (symmetricGaugeBall_unit_pos (d := d)).ne' hunitTop
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunitTop) hmeasure
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hell (by norm_num : (0 : ℝ) ≤ 2)) _),
      ENNReal.toReal_ofReal (pow_nonneg (by positivity : 0 ≤ 3 * R / 2) _)] at hr
    exact (mul_le_mul_iff_left₀ hunitPos).mp (by nlinarith [hr])
  · have heq : ell = 0 := le_antisymm (le_of_not_gt hellpos) hell
    simp only [heq, zero_div, zero_pow (by omega : d - 1 ≠ 0), mul_zero]
    positivity

end Antichain
