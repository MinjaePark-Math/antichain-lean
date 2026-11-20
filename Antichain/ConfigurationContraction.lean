import Antichain.GaussianPartitionIntegral
import Antichain.HeightCoordinates
import Antichain.ReferenceSimplex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Abel
import Mathlib.MeasureTheory.Group.Pointwise

/-! Convex interior margins and actual configuration-volume contractions for
the boundary-matching argument. -/

noncomputable section

namespace Antichain

open Set Metric MeasureTheory Module
open scoped Pointwise ENNReal

theorem convex_referenceSimplex (d : ℕ) : Convex ℝ (referenceSimplex d) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i j hij
    change a * x.val j + b * y.val j ≤ a * x.val i + b * y.val i
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.1 hij) ha)
      (mul_le_mul_of_nonneg_left (hy.1 hij) hb)
  · intro i j
    change (a * x.val i + b * y.val i) - (a * x.val j + b * y.val j) ≤ 1
    have h := add_le_add (mul_le_mul_of_nonneg_left (hx.2 i j) ha)
      (mul_le_mul_of_nonneg_left (hy.2 i j) hb)
    nlinarith

theorem referenceSimplex_ne_univ {d : ℕ} (hd : 2 ≤ d) :
    referenceSimplex d ≠ univ := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; dsimp [i, j] at hh; omega
  let p : FloorSpace (Fin d) :=
    ⟨EuclideanSpace.single i (2 : ℝ) - EuclideanSpace.single j 2, by simp [coordinateSum]⟩
  intro h
  have hp : p ∈ referenceSimplex d := h.symm ▸ mem_univ p
  have hbad := hp.2 i j
  dsimp [p] at hbad
  simp [hij, Ne.symm hij] at hbad
  norm_num at hbad

theorem referenceSimplex_frontier_nonempty {d : ℕ} (hd : 2 ≤ d) :
    (frontier (referenceSimplex d)).Nonempty :=
  nonempty_frontier_iff.mpr
    ⟨(referenceSimplex_interior_nonempty hd).mono interior_subset, referenceSimplex_ne_univ hd⟩

section ConvexMargin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Contracting toward a genuine interior ball preserves a scaled interior ball. -/
theorem convex_contraction_ball_subset {B : Set E} (hconv : Convex ℝ B)
    {center : E} {rho t : ℝ} (hball : ball center rho ⊆ B)
    (ht : 0 < t) (ht1 : t ≤ 1) {x : E} (hx : x ∈ B) :
    ball (t • center + (1 - t) • x) (t * rho) ⊆ B := by
  intro z hz
  let y := t • center + (1 - t) • x
  let u := t⁻¹ • (z - y)
  have hz' : ‖z - y‖ < t * rho := by simpa only [mem_ball, dist_eq_norm] using hz
  have hu : ‖u‖ < rho := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_iff₀ ht).mpr (by simpa only [mul_comm] using hz')
  have hcu : center + u ∈ B := hball (by simpa [mem_ball, dist_eq_norm] using hu)
  have hc := hconv hx hcu (sub_nonneg.mpr ht1) ht.le (by ring : (1 - t) + t = 1)
  have heq : (1 - t) • x + t • (center + u) = z := by
    dsimp [u]
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    dsimp [y]
    abel
  rwa [heq] at hc

theorem convex_contraction_dist_frontier {B : Set E} (hconv : Convex ℝ B)
    (hfront : (frontier B).Nonempty) {center : E} {rho t : ℝ}
    (hball : ball center rho ⊆ B) (ht : 0 < t) (ht1 : t ≤ 1) {x : E} (hx : x ∈ B) :
    t * rho ≤ infDist (t • center + (1 - t) • x) (frontier B) := by
  apply (le_infDist hfront).mpr
  intro z hz
  by_contra hn
  have hzb : z ∈ ball (t • center + (1 - t) • x) (t * rho) := by
    simpa only [mem_ball, dist_comm] using lt_of_not_ge hn
  have hball' := convex_contraction_ball_subset hconv hball ht ht1 hx
  have hzint : z ∈ interior B := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hzb) hball')
  exact hz.2 hzint

end ConvexMargin

/-- A fixed genuine simplex interior radius, independent of sample count and contraction. -/
theorem referenceSimplex_exists_contraction_radius {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ rho : ℝ, 0 < rho ∧
      ball (referenceSimplexInteriorPoint d) rho ⊆ referenceSimplex d ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ referenceSimplex d,
        t * rho ≤ infDist (t • referenceSimplexInteriorPoint d + (1 - t) • x)
          (frontier (referenceSimplex d)) := by
  have hnhds := (isOpen_referenceSimplexCore d).mem_nhds
    (referenceSimplexInteriorPoint_mem_core d)
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hb := hball.trans (referenceSimplexCore_subset d)
  exact ⟨rho, hrho, hb, fun t ht ht1 x hx => convex_contraction_dist_frontier
    (convex_referenceSimplex d) (referenceSimplex_frontier_nonempty hd) hb ht ht1 hx⟩

instance floorHeightConfiguration_isAddHaar (n d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (FloorHeightConfiguration n d)) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem finrank_floorHeightConfiguration (n d : ℕ) [NeZero d] :
    finrank ℝ (FloorHeightConfiguration n d) = d * n := by
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel (NeZero.pos d)
  simp only [FloorHeightConfiguration, finrank_prod, finrank_pi_fintype, finrank_floorSpace,
    finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  calc
    n * (d - 1) + n * 1 = n * (d - 1 + 1) := by ring
    _ = _ := by rw [hd]; ring

/-- The actual simultaneous floor/height contraction in Lemma 5.2. -/
def jointConfigurationContraction {d : ℕ} (n : ℕ) (center : FloorSpace (Fin d))
    (eta : ℝ) (p : FloorHeightConfiguration n d) : FloorHeightConfiguration n d :=
  ((fun _ => eta • center), 0) + (1 - eta) • p

theorem jointConfigurationContraction_floor {d n : ℕ} (center : FloorSpace (Fin d))
    (eta : ℝ) (p : FloorHeightConfiguration n d) (j : Fin n) :
    (jointConfigurationContraction n center eta p).1 j = eta • center + (1 - eta) • p.1 j := rfl

theorem jointConfigurationContraction_height {d n : ℕ} (center : FloorSpace (Fin d))
    (eta : ℝ) (p : FloorHeightConfiguration n d) (j : Fin n) :
    (jointConfigurationContraction n center eta p).2 j = (1 - eta) * p.2 j := by
  simp [jointConfigurationContraction, smul_eq_mul]

theorem jointConfigurationContraction_image {d n : ℕ} (center : FloorSpace (Fin d))
    (eta : ℝ) (A : Set (FloorHeightConfiguration n d)) :
    jointConfigurationContraction n center eta '' A =
      (fun p => ((fun _ => eta • center), (0 : Fin n → ℝ)) + p) '' ((1 - eta) • A) := by
  change jointConfigurationContraction n center eta '' A =
    (fun p => ((fun _ => eta • center), (0 : Fin n → ℝ)) + p) ''
      ((fun p => (1 - eta) • p) '' A)
  rw [Set.image_image]
  rfl

theorem measurableSet_jointConfigurationContraction_image {d n : ℕ}
    (center : FloorSpace (Fin d)) (eta : ℝ) (heta : eta < 1)
    {A : Set (FloorHeightConfiguration n d)} (hA : MeasurableSet A) :
    MeasurableSet (jointConfigurationContraction n center eta '' A) := by
  rw [jointConfigurationContraction_image]
  exact (MeasurableEquiv.addLeft _).measurableSet_image.mpr
    (hA.const_smul_of_ne_zero (sub_pos.mpr heta).ne')

theorem configuration_volume_image_add {d n : ℕ} (a : FloorHeightConfiguration n d)
    {A : Set (FloorHeightConfiguration n d)} (hA : MeasurableSet A) :
    volume ((fun p => a + p) '' A) = volume A := by
  have hm := ((MeasurableEquiv.addLeft a).measurableSet_image).mpr hA
  have h := (measurePreserving_add_left volume a).measure_preimage hm.nullMeasurableSet
  change volume ((fun x => a + x) ⁻¹' ((fun x => a + x) '' A)) =
    volume ((fun x => a + x) '' A) at h
  rw [Set.preimage_image_eq A (show Function.Injective (fun x => a + x) from
    fun _ _ h => add_left_cancel h)] at h
  exact h.symm

/-- The actual full-dimensional factor (1-eta)^(d*n), including both floors and heights. -/
theorem jointConfigurationContraction_volume {d : ℕ} [NeZero d] (n : ℕ)
    (center : FloorSpace (Fin d)) (eta : ℝ) (heta : eta < 1)
    {A : Set (FloorHeightConfiguration n d)} (hA : MeasurableSet A) :
    volume (jointConfigurationContraction n center eta '' A) =
      ENNReal.ofReal (1 - eta) ^ (d * n) * volume A := by
  have hs : 0 < 1 - eta := sub_pos.mpr heta
  have heq : jointConfigurationContraction n center eta '' A =
      (fun p => ((fun _ => eta • center), (0 : Fin n → ℝ)) + p) '' ((1 - eta) • A) := by
    change jointConfigurationContraction n center eta '' A =
      (fun p => ((fun _ => eta • center), (0 : Fin n → ℝ)) + p) ''
        ((fun p => (1 - eta) • p) '' A)
    rw [Set.image_image]
    rfl
  rw [heq, configuration_volume_image_add _ (hA.const_smul_of_ne_zero hs.ne'),
    Measure.addHaar_smul_of_nonneg volume hs.le, finrank_floorHeightConfiguration,
    ENNReal.ofReal_pow hs.le]

/-- Scale only the n actual height coordinates. -/
def heightScalingEquiv (n d : ℕ) (t : ℝ) (ht : t ≠ 0) :
    FloorHeightConfiguration n d ≃ᵐ FloorHeightConfiguration n d where
  toFun p := (p.1, t • p.2)
  invFun p := (p.1, t⁻¹ • p.2)
  left_inv p := by ext j <;> simp [ht]
  right_inv p := by ext j <;> simp [ht]
  measurable_toFun := measurable_fst.prodMk ((measurable_const_smul t).comp measurable_snd)
  measurable_invFun := measurable_fst.prodMk ((measurable_const_smul t⁻¹).comp measurable_snd)

theorem heightScalingEquiv_volume (n d : ℕ) (t : ℝ) (ht : 0 < t)
    {A : Set (FloorHeightConfiguration n d)} (hA : MeasurableSet A) :
    volume (heightScalingEquiv n d t ht.ne' '' A) = ENNReal.ofReal t ^ n * volume A := by
  have hm := ((heightScalingEquiv n d t ht.ne').measurableSet_image).mpr hA
  have hs (f : Fin n → FloorSpace (Fin d)) :
      Prod.mk f ⁻¹' (heightScalingEquiv n d t ht.ne' '' A) = t • (Prod.mk f ⁻¹' A) := by
    ext h
    constructor
    · rintro ⟨⟨g, k⟩, hk, heq⟩
      have heq' : g = f ∧ t • k = h := Prod.mk.inj heq
      rcases heq' with ⟨rfl, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(f, k), hk, rfl⟩
  change ((volume : Measure (Fin n → FloorSpace (Fin d))).prod
    (volume : Measure (Fin n → ℝ))) (heightScalingEquiv n d t ht.ne' '' A) = _
  rw [Measure.prod_apply hm]
  simp_rw [hs, Measure.addHaar_smul_of_nonneg volume ht.le, finrank_pi, Fintype.card_fin,
    ENNReal.ofReal_pow ht.le]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  congr 1
  exact (Measure.prod_apply hA).symm

end Antichain
