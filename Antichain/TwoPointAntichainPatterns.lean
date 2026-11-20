import Antichain.PatternFrequency
import Antichain.LimitMarginals
import Antichain.RankIndependence
import Mathlib.Tactic.FinCases

/-! The three two-point patterns of the actual three-dimensional antichain
permuton have probability one third, by coordinate symmetry. -/

noncomputable section
namespace Antichain
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal Topology

def cubeCoordinatePermute {d : ℕ} (e : Equiv.Perm (Fin d)) (x : CubePoint d) : CubePoint d :=
  fun i => x (e i)

theorem limitingCubeMap_coordinatePermute {d : ℕ} (e : Equiv.Perm (Fin d)) (y : Fin d → ℝ) :
    limitingCubeMap (cubeCoordinatePermute e y) = cubeCoordinatePermute e (limitingCubeMap y) := by
  have hs : ∑ j, y (e j) = ∑ j, y j := Equiv.sum_comp e y
  funext i
  simp only [limitingCubeMap, scaledCenteredCoordinates, cubeCoordinatePermute, hs]

theorem limitingCube_coordinatePermute_measurePreserving {d : ℕ} (e : Equiv.Perm (Fin d)) :
    MeasurePreserving (cubeCoordinatePermute e)
      (limitingCubeProbability d : Measure (CubePoint d)) (limitingCubeProbability d) := by
  have he := scalar_labelPermute_measurePreserving (gaussianReal 0 1) e
  have he' : MeasurePreserving (cubeCoordinatePermute e)
      (standardGaussianProduct (Fin d)) (standardGaussianProduct (Fin d)) := he
  have hm : Measurable (cubeCoordinatePermute e : CubePoint d → CubePoint d) := by
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))
  refine ⟨hm, ?_⟩
  change ((standardGaussianProduct (Fin d)).map limitingCubeMap).map (cubeCoordinatePermute e) = _
  rw [Measure.map_map hm limitingCubeMap_continuous.measurable]
  have hc : cubeCoordinatePermute e ∘ limitingCubeMap = limitingCubeMap ∘ cubeCoordinatePermute e := by
    funext y
    exact (limitingCubeMap_coordinatePermute e y).symm
  rw [hc, ← Measure.map_map limitingCubeMap_continuous.measurable he'.measurable, he'.map_eq]
  rfl

def twoPointMinorityEvent (i : Fin 3) : Set (CubeSample 2 3) :=
  {x | (x 0 i < x 1 i ∧ ∀ j, j ≠ i → x 1 j < x 0 j) ∨
    (x 1 i < x 0 i ∧ ∀ j, j ≠ i → x 0 j < x 1 j)}

theorem twoPointMinorityEvent_isOpen (i : Fin 3) : IsOpen (twoPointMinorityEvent i) := by
  simp only [twoPointMinorityEvent, Set.setOf_or, Set.setOf_and, Set.setOf_forall]
  apply IsOpen.union
  all_goals
    apply IsOpen.inter
    · exact isOpen_lt (by fun_prop) (by fun_prop)
    · apply isOpen_iInter_of_finite
      intro j
      apply isOpen_iInter_of_finite
      intro _
      exact isOpen_lt (by fun_prop) (by fun_prop)

theorem twoPointMinorityEvent_coordinatePermute (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (fun x : CubeSample 2 3 => fun j => cubeCoordinatePermute e (x j)) ⁻¹'
      twoPointMinorityEvent i = twoPointMinorityEvent (e i) := by
  ext x
  simp only [twoPointMinorityEvent, Set.mem_preimage, Set.mem_setOf_eq, cubeCoordinatePermute]
  have hforall (a b : Fin 3 → ℝ) :
      (∀ j, j ≠ i → a (e j) < b (e j)) ↔ (∀ j, j ≠ e i → a j < b j) := by
    constructor
    · intro h j hj
      have hn : e.symm j ≠ i := fun hh => hj (by simpa using congrArg e hh)
      simpa using h (e.symm j) hn
    · intro h j hj
      exact h (e j) (e.injective.ne hj)
  rw [hforall, hforall]

abbrev limitingTwoPointLaw : Measure (CubeSample 2 3) :=
  Measure.pi (fun _ : Fin 2 => (limitingCubeProbability 3 : Measure (CubePoint 3)))

theorem limitingTwoPoint_minority_mass_eq (i j : Fin 3) :
    limitingTwoPointLaw (twoPointMinorityEvent i) = limitingTwoPointLaw (twoPointMinorityEvent j) := by
  let e := Equiv.swap i j
  have hp := measurePreserving_pi
    (fun _ : Fin 2 => (limitingCubeProbability 3 : Measure (CubePoint 3)))
    (fun _ : Fin 2 => (limitingCubeProbability 3 : Measure (CubePoint 3)))
    (fun _ => limitingCube_coordinatePermute_measurePreserving e)
  have hh := hp.measure_preimage (twoPointMinorityEvent_isOpen i).measurableSet.nullMeasurableSet
  rw [twoPointMinorityEvent_coordinatePermute] at hh
  simpa [e] using hh.symm

theorem measurableSet_normalQuantileSurface_three :
    MeasurableSet (normalQuantileSurface (Fin 3)) := by
  change MeasurableSet {x : CubePoint 3 | (∀ i, x i ∈ Ioo (0 : ℝ) 1) ∧
    ∑ i, normalQuantile (x i) = 0}
  apply MeasurableSet.inter
  · have h : MeasurableSet (⋂ i : Fin 3, {x : CubePoint 3 | x i ∈ Ioo (0 : ℝ) 1}) :=
      MeasurableSet.iInter (fun i => measurableSet_Ioo.preimage (measurable_pi_apply i))
    convert h using 1
    ext x
    constructor
    · intro hx
      exact Set.mem_iInter.mpr hx
    · intro hx
      exact Set.mem_iInter.mp hx
  · have hm : Measurable (fun x : CubePoint 3 => ∑ i, normalQuantile (x i)) :=
      Finset.measurable_sum _ (fun i _ => normalQuantile_measurable.comp (measurable_pi_apply i))
    exact measurableSet_eq_fun hm measurable_const

theorem limitingCube_surface_ae_three :
    ∀ᵐ x ∂(limitingCubeProbability 3 : Measure (CubePoint 3)), x ∈ normalQuantileSurface (Fin 3) := by
  change ∀ᵐ x ∂(standardGaussianProduct (Fin 3)).map limitingCubeMap, _
  apply (ae_map_iff limitingCubeMap_continuous.measurable.aemeasurable
    measurableSet_normalQuantileSurface_three).mpr
  exact Filter.Eventually.of_forall (fun y => by
    refine ⟨fun i => normalCDF_mem_Ioo _, ?_⟩
    simpa only [limitingCubeMap, normalQuantile_normalCDF] using scaledCenteredCoordinates_sum_zero y)

theorem limitingTwoPoint_antichain_ae :
    ∀ᵐ x ∂limitingTwoPointLaw, ¬ StrictBelow (x 0) (x 1) ∧ ¬ StrictBelow (x 1) (x 0) := by
  have h0 := (measurePreserving_eval
    (fun _ : Fin 2 => (limitingCubeProbability 3 : Measure (CubePoint 3))) 0).quasiMeasurePreserving.tendsto_ae.eventually
    limitingCube_surface_ae_three
  have h1 := (measurePreserving_eval
    (fun _ : Fin 2 => (limitingCubeProbability 3 : Measure (CubePoint 3))) 1).quasiMeasurePreserving.tendsto_ae.eventually
    limitingCube_surface_ae_three
  filter_upwards [h0, h1] with x hx0 hx1
  rw [← normalCDF_surface_eq_quantileSurface] at hx0 hx1
  exact ⟨coordinateImageSurface_not_strictBelow normalCDF normalCDF_strictMono hx0 hx1,
    coordinateImageSurface_not_strictBelow normalCDF normalCDF_strictMono hx1 hx0⟩

theorem twoPointMinorityEvent_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (twoPointMinorityEvent i) (twoPointMinorityEvent j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  fin_cases i <;> fin_cases j <;>
    simp only [twoPointMinorityEvent, Set.mem_setOf_eq, Fin.forall_fin_succ] at hi hj <;>
    simp_all <;> rcases hi with hi | hi <;> rcases hj with hj | hj <;> linarith

theorem limitingTwoPoint_minority_cover_ae :
    ∀ᵐ x ∂limitingTwoPointLaw, ∃ i, x ∈ twoPointMinorityEvent i := by
  have ht := iid_permuton_coordinateTieFree_ae 2 3 (limitingCubeProbability 3)
    (fun i => limitingAntichainMeasure_coordinate_map (by decide : 2 ≤ Fintype.card (Fin 3)) i)
  filter_upwards [limitingTwoPoint_antichain_ae, ht] with x ha ht
  have hne (i : Fin 3) : x 0 i ≠ x 1 i := fun h => (by decide : (0 : Fin 2) ≠ 1) (ht i h)
  by_cases h0 : x 0 0 < x 1 0 <;> by_cases h1 : x 0 1 < x 1 1 <;>
    by_cases h2 : x 0 2 < x 1 2
  all_goals
    have hrev (i : Fin 3) (hi : ¬x 0 i < x 1 i) : x 1 i < x 0 i :=
      lt_of_le_of_ne (le_of_not_gt hi) (hne i).symm
  · exact False.elim (ha.1 (by intro i; fin_cases i <;> assumption))
  · refine ⟨2, Or.inr ⟨hrev 2 h2, ?_⟩⟩
    intro j hj; fin_cases j <;> simp_all
  · refine ⟨1, Or.inr ⟨hrev 1 h1, ?_⟩⟩
    intro j hj; fin_cases j <;> simp_all
  · refine ⟨0, Or.inl ⟨h0, ?_⟩⟩
    intro j hj; fin_cases j <;> simp_all
  · refine ⟨0, Or.inr ⟨hrev 0 h0, ?_⟩⟩
    intro j hj; fin_cases j <;> simp_all
  · refine ⟨1, Or.inl ⟨h1, ?_⟩⟩
    intro j hj; fin_cases j <;> simp_all
  · refine ⟨2, Or.inl ⟨h2, ?_⟩⟩
    intro j hj; fin_cases j <;> simp_all
  · exact False.elim (ha.2 (fun i => hrev i (by fin_cases i <;> assumption)))

theorem limitingTwoPoint_minority_probability (i : Fin 3) :
    (limitingTwoPointLaw (twoPointMinorityEvent i)).toReal = (1 : ℝ) / 3 := by
  have hcover : limitingTwoPointLaw (⋃ i, twoPointMinorityEvent i) = 1 := by
    calc
      _ = limitingTwoPointLaw univ := measure_congr (by
        filter_upwards [limitingTwoPoint_minority_cover_ae] with x hx
        exact propext ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr hx⟩)
      _ = 1 := measure_univ
  have hmeasure := measure_iUnion (μ := limitingTwoPointLaw)
    twoPointMinorityEvent_pairwise_disjoint (fun i => (twoPointMinorityEvent_isOpen i).measurableSet)
  rw [hcover, tsum_fintype] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at hreal
  have heq (j : Fin 3) : (limitingTwoPointLaw (twoPointMinorityEvent j)).toReal =
      (limitingTwoPointLaw (twoPointMinorityEvent i)).toReal :=
    congrArg ENNReal.toReal (limitingTwoPoint_minority_mass_eq j i)
  simp only [ENNReal.toReal_one, heq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hreal
  norm_num at hreal
  linarith

def twoPointAntichainPattern (i : Fin 3) : Fin 2 → Equiv.Perm (Fin 2) :=
  if i = 0 then ![Fin.revPerm, Fin.revPerm] else
    if i = 1 then ![Fin.revPerm, Equiv.refl _] else ![Equiv.refl _, Fin.revPerm]

theorem patternEvent_two_point_iff {m : ℕ} (tau : Fin m → Equiv.Perm (Fin 2))
    (x : CubeSample 2 (m + 1)) :
    x ∈ patternEvent 2 m tau ↔
      (∀ i : Fin (m + 1), if ((Fin.cons (Equiv.refl (Fin 2)) tau : Fin (m + 1) → Equiv.Perm (Fin 2)) i) 0 <
          ((Fin.cons (Equiv.refl (Fin 2)) tau : Fin (m + 1) → Equiv.Perm (Fin 2)) i) 1
        then x 0 i < x 1 i else x 1 i < x 0 i) ∨
      (∀ i : Fin (m + 1), if ((Fin.cons (Equiv.refl (Fin 2)) tau : Fin (m + 1) → Equiv.Perm (Fin 2)) i) 0 <
          ((Fin.cons (Equiv.refl (Fin 2)) tau : Fin (m + 1) → Equiv.Perm (Fin 2)) i) 1
        then x 1 i < x 0 i else x 0 i < x 1 i) := by
  constructor
  · rintro ⟨e, he⟩
    have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
    have hc (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases hc (e 0) with h0 | h0 <;> rcases hc (e 1) with h1 | h1
    · exact False.elim (hne (h0.trans h1.symm))
    · left
      intro i
      simpa only [h0, h1] using he i 0 1 (by decide)
    · right
      intro i
      simpa only [h0, h1] using he i 0 1 (by decide)
    · exact False.elim (hne (h0.trans h1.symm))
  · rintro (h | h)
    · refine ⟨Equiv.refl _, ?_⟩
      intro i j k hjk
      fin_cases j <;> fin_cases k <;> simp_all
    · refine ⟨Fin.revPerm, ?_⟩
      intro i j k hjk
      fin_cases j <;> fin_cases k <;> simp_all

theorem twoPointAntichainPattern_event (i : Fin 3) :
    patternEvent 2 2 (twoPointAntichainPattern i) = twoPointMinorityEvent i := by
  ext x
  rw [patternEvent_two_point_iff]
  fin_cases i <;>
    simp [twoPointAntichainPattern, twoPointMinorityEvent, Fin.forall_fin_succ] <;> tauto

/-- The three active two-point antichain patterns in the revised manuscript
have equal probability one third under the actual limiting law. -/
theorem twoPointAntichainPattern_probability (i : Fin 3) :
    patternProbability 2 2 (twoPointAntichainPattern i) (limitingCubeProbability 3) = (1 : ℝ) / 3 := by
  rw [patternProbability, twoPointAntichainPattern_event]
  exact limitingTwoPoint_minority_probability i

end Antichain
