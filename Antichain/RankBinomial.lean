import Antichain.RankHoeffding
import Antichain.PoissonRestrictions
import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-! Literal binomial count laws for the manuscript's uniform order statistics. -/
noncomputable section
namespace Antichain
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

theorem iid_selection_mass {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsFiniteMeasure mu] (U : Set X) {n : ℕ} (S : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => mu)) (configurationSelectionSet U n S) =
      mu U ^ S.card * mu Uᶜ ^ (n - S.card) := by
  classical
  letI (j : Fin n) : IsFiniteMeasure (if j ∈ S then mu.restrict U else mu.restrict Uᶜ) := by
    split_ifs <;> infer_instance
  rw [← Measure.restrict_apply_univ, ← pi_configurationSelectionSet mu U S, Measure.pi_univ]
  have hterm (j : Fin n) :
      (if j ∈ S then mu.restrict U else mu.restrict Uᶜ) univ =
        if j ∈ S then mu U else mu Uᶜ := by split_ifs <;> simp
  simp_rw [hterm]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  congr 1
  congr 1
  have hset : (univ.filter (fun j : Fin n => j ∉ S)) = Sᶜ := by ext j; simp
  rw [hset, Finset.card_compl, Fintype.card_fin]

theorem iid_count_selection_event {X : Type*} (U : Set X) (n k : ℕ) :
    {x : Fin n → X | (configurationRestrictionIndices U x).card = k} =
      ⋃ S ∈ (univ : Finset (Fin n)).powersetCard k, configurationSelectionSet U n S := by
  classical
  ext x
  constructor
  · intro hx
    apply Set.mem_iUnion₂.mpr
    refine ⟨configurationRestrictionIndices U x, ?_, ?_⟩
    · exact mem_powersetCard.mpr ⟨subset_univ _, hx⟩
    · exact (configurationRestrictionIndices_eq_iff U x _).mp rfl
  · intro hx
    obtain ⟨S, hS, hx⟩ := Set.mem_iUnion₂.mp hx
    change (configurationRestrictionIndices U x).card = k
    rw [(configurationRestrictionIndices_eq_iff U x S).mpr hx]
    exact (mem_powersetCard.mp hS).2

theorem iid_count_selection_mass {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U) (n k : ℕ) :
    (Measure.pi (fun _ : Fin n => mu))
      {x | (configurationRestrictionIndices U x).card = k} =
        (n.choose k : ℝ≥0∞) * (mu U ^ k * mu Uᶜ ^ (n - k)) := by
  classical
  rw [iid_count_selection_event]
  rw [measure_biUnion_finset]
  · have hterm (S : Finset (Fin n)) (hS : S ∈ (univ : Finset (Fin n)).powersetCard k) :
        (Measure.pi (fun _ : Fin n => mu)) (configurationSelectionSet U n S) =
          mu U ^ k * mu Uᶜ ^ (n - k) := by
      rw [iid_selection_mass mu U S, (mem_powersetCard.mp hS).2]
    simp_rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro S hS T hT hST
    apply Set.disjoint_left.mpr
    intro x hxS hxT
    exact hST (((configurationRestrictionIndices_eq_iff U x S).mpr hxS).symm.trans
      ((configurationRestrictionIndices_eq_iff U x T).mpr hxT))
  · exact fun S _ => measurableSet_configurationSelectionSet hU n S

def uniformSampleCount (n : ℕ) (t : ℝ) (x : Fin n → ℝ) : Fin (n + 1) :=
  ⟨(configurationRestrictionIndices (Iic t) x).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))⟩

theorem uniformSampleCount_measurable (n : ℕ) (t : ℝ) : Measurable (uniformSampleCount n t) := by
  classical
  apply measurable_to_countable'
  intro k
  have hset : uniformSampleCount n t ⁻¹' {k} =
      {x | (configurationRestrictionIndices (Iic t) x).card = k.val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact Fin.ext_iff
  rw [hset, iid_count_selection_event]
  exact MeasurableSet.iUnion (fun S => MeasurableSet.iUnion (fun _ =>
    measurableSet_configurationSelectionSet measurableSet_Iic n S))

theorem uniformSampleCount_binomial (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)).map (uniformSampleCount n t) =
      (PMF.binomial ⟨t, ht.1⟩ (by exact ht.2) n).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (uniformSampleCount_measurable n t) (measurableSet_singleton k)]
  have hset : uniformSampleCount n t ⁻¹' {k} =
      {x | (configurationRestrictionIndices (Iic t) x).card = k.val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact Fin.ext_iff
  rw [hset, iid_count_selection_mass cubeCoordinateLaw measurableSet_Iic n k.val]
  rw [cubeCoordinateLaw_Iic, min_eq_left ht.2]
  have hcomp : cubeCoordinateLaw (Iic t)ᶜ = ENNReal.ofReal (1 - t) := by
    rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
      cubeCoordinateLaw_Iic, min_eq_left ht.2, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 ht.1]
  rw [hcomp, PMF.toMeasure_apply_singleton, PMF.binomial_apply]
  simp only [Fin.val_last]
  rw [← ENNReal.ofReal_eq_coe_nnreal ht.1]
  rw [show (1 : ℝ≥0∞) - ENNReal.ofReal t = ENNReal.ofReal (1 - t) by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_sub 1 ht.1).symm]
  ring
  all_goals exact measurableSet_singleton _

theorem uniformSampleCount_sorted (n : ℕ) (t : ℝ) (x : Fin n → ℝ) :
    uniformSampleCount n t (sampleSortedValues x) = uniformSampleCount n t x := by
  classical
  apply Fin.ext
  change (univ.filter (fun j => sampleSortedValues x j ∈ Iic t)).card =
    (univ.filter (fun j => x j ∈ Iic t)).card
  have h := Equiv.sum_comp (sampleSortPermutation x)
    (fun j => if x j ≤ t then (1 : ℕ) else 0)
  simpa only [sampleSortedValues, Finset.sum_boole, Set.mem_Iic] using h

theorem conditional_sorted_count_binomial (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (i : Fin d) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (cubeAntichainLaw n d).map
      (fun x => uniformSampleCount n t (coordinateSortedValues n d x i)) =
        (PMF.binomial ⟨t, ht.1⟩ (by exact ht.2) n).toMeasure := by
  have hm : Measurable (fun x : CubeSample n d => coordinateSortedValues n d x i) :=
    (measurable_pi_apply i).comp (coordinateSortedValues_measurable n d)
  rw [show (fun x : CubeSample n d => uniformSampleCount n t (coordinateSortedValues n d x i)) =
      uniformSampleCount n t ∘ (fun x => coordinateSortedValues n d x i) from rfl,
    ← Measure.map_map (uniformSampleCount_measurable n t) hm,
    cubeAntichain_sortedCoordinate_law n d hd i, scalarSortedLaw,
    Measure.map_map (uniformSampleCount_measurable n t) (sampleSortedValues_measurable n)]
  have hcomp : uniformSampleCount n t ∘ sampleSortedValues = uniformSampleCount n t :=
    funext (uniformSampleCount_sorted n t)
  rw [hcomp]
  exact uniformSampleCount_binomial n ht

end Antichain
