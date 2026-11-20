import Antichain.PoissonSpatialIndependence
import Mathlib.Data.Finset.Preimage
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! The source Poisson product argument for measurable hereditary events.
All spatial restriction laws and their independence are proved upstream. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

variable {X K : Type*} [MeasurableSpace X]

theorem poisson_normalizer_disjoint_union (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] (C : K → Set X) (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (S : Finset K) :
    ENNReal.ofReal (Real.exp ((t : ℝ) * ((mu.restrict (⋃ i ∈ S, C i)) Set.univ).toReal)) =
      ∏ i ∈ S, ENNReal.ofReal (Real.exp ((t : ℝ) * ((mu.restrict (C i)) Set.univ).toReal)) := by
  have hm : ((mu.restrict (⋃ i ∈ S, C i)) Set.univ).toReal =
      ∑ i ∈ S, ((mu.restrict (C i)) Set.univ).toReal := by
    simp only [Measure.restrict_apply_univ]
    rw [measure_biUnion_finset (fun _ _ _ _ hij => hdisj hij) (fun i _ => hC i),
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  rw [hm, Finset.mul_sum, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]

theorem configurationSeriesMeasure_restrict_biUnion_le_poisson
    (t : ℝ≥0) (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (S : Finset K) (A : Set (FiniteConfiguration X)) (hA : MeasurableSet A)
    (hhered : ∀ (V : Set X) z, z ∈ A → configurationRestriction V z ∈ A) :
    configurationSeriesMeasure (t : ℝ≥0∞) (mu.restrict (⋃ i ∈ S, C i)) A ≤
      ∏ i ∈ S, configurationSeriesMeasure (t : ℝ≥0∞) (mu.restrict (C i)) A := by
  classical
  let U : Set X := ⋃ i ∈ S, C i
  have hsub : A ⊆ ⋂ i ∈ S, configurationRestriction (C i) ⁻¹' A := by
    intro z hz
    apply Set.mem_iInter₂.mpr
    intro i hi
    exact hhered (C i) z hz
  have hp : finiteIntensityPoissonLaw t (mu.restrict U) A ≤
      ∏ i ∈ S, finiteIntensityPoissonLaw t (mu.restrict (C i)) A := by
    calc
      _ ≤ _ := measure_mono hsub
      _ = _ := by
        rw [finiteIntensityPoissonLaw_disjoint_rectangle t (mu.restrict U) C hC hdisj
          (fun _ => A) (fun _ => hA) S]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Measure.restrict_restrict_of_subset (show C i ⊆ U from
          fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩)]
  rw [configurationSeriesMeasure_eq_exp_smul_poisson_all, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal (Real.exp ((t : ℝ) * ((mu.restrict U) Set.univ).toReal)) *
        ∏ i ∈ S, finiteIntensityPoissonLaw t (mu.restrict (C i)) A :=
      mul_le_mul_left' hp _
    _ = _ := by
      rw [poisson_normalizer_disjoint_union t mu C hC hdisj S,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [configurationSeriesMeasure_eq_exp_smul_poisson_all, Measure.smul_apply, smul_eq_mul]

theorem configurationSeriesMeasure_exhaustion_event (t : ℝ≥0∞)
    (mu : Measure X) [IsFiniteMeasure mu] (U : ℕ → Set X)
    (hU : ∀ m, MeasurableSet (U m)) (hmono : Monotone U)
    (hcover : (⋃ m, U m) = Set.univ) {A : Set (FiniteConfiguration X)}
    (hA : MeasurableSet A) :
    configurationSeriesMeasure t mu A =
      ⨆ m : ℕ, configurationSeriesMeasure t (mu.restrict (U m)) A := by
  let B : ∀ n : ℕ, Set (Fin n → X) := fun n => configurationMk n ⁻¹' A
  have hB (n : ℕ) : MeasurableSet (B n) := (measurable_configurationMk n) hA
  have heq : configurationEvent B = A := by ext z; cases z; rfl
  simpa only [heq] using
    configurationSeriesMeasure_exhaustion t mu U hU hmono hcover B hB

def poissonCellPrefix (K : Type*) [Encodable K] (m : ℕ) : Finset K :=
  (Finset.range m).preimage Encodable.encode Encodable.encode_injective.injOn

@[simp] theorem mem_poissonCellPrefix {K : Type*} [Encodable K] (m : ℕ) (i : K) :
    i ∈ poissonCellPrefix K m ↔ Encodable.encode i < m := by
  simp [poissonCellPrefix]

theorem configurationSeriesMeasure_countable_le_exp_sum_poisson {K : Type*} [Encodable K]
    (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : (⋃ i, C i) = Set.univ) (t : ℝ≥0) (A : Set (FiniteConfiguration X))
    (hA : MeasurableSet A)
    (hhered : ∀ (V : Set X) z, z ∈ A → configurationRestriction V z ∈ A)
    (V : K → ℝ) (hV : ∀ i, 1 ≤ V i) (hlogs : Summable (fun i => Real.log (V i)))
    (hlocal : ∀ i, configurationSeriesMeasure (t : ℝ≥0∞) (mu.restrict (C i)) A ≤
      ENNReal.ofReal (V i)) :
    configurationSeriesMeasure (t : ℝ≥0∞) mu A ≤
      ENNReal.ofReal (Real.exp (∑' i, Real.log (V i))) := by
  classical
  let U : ℕ → Set X := fun m => ⋃ i ∈ poissonCellPrefix K m, C i
  have hU : ∀ m, MeasurableSet (U m) := fun m =>
    (poissonCellPrefix K m).measurableSet_biUnion (fun i _ => hC i)
  have hmono : Monotone U := by
    intro m n hmn x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion₂.mpr ⟨i,
      (mem_poissonCellPrefix n i).mpr ((mem_poissonCellPrefix m i).mp hi |>.trans_le hmn), hx⟩
  have hcov : (⋃ m, U m) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, C i := hcover.symm ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨Encodable.encode i + 1, Set.mem_iUnion₂.mpr
      ⟨i, (mem_poissonCellPrefix _ i).mpr (Nat.lt_succ_self _), hi⟩⟩
  rw [configurationSeriesMeasure_exhaustion_event (t : ℝ≥0∞) mu U hU hmono hcov hA]
  apply iSup_le
  intro m
  let S := poissonCellPrefix K m
  calc
    _ ≤ ∏ i ∈ S, configurationSeriesMeasure (t : ℝ≥0∞) (mu.restrict (C i)) A :=
      configurationSeriesMeasure_restrict_biUnion_le_poisson t mu C hC hdisj S A hA hhered
    _ ≤ ∏ i ∈ S, ENNReal.ofReal (V i) := Finset.prod_le_prod' (fun i _ => hlocal i)
    _ = ENNReal.ofReal (Real.exp (∑ i ∈ S, Real.log (V i))) := by
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (hV i))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (hlogs.sum_le_tsum S (fun i _ => Real.log_nonneg (hV i))))

end Antichain
