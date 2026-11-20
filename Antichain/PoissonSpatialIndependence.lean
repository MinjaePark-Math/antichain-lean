import Antichain.PoissonRestrictionLaw
import Antichain.PoissonRestrictionComposition

/-! Genuine independence of arbitrary disjoint spatial restrictions of the
constructed finite-intensity Poisson process. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

variable {X K : Type*} [MeasurableSpace X]

theorem finiteIntensityPoissonLaw_disjoint_rectangle (t : ℝ≥0)
    (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (A : K → Set (FiniteConfiguration X)) (hA : ∀ i, MeasurableSet (A i)) (S : Finset K) :
    finiteIntensityPoissonLaw t mu (⋂ i ∈ S, configurationRestriction (C i) ⁻¹' A i) =
      ∏ i ∈ S, finiteIntensityPoissonLaw t (mu.restrict (C i)) (A i) := by
  classical
  induction S using Finset.induction_on generalizing mu with
  | empty =>
    letI := finiteIntensityPoissonLaw_probability_all t mu
    simp
  | @insert i S hi ih =>
    let B : Set (FiniteConfiguration X) := ⋂ j ∈ S, configurationRestriction (C j) ⁻¹' A j
    have hB : MeasurableSet B := by
      apply S.measurableSet_biInter
      intro j hj
      exact (measurable_configurationRestriction (hC j)) (hA j)
    have hsub (j : K) (hj : j ∈ S) : C j ⊆ (C i)ᶜ := by
      intro x hxj hxi
      have hji : j ≠ i := by intro heq; subst j; exact hi hj
      exact Set.disjoint_left.mp (hdisj hji) hxj hxi
    have hpre : configurationRestriction (C i)ᶜ ⁻¹' B = B := by
      ext z
      simp only [B, Set.mem_preimage, Set.mem_iInter]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro hj
      rw [configurationRestriction_composition, Set.inter_eq_left.mpr (hsub j hj)]
    have hset : (⋂ j ∈ insert i S, configurationRestriction (C j) ⁻¹' A j) =
        configurationRestriction (C i) ⁻¹' A i ∩ B := by
      ext z
      simp only [Set.mem_iInter, Finset.mem_insert, forall_eq_or_imp,
        Set.mem_inter_iff, B]
    rw [hset, Finset.prod_insert hi]
    change finiteIntensityPoissonLaw t mu
      (configurationRestriction (C i) ⁻¹' A i ∩ B) = _
    rw [← hpre, finiteIntensityPoissonLaw_restriction_rectangle t mu (hC i) (hA i) hB]
    rw [ih (mu.restrict (C i)ᶜ)]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Measure.restrict_restrict_of_subset (hsub j hj)]

theorem finiteIntensityPoissonLaw_disjoint_restrictions_independent (t : ℝ≥0)
    (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) :
    iIndepFun (fun i => configurationRestriction (C i)) (finiteIntensityPoissonLaw t mu) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S A hA
  let B : K → Set (FiniteConfiguration X) := fun i => if i ∈ S then A i else Set.univ
  have hB (i : K) : MeasurableSet (B i) := by
    dsimp only [B]
    split_ifs with hi
    · exact hA i hi
    · exact MeasurableSet.univ
  have hsets : (⋂ i ∈ S, configurationRestriction (C i) ⁻¹' B i) =
      ⋂ i ∈ S, configurationRestriction (C i) ⁻¹' A i := by
    apply Set.iInter_congr
    intro i
    apply Set.iInter_congr
    intro hi
    simp only [B, if_pos hi]
  rw [← hsets, finiteIntensityPoissonLaw_disjoint_rectangle t mu C hC hdisj B hB S]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [B, if_pos hi]
  have h := congrArg (fun nu : Measure (FiniteConfiguration X) => nu (A i))
    (finiteIntensityPoissonLaw_restriction t mu (hC i))
  dsimp only at h
  rw [Measure.map_apply (measurable_configurationRestriction (hC i)) (hA i hi)] at h
  exact h.symm

theorem finiteIntensityPoissonLaw_disjoint_joint [Fintype K] (t : ℝ≥0)
    (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (finiteIntensityPoissonLaw t mu).map (fun z i => configurationRestriction (C i) z) =
      Measure.pi (fun i => finiteIntensityPoissonLaw t (mu.restrict (C i))) := by
  letI := finiteIntensityPoissonLaw_probability_all t mu
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_configurationRestriction (hC i)).aemeasurable)).mp
      (finiteIntensityPoissonLaw_disjoint_restrictions_independent t mu C hC hdisj)
  have hmaps : (fun i => (finiteIntensityPoissonLaw t mu).map (configurationRestriction (C i))) =
      fun i => finiteIntensityPoissonLaw t (mu.restrict (C i)) := by
    funext i
    exact finiteIntensityPoissonLaw_restriction t mu (hC i)
  rw [hmaps] at h
  exact h

end Antichain
