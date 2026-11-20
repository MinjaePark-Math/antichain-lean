import Antichain.PoissonConfiguration
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.Independence.Basic

/-! Literal restrictions of the actual finite-list Poisson configuration.
The retained points keep their original relative order. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

local instance configurationSubsetFintype {n : ℕ} (S : Finset (Fin n)) : Fintype S :=
  Subtype.fintype (fun j => j ∈ S)

def configurationSubsequence {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → X) : FiniteConfiguration X :=
  ⟨S.card, fun j => x (S.orderIsoOfFin rfl j)⟩

theorem measurable_configurationSubsequence {n : ℕ} (S : Finset (Fin n)) :
    Measurable (configurationSubsequence (X := X) S) := by
  exact (measurable_configurationMk S.card).comp
    (measurable_pi_lambda _ (fun j => measurable_pi_apply _))

def configurationRestrictionIndices (U : Set X) {n : ℕ} (x : Fin n → X) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => x j ∈ U)

omit [MeasurableSpace X] in
@[simp] theorem mem_configurationRestrictionIndices (U : Set X) {n : ℕ}
    (x : Fin n → X) (j : Fin n) :
    j ∈ configurationRestrictionIndices U x ↔ x j ∈ U := by
  classical
  simp [configurationRestrictionIndices]

def configurationRestriction (U : Set X) (z : FiniteConfiguration X) :
    FiniteConfiguration X :=
  configurationSubsequence (configurationRestrictionIndices U z.2) z.2

def configurationSelectionSet (U : Set X) (n : ℕ) (S : Finset (Fin n)) :
    Set (Fin n → X) := {x | ∀ j, x j ∈ U ↔ j ∈ S}

theorem measurableSet_configurationSelectionSet {U : Set X} (hU : MeasurableSet U)
    (n : ℕ) (S : Finset (Fin n)) :
    MeasurableSet (configurationSelectionSet U n S) := by
  classical
  change MeasurableSet {x : Fin n → X | ∀ j, x j ∈ U ↔ j ∈ S}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j ∈ S
  · simpa only [hj, iff_true] using hU.preimage (measurable_pi_apply j)
  · simpa only [hj, iff_false] using (hU.preimage (measurable_pi_apply j)).compl

omit [MeasurableSpace X] in
theorem configurationRestrictionIndices_eq_iff (U : Set X) {n : ℕ}
    (x : Fin n → X) (S : Finset (Fin n)) :
    configurationRestrictionIndices U x = S ↔ x ∈ configurationSelectionSet U n S := by
  classical
  simp only [Finset.ext_iff, mem_configurationRestrictionIndices,
    configurationSelectionSet, Set.mem_setOf_eq]

omit [MeasurableSpace X] in
theorem configurationRestriction_preimage_slice (U : Set X) (A : Set (FiniteConfiguration X))
    (n : ℕ) :
    configurationMk n ⁻¹' (configurationRestriction U ⁻¹' A) =
      ⋃ S : Finset (Fin n), configurationSelectionSet U n S ∩
        configurationSubsequence S ⁻¹' A := by
  classical
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr ⟨configurationRestrictionIndices U x,
      (configurationRestrictionIndices_eq_iff U x _).mp rfl, hx⟩
  · intro hx
    obtain ⟨S, hS, hx⟩ := Set.mem_iUnion.mp hx
    change configurationSubsequence (configurationRestrictionIndices U x) x ∈ A
    rw [(configurationRestrictionIndices_eq_iff U x S).mpr hS]
    exact hx

theorem measurable_configurationRestriction {U : Set X} (hU : MeasurableSet U) :
    Measurable (configurationRestriction U) := by
  intro A hA
  change MeasurableSet[⨅ n, (inferInstance : MeasurableSpace (Fin n → X)).map
    (configurationMk n)] (configurationRestriction U ⁻¹' A)
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet (configurationMk n ⁻¹' (configurationRestriction U ⁻¹' A))
  rw [configurationRestriction_preimage_slice]
  exact MeasurableSet.iUnion (fun S =>
    (measurableSet_configurationSelectionSet hU n S).inter
      ((measurable_configurationSubsequence S) hA))

omit [MeasurableSpace X] in
theorem configurationRestriction_points_mem (U : Set X) (z : FiniteConfiguration X)
    (j : Fin (configurationRestriction U z).1) :
    (configurationRestriction U z).2 j ∈ U := by
  change Fin (configurationRestrictionIndices U z.2).card at j
  change z.2 ((configurationRestrictionIndices U z.2).orderIsoOfFin rfl j) ∈ U
  exact (mem_configurationRestrictionIndices U z.2 _).mp
    ((configurationRestrictionIndices U z.2).orderIsoOfFin rfl j).property

def configurationComplementIndex {n : ℕ} (S : Finset (Fin n)) :
    Fin Sᶜ.card ≃ {j : Fin n // j ∉ S} where
  toFun j := ⟨Sᶜ.orderIsoOfFin rfl j, by
    simpa only [Finset.mem_compl] using (Sᶜ.orderIsoOfFin rfl j).property⟩
  invFun j := (Sᶜ.orderIsoOfFin rfl).symm ⟨j.val, by
    simpa only [Finset.mem_compl] using j.property⟩
  left_inv j := by
    apply (Sᶜ.orderIsoOfFin rfl).injective
    apply Subtype.ext
    simp
  right_inv j := by
    apply Subtype.ext
    change ((Sᶜ.orderIsoOfFin rfl)
      ((Sᶜ.orderIsoOfFin rfl).symm ⟨j.val, by simpa using j.property⟩)).val = j.val
    simp

theorem pi_reindex_event {J K : Type*} [Fintype J] [Fintype K]
    (mu : Measure X) [IsFiniteMeasure mu] (e : J ≃ K)
    {A : Set (J → X)} (hA : MeasurableSet A) :
    Measure.pi (fun _ : K => mu) {x | (fun j => x (e j)) ∈ A} =
      Measure.pi (fun _ : J => mu) A := by
  have hmp := measurePreserving_piCongrLeft (fun _ : J => mu) e.symm
  have hfun : (MeasurableEquiv.piCongrLeft (fun _ : J => X) e.symm :
      (K → X) → (J → X)) = fun x j => x (e j) := by
    funext x j
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      Equiv.symm_symm, cast_eq]
  rw [hfun] at hmp
  exact hmp.measure_preimage hA.nullMeasurableSet

theorem pi_configurationSelectionSet (mu : Measure X) [IsFiniteMeasure mu]
    (U : Set X) {n : ℕ} (S : Finset (Fin n)) :
    Measure.pi (fun j : Fin n => if j ∈ S then mu.restrict U else mu.restrict Uᶜ) =
      (Measure.pi (fun _ : Fin n => mu)).restrict (configurationSelectionSet U n S) := by
  classical
  have hset : Set.univ.pi (fun j : Fin n => if j ∈ S then U else Uᶜ) =
      configurationSelectionSet U n S := by
    ext x
    simp only [Set.mem_univ_pi, configurationSelectionSet, Set.mem_setOf_eq]
    apply forall_congr'
    intro j
    split_ifs <;> simp_all
  have hmeasure : (fun j : Fin n => if j ∈ S then mu.restrict U else mu.restrict Uᶜ) =
      fun j => mu.restrict (if j ∈ S then U else Uᶜ) := by
    funext j
    split_ifs <;> rfl
  rw [hmeasure, ← Measure.restrict_pi_pi, hset]

theorem pi_selection_restriction_rectangle (mu : Measure X) [IsFiniteMeasure mu]
    (U : Set X) {n : ℕ} (S : Finset (Fin n))
    {A B : Set (FiniteConfiguration X)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi (fun _ : Fin n => mu)
      ((configurationSubsequence S ⁻¹' A ∩ configurationSubsequence Sᶜ ⁻¹' B) ∩
        configurationSelectionSet U n S) =
      Measure.pi (fun _ : Fin S.card => mu.restrict U) (configurationMk S.card ⁻¹' A) *
        Measure.pi (fun _ : Fin Sᶜ.card => mu.restrict Uᶜ) (configurationMk Sᶜ.card ⁻¹' B) := by
  classical
  letI : Fintype S := Subtype.fintype (fun j => j ∈ S)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => X) (fun j => j ∈ S)
  let AL : Set (S → X) := {x | configurationMk S.card
    (fun j => x (S.orderIsoOfFin rfl j)) ∈ A}
  let BR : Set ({j : Fin n // j ∉ S} → X) := {x | configurationMk Sᶜ.card
    (fun j => x (configurationComplementIndex S j)) ∈ B}
  have hAL : MeasurableSet AL := (measurable_configurationMk S.card hA).preimage
    (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  have hBR : MeasurableSet BR := (measurable_configurationMk Sᶜ.card hB).preimage
    (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  letI : ∀ j : Fin n, SigmaFinite (if j ∈ S then mu.restrict U else mu.restrict Uᶜ) :=
    fun j => by split_ifs <;> infer_instance
  have hmp : MeasurePreserving e
      (Measure.pi (fun j : Fin n => if j ∈ S then mu.restrict U else mu.restrict Uᶜ))
      ((Measure.pi (fun _ : S => mu.restrict U)).prod
        (Measure.pi (fun _ : {j : Fin n // j ∉ S} => mu.restrict Uᶜ))) := by
    have h := measurePreserving_piEquivPiSubtypeProd
      (fun j : Fin n => if j ∈ S then mu.restrict U else mu.restrict Uᶜ) (fun j => j ∈ S)
    have hleft : (fun j : S => if j.val ∈ S then mu.restrict U else mu.restrict Uᶜ) =
        fun _ => mu.restrict U := by funext j; exact if_pos j.property
    have hright : (fun j : {j : Fin n // j ∉ S} =>
        if j.val ∈ S then mu.restrict U else mu.restrict Uᶜ) =
        fun _ => mu.restrict Uᶜ := by funext j; exact if_neg j.property
    rw [hleft, hright] at h
    exact h
  rw [← Measure.restrict_apply
    (((measurable_configurationSubsequence S) hA).inter
      ((measurable_configurationSubsequence Sᶜ) hB)), ← pi_configurationSelectionSet mu U S]
  have hpre : e ⁻¹' (AL ×ˢ BR) =
      configurationSubsequence S ⁻¹' A ∩ configurationSubsequence Sᶜ ⁻¹' B := by
    ext x
    rfl
  rw [← hpre, hmp.measure_preimage (hAL.prod hBR).nullMeasurableSet, Measure.prod_prod]
  exact congrArg₂ (fun a b : ℝ≥0∞ => a * b)
    (pi_reindex_event (mu.restrict U) (S.orderIsoOfFin rfl).toEquiv
      ((measurable_configurationMk S.card) hA))
    (pi_reindex_event (mu.restrict Uᶜ) (configurationComplementIndex S)
      ((measurable_configurationMk Sᶜ.card) hB))

omit [MeasurableSpace X] in
theorem configurationRestrictionIndices_compl (U : Set X) {n : ℕ} (x : Fin n → X) :
    configurationRestrictionIndices Uᶜ x = (configurationRestrictionIndices U x)ᶜ := by
  classical
  ext j
  simp

omit [MeasurableSpace X] in
theorem configurationRestriction_pair_preimage_slice (U : Set X)
    (A B : Set (FiniteConfiguration X)) (n : ℕ) :
    configurationMk n ⁻¹'
      ((configurationRestriction U ⁻¹' A) ∩ (configurationRestriction Uᶜ ⁻¹' B)) =
      ⋃ S : Finset (Fin n),
        (configurationSubsequence S ⁻¹' A ∩ configurationSubsequence Sᶜ ⁻¹' B) ∩
          configurationSelectionSet U n S := by
  classical
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.mpr ⟨configurationRestrictionIndices U x, ?_,
      (configurationRestrictionIndices_eq_iff U x _).mp rfl⟩
    refine ⟨hx.1, ?_⟩
    have hxB := hx.2
    change configurationSubsequence (configurationRestrictionIndices Uᶜ x) x ∈ B at hxB
    change configurationSubsequence _ x ∈ B
    simpa only [configurationRestrictionIndices_compl] using hxB
  · intro hx
    obtain ⟨S, hx, hS⟩ := Set.mem_iUnion.mp hx
    have hindices := (configurationRestrictionIndices_eq_iff U x S).mpr hS
    change configurationSubsequence (configurationRestrictionIndices U x) x ∈ A ∧
      configurationSubsequence (configurationRestrictionIndices Uᶜ x) x ∈ B
    rw [configurationRestrictionIndices_compl, hindices]
    exact hx

def configurationSliceMass (mu : Measure X) (A : Set (FiniteConfiguration X))
    (n : ℕ) : ℝ≥0∞ :=
  Measure.pi (fun _ : Fin n => mu) (configurationMk n ⁻¹' A)

theorem pi_configurationRestriction_rectangle (mu : Measure X) [IsFiniteMeasure mu]
    {U : Set X} (hU : MeasurableSet U) {A B : Set (FiniteConfiguration X)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    configurationSliceMass mu
      ((configurationRestriction U ⁻¹' A) ∩ (configurationRestriction Uᶜ ⁻¹' B)) n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) *
        (configurationSliceMass (mu.restrict U) A k *
          configurationSliceMass (mu.restrict Uᶜ) B (n - k)) := by
  classical
  let E : Finset (Fin n) → Set (Fin n → X) := fun S =>
    (configurationSubsequence S ⁻¹' A ∩ configurationSubsequence Sᶜ ⁻¹' B) ∩
      configurationSelectionSet U n S
  have hE (S : Finset (Fin n)) : MeasurableSet (E S) :=
    (((measurable_configurationSubsequence S) hA).inter
      ((measurable_configurationSubsequence Sᶜ) hB)).inter
        (measurableSet_configurationSelectionSet hU n S)
  have hdisj : Pairwise (fun S T => Disjoint (E S) (E T)) := by
    intro S T hST
    apply Set.disjoint_left.mpr
    intro x hxS hxT
    exact hST (((configurationRestrictionIndices_eq_iff U x S).mpr hxS.2).symm.trans
      ((configurationRestrictionIndices_eq_iff U x T).mpr hxT.2))
  unfold configurationSliceMass
  rw [configurationRestriction_pair_preimage_slice,
    measure_iUnion hdisj (fun S => hE S), tsum_fintype]
  calc
    _ = ∑ S : Finset (Fin n), configurationSliceMass (mu.restrict U) A S.card *
        configurationSliceMass (mu.restrict Uᶜ) B (n - S.card) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [pi_selection_restriction_rectangle mu U S hA hB]
      change configurationSliceMass (mu.restrict U) A S.card *
        configurationSliceMass (mu.restrict Uᶜ) B Sᶜ.card = _
      have hc : Sᶜ.card = n - S.card := by
        rw [Finset.card_compl, Fintype.card_fin]
      rw [hc]
    _ = _ := by
      change (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        configurationSliceMass (mu.restrict U) A S.card *
          configurationSliceMass (mu.restrict Uᶜ) B (n - S.card)) = _
      rw [Finset.sum_powerset]
      simp only [Finset.card_univ, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_powersetCard k (Finset.univ : Finset (Fin n))
          (fun j => configurationSliceMass (mu.restrict U) A j *
            configurationSliceMass (mu.restrict Uᶜ) B (n - j))

end Antichain
