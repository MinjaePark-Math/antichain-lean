import Antichain.RankIndependence
import Antichain.FiniteConditioning
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Measure.Real

/-! Actual with- and without-replacement label sampling and the collision error. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

theorem conditional_probability_error_le_complement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {D E : Set Ω}
    (hD : MeasurableSet D) :
    |μ.real E - (ProbabilityTheory.cond μ D).real E| ≤ μ.real Dᶜ := by
  have hn := congrArg ENNReal.toReal (cond_mul_eq_inter hD E μ)
  simp only [ENNReal.toReal_mul, ← measureReal_def] at hn
  rw [Set.inter_comm D E] at hn
  have hs := measureReal_inter_add_diff (μ := μ) (s := E) hD
  have hcomp : μ.real Dᶜ = 1 - μ.real D := by rw [measureReal_compl hD]; simp
  have hb0 : 0 ≤ μ.real (E \ D) := measureReal_nonneg
  have hb1 : μ.real (E \ D) ≤ μ.real Dᶜ :=
    measureReal_mono (fun _ hx ↦ hx.2)
  have ha0 : 0 ≤ (ProbabilityTheory.cond μ D).real E := measureReal_nonneg
  have ha1 : (ProbabilityTheory.cond μ D).real E ≤ 1 := measureReal_le_one
  have hq0 : 0 ≤ μ.real Dᶜ := measureReal_nonneg
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hq0 ha0, mul_nonneg hq0 (sub_nonneg.mpr ha1)]

def distinctPatternLabelSet (n q : ℕ) : Set (Fin q → Fin n) := {f | Function.Injective f}

def iidPatternLabelLaw (n q : ℕ) [NeZero n] : Measure (Fin q → Fin n) :=
  Measure.pi (fun _ : Fin q ↦ (PMF.uniformOfFintype (Fin n)).toMeasure)

instance iidPatternLabelLaw_isProbabilityMeasure (n q : ℕ) [NeZero n] :
    IsProbabilityMeasure (iidPatternLabelLaw n q) := by unfold iidPatternLabelLaw; infer_instance

def injectionPatternLabelLaw (n q : ℕ) : Measure (Fin q → Fin n) := uniformOn (distinctPatternLabelSet n q)

theorem iidPatternLabelLaw_eq_uniform (n q : ℕ) [NeZero n] :
    iidPatternLabelLaw n q = (PMF.uniformOfFintype (Fin q → Fin n)).toMeasure := finite_uniform_pi_law

theorem iidPatternLabelLaw_condition_distinct (n q : ℕ) [NeZero n] :
    ProbabilityTheory.cond (iidPatternLabelLaw n q) (distinctPatternLabelSet n q) =
      injectionPatternLabelLaw n q := by
  rw [iidPatternLabelLaw_eq_uniform]
  exact finite_uniform_restrict_normalize_eq_uniformOn _

theorem distinctPatternLabelSet_nonempty {n q : ℕ} (hqn : q ≤ n) : (distinctPatternLabelSet n q).Nonempty :=
  ⟨Fin.castLEEmb hqn, (Fin.castLEEmb hqn).injective⟩

theorem iidPatternLabelLaw_distinct_pos {n q : ℕ} [NeZero n] (hqn : q ≤ n) :
    0 < iidPatternLabelLaw n q (distinctPatternLabelSet n q) := by
  obtain ⟨f, hf⟩ := distinctPatternLabelSet_nonempty hqn
  have hs : 0 < iidPatternLabelLaw n q {f} := by
    rw [iidPatternLabelLaw_eq_uniform, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  exact hs.trans_le (measure_mono (Set.singleton_subset_iff.mpr hf))

theorem injectionPatternLabelLaw_isProbabilityMeasure {n q : ℕ} (hqn : q ≤ n) :
    IsProbabilityMeasure (injectionPatternLabelLaw n q) :=
  uniformOn_isProbabilityMeasure (Set.toFinite _) (distinctPatternLabelSet_nonempty hqn)

def patternEmbeddingFunctionEquiv (n q : ℕ) :
    (Fin q ↪ Fin n) ≃ distinctPatternLabelSet n q where
  toFun e := ⟨e, e.injective⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem iidPatternLabelLaw_pair_collision (n q : ℕ) [NeZero n]
    {i j : Fin q} (hij : i ≠ j) :
    iidPatternLabelLaw n q {f | f i = f j} = (n : ℝ≥0∞)⁻¹ := by
  classical
  let μ := iidPatternLabelLaw n q
  have hind : IndepFun (fun f : Fin q → Fin n ↦ f i) (fun f ↦ f j) μ :=
    (iIndepFun_pi (X := fun _ : Fin q ↦ (id : Fin n → Fin n))
      (fun _ ↦ measurable_id.aemeasurable)).indepFun hij
  have heval (k : Fin q) (a : Fin n) : μ ((fun f : Fin q → Fin n ↦ f k) ⁻¹' {a}) = (n : ℝ≥0∞)⁻¹ := by
    change iidPatternLabelLaw n q ((fun f ↦ f k) ⁻¹' {a}) = _
    rw [← Measure.map_apply (measurable_pi_apply k) (measurableSet_singleton a),
      show (iidPatternLabelLaw n q).map (fun f ↦ f k) = (PMF.uniformOfFintype (Fin n)).toMeasure from
        (measurePreserving_eval (fun _ : Fin q ↦ (PMF.uniformOfFintype (Fin n)).toMeasure) k).map_eq,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply, Fintype.card_fin]
  let E : Fin n → Set (Fin q → Fin n) := fun a ↦ {f | f i = a} ∩ {f | f j = a}
  have heq : {f : Fin q → Fin n | f i = f j} = ⋃ a, E a := by
    ext f
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨f i, rfl, h.symm⟩
    · intro h
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp h
      exact ha.1.trans ha.2.symm
  have hdisj : Pairwise (fun a b ↦ Disjoint (E a) (E b)) := by
    intro a b hab
    exact Set.disjoint_left.mpr (fun _ ha hb ↦ hab (ha.1.symm.trans hb.1))
  have hmass (a : Fin n) : μ (E a) = (n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ := by
    change μ ((fun f : Fin q → Fin n ↦ f i) ⁻¹' {a} ∩ (fun f ↦ f j) ⁻¹' {a}) = _
    rw [hind.measure_inter_preimage_eq_mul {a} {a} (measurableSet_singleton a) (measurableSet_singleton a),
      heval, heval]
  change μ _ = _
  rw [heq, measure_iUnion hdisj (fun a ↦ (Set.toFinite (E a)).measurableSet), tsum_fintype]
  simp only [hmass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top _), one_mul]

theorem iidPatternLabelLaw_collision_bound (n q : ℕ) [NeZero n] :
    iidPatternLabelLaw n q (distinctPatternLabelSet n q)ᶜ ≤ (q.choose 2 : ℝ≥0∞) / (n : ℝ≥0∞) := by
  classical
  let T := (Finset.univ : Finset (Fin q)).powersetCard 2
  let E : Finset (Fin q) → Set (Fin q → Fin n) := fun s ↦ {f | ∀ i ∈ s, ∀ j ∈ s, f i = f j}
  have hmass (s : Finset (Fin q)) (hs : s ∈ T) :
      iidPatternLabelLaw n q (E s) = (n : ℝ≥0∞)⁻¹ := by
    have hcard := (Finset.mem_powersetCard.mp hs).2
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
    have heq : E {i, j} = {f : Fin q → Fin n | f i = f j} := by
      ext f
      simp only [E, mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [heq]
    exact iidPatternLabelLaw_pair_collision n q hij
  have hcover : (distinctPatternLabelSet n q)ᶜ = ⋃ s ∈ T, E s := by
    ext f
    constructor
    · intro hf
      have hf : ¬ Function.Injective f := hf
      obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hf
      refine Set.mem_iUnion.mpr ⟨{i, j}, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp [hij]⟩
      · simp only [E, mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
        aesop
    · intro hf hinj
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hf
      obtain ⟨hs, hsf⟩ := Set.mem_iUnion.mp hs
      obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
      exact hij (hinj (hsf i (by simp) j (by simp)))
  rw [hcover]
  apply (measure_biUnion_finset_le T E).trans_eq
  calc
    _ = ∑ _s ∈ T, (n : ℝ≥0∞)⁻¹ := Finset.sum_congr rfl hmass
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, T, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, div_eq_mul_inv]

theorem iidPatternLabelLaw_collision_real_bound (n q : ℕ) [NeZero n] :
    (iidPatternLabelLaw n q).real (distinctPatternLabelSet n q)ᶜ ≤ (q.choose 2 : ℝ) / n := by
  have h := ENNReal.toReal_mono
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast NeZero.ne n))
    (iidPatternLabelLaw_collision_bound n q)
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_natCast] using h

theorem cond_event_eq_of_ae_on {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {D P Q : Set Ω} (hD : MeasurableSet D)
    (h : ∀ᵐ x ∂μ, x ∈ D → (x ∈ P ↔ x ∈ Q)) :
    ProbabilityTheory.cond μ D P = ProbabilityTheory.cond μ D Q := by
  rw [cond_apply hD, cond_apply hD]
  congr 1
  apply measure_congr
  filter_upwards [h] with x hx
  exact propext (and_congr_right (fun hD ↦ hx hD))

theorem cond_prod_fst_event {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {D Q : Set Ω} (hD : MeasurableSet D) (hQ : MeasurableSet Q) :
    ProbabilityTheory.cond (μ.prod ν) (Prod.fst ⁻¹' D) (Prod.fst ⁻¹' Q) =
      ProbabilityTheory.cond μ D Q := by
  have hfst : MeasurePreserving (Prod.fst : Ω × Y → Ω) (μ.prod ν) μ := measurePreserving_fst
  rw [cond_apply (hD.preimage measurable_fst), cond_apply hD, ← Set.preimage_inter,
    hfst.measure_preimage hD.nullMeasurableSet,
    hfst.measure_preimage (hD.inter hQ).nullMeasurableSet]

/-- The actual sampling-with-replacement error for any event with auxiliary
independent randomness. Agreement is required only almost surely on distinct labels. -/
theorem iid_injection_aux_event_error (n q : ℕ) [NeZero n]
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (P : Set ((Fin q → Fin n) × Y)) (Q : Set (Fin q → Fin n))
    (hagree : ∀ᵐ z ∂(iidPatternLabelLaw n q).prod ν,
      Function.Injective z.1 → (z ∈ P ↔ z.1 ∈ Q)) :
    |((iidPatternLabelLaw n q).prod ν).real P - (injectionPatternLabelLaw n q).real Q| ≤
      (q.choose 2 : ℝ) / n := by
  let μ := (iidPatternLabelLaw n q).prod ν
  let D := (Prod.fst : ((Fin q → Fin n) × Y) → (Fin q → Fin n)) ⁻¹' distinctPatternLabelSet n q
  have hDl : MeasurableSet (distinctPatternLabelSet n q) := (Set.toFinite _).measurableSet
  have hD : MeasurableSet D := hDl.preimage measurable_fst
  have hQ : MeasurableSet Q := Q.toFinite.measurableSet
  have heq : (ProbabilityTheory.cond μ D).real P = (injectionPatternLabelLaw n q).real Q := by
    change (ProbabilityTheory.cond μ D P).toReal = _
    rw [cond_event_eq_of_ae_on μ hD hagree]
    change (ProbabilityTheory.cond ((iidPatternLabelLaw n q).prod ν)
      (Prod.fst ⁻¹' distinctPatternLabelSet n q) (Prod.fst ⁻¹' Q)).toReal = _
    rw [cond_prod_fst_event (iidPatternLabelLaw n q) ν hDl hQ, iidPatternLabelLaw_condition_distinct]
    rfl
  have herr := conditional_probability_error_le_complement μ (E := P) hD
  rw [heq] at herr
  apply herr.trans
  have hfst : MeasurePreserving (Prod.fst : ((Fin q → Fin n) × Y) → (Fin q → Fin n)) μ
      (iidPatternLabelLaw n q) := measurePreserving_fst
  have hc : μ.real Dᶜ = (iidPatternLabelLaw n q).real (distinctPatternLabelSet n q)ᶜ := by
    change μ.real (Prod.fst ⁻¹' (distinctPatternLabelSet n q)ᶜ) = _
    exact hfst.measureReal_preimage hDl.compl.nullMeasurableSet
  rw [hc]
  exact iidPatternLabelLaw_collision_real_bound n q

theorem iid_injection_event_error (n q : ℕ) [NeZero n] (Q : Set (Fin q → Fin n)) :
    |(iidPatternLabelLaw n q).real Q - (injectionPatternLabelLaw n q).real Q| ≤ (q.choose 2 : ℝ) / n := by
  have hD : MeasurableSet (distinctPatternLabelSet n q) := (Set.toFinite _).measurableSet
  have h := conditional_probability_error_le_complement (iidPatternLabelLaw n q) (E := Q) hD
  rw [iidPatternLabelLaw_condition_distinct] at h
  exact h.trans (iidPatternLabelLaw_collision_real_bound n q)

theorem count_finite_set_eq_ncard {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K]
    (C : Set K) (hC : C.Finite) : (Measure.count : Measure K) C = (C.ncard : ℝ≥0∞) := by
  rw [Measure.count_apply_finite C hC, Set.ncard_eq_toFinset_card C hC]

theorem injectionPatternLabelLaw_count_formula (n q : ℕ) (Q : Set (Fin q → Fin n)) :
    (injectionPatternLabelLaw n q).real Q =
      (((distinctPatternLabelSet n q ∩ Q).ncard : ℝ) / (distinctPatternLabelSet n q).ncard) := by
  rw [measureReal_def, injectionPatternLabelLaw, uniformOn,
    cond_apply (Set.toFinite _).measurableSet,
    count_finite_set_eq_ncard _ (Set.toFinite _), count_finite_set_eq_ncard _ (Set.toFinite _),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  ring

theorem distinctPatternLabelSet_ncard (n q : ℕ) :
    (distinctPatternLabelSet n q).ncard = n.descFactorial q := by
  letI : Fintype (Fin q ↪ Fin n) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (patternEmbeddingFunctionEquiv n q),
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-- Literal normalized finite injection count, including the zero-class convention. -/
theorem injectionPatternLabelLaw_count_descFactorial (n q : ℕ) (Q : Set (Fin q → Fin n)) :
    (injectionPatternLabelLaw n q).real Q =
      (Nat.card {f : Fin q → Fin n // Function.Injective f ∧ f ∈ Q} : ℝ) / (n.descFactorial q : ℝ) := by
  rw [injectionPatternLabelLaw_count_formula, distinctPatternLabelSet_ncard]
  rfl

end Antichain
