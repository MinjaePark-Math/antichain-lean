import Antichain.PatternSampling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort

/-! Ordered distinct label sampling equals the literal uniform subset frequency. -/

noncomputable section

namespace Antichain

open MeasureTheory Set

def PatternSubset (n q : ℕ) := {s : Finset (Fin n) // s.card = q}

instance patternSubset_fintype (n q : ℕ) : Fintype (PatternSubset n q) := by
  unfold PatternSubset
  infer_instance

def patternSubsetEnumeration {n q : ℕ} (s : PatternSubset n q) : Fin q ↪ Fin n :=
  (s.val.orderEmbOfFin s.property).toEmbedding

theorem patternSubset_card (n q : ℕ) : Fintype.card (PatternSubset n q) = n.choose q := by
  exact (Fintype.card_finset_len q).trans (congrArg (fun k ↦ k.choose q) (Fintype.card_fin n))

def subsetPermutationEmbedding {n q : ℕ} (s : PatternSubset n q) (p : Equiv.Perm (Fin q)) : Fin q ↪ Fin n :=
  p.toEmbedding.trans (patternSubsetEnumeration s)

theorem range_subsetPermutationEmbedding {n q : ℕ} (s : PatternSubset n q) (p : Equiv.Perm (Fin q)) :
    Set.range (subsetPermutationEmbedding s p) = (s.val : Set (Fin n)) := by
  change Set.range ((patternSubsetEnumeration s) ∘ p) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr p.surjective, Set.image_univ]
  exact Finset.range_orderEmbOfFin s.val s.property

theorem subsetPermutationEmbedding_bijective (n q : ℕ) :
    Function.Bijective (fun p : PatternSubset n q × Equiv.Perm (Fin q) ↦ subsetPermutationEmbedding p.1 p.2) := by
  classical
  constructor
  · rintro ⟨s, p⟩ ⟨t, r⟩ h
    have hst : s = t := by
      apply Subtype.ext
      apply Finset.coe_injective
      exact (range_subsetPermutationEmbedding s p).symm.trans
        ((congrArg (fun e : Fin q ↪ Fin n ↦ Set.range e) h).trans (range_subsetPermutationEmbedding t r))
    subst t
    have hpr : p = r := by
      apply Equiv.ext
      intro i
      exact (patternSubsetEnumeration s).injective (congrArg (fun e : Fin q ↪ Fin n ↦ e i) h)
    exact Prod.ext rfl hpr
  · intro f
    let s : PatternSubset n q := ⟨Finset.univ.map f, by simp⟩
    let ef : Fin q ≃ (s.val : Finset (Fin n)) := Equiv.ofBijective
      (fun j ↦ ⟨f j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩) (by
        constructor
        · intro i j h
          exact f.injective (congrArg Subtype.val h)
        · intro x
          obtain ⟨j, _, hj⟩ := Finset.mem_map.mp x.property
          exact ⟨j, Subtype.ext hj⟩)
    let o := s.val.orderIsoOfFin s.property
    let p : Equiv.Perm (Fin q) := ef.trans o.symm.toEquiv
    refine ⟨(s, p), ?_⟩
    apply Function.Embedding.ext
    intro j
    exact congrArg Subtype.val (o.apply_symm_apply (ef j))

def subsetPermutationEmbeddingEquiv (n q : ℕ) :
    (PatternSubset n q × Equiv.Perm (Fin q)) ≃ (Fin q ↪ Fin n) :=
  Equiv.ofBijective _ (subsetPermutationEmbedding_bijective n q)

def goodInjectionEmbeddingEquiv (n q : ℕ) (Q : Set (Fin q → Fin n)) :
    {f : Fin q → Fin n // Function.Injective f ∧ f ∈ Q} ≃
      {e : Fin q ↪ Fin n // (e : Fin q → Fin n) ∈ Q} where
  toFun f := ⟨⟨f.val, f.property.1⟩, f.property.2⟩
  invFun e := ⟨e.val, e.val.injective, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem invariant_injection_count (n q : ℕ) (Q : Set (Fin q → Fin n))
    (hQ : ∀ (f : Fin q → Fin n) (p : Equiv.Perm (Fin q)), f ∘ p ∈ Q ↔ f ∈ Q) :
    Nat.card {f : Fin q → Fin n // Function.Injective f ∧ f ∈ Q} =
      Nat.card {s : PatternSubset n q // (patternSubsetEnumeration s : Fin q → Fin n) ∈ Q} * q.factorial := by
  let e := subsetPermutationEmbeddingEquiv n q
  have he (p : PatternSubset n q × Equiv.Perm (Fin q)) :
      (patternSubsetEnumeration p.1 : Fin q → Fin n) ∈ Q ↔ (e p : Fin q → Fin n) ∈ Q :=
    (hQ (patternSubsetEnumeration p.1) p.2).symm
  let er : {p : PatternSubset n q × Equiv.Perm (Fin q) //
      (patternSubsetEnumeration p.1 : Fin q → Fin n) ∈ Q} ≃
      {f : Fin q ↪ Fin n // (f : Fin q → Fin n) ∈ Q} := e.subtypeEquiv he
  let eg := (goodInjectionEmbeddingEquiv n q Q).trans
    (er.symm.trans (Equiv.prodSubtypeFstEquivSubtypeProd
      (α := PatternSubset n q) (β := Equiv.Perm (Fin q))
      (p := fun s ↦ (patternSubsetEnumeration s : Fin q → Fin n) ∈ Q)))
  have hc := Nat.card_congr eg
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin q)), Fintype.card_perm, Fintype.card_fin] at hc
  exact hc

def patternSubsetFrequency (n q : ℕ) (Q : Set (Fin q → Fin n)) : ℝ :=
  (Nat.card {s : PatternSubset n q // (patternSubsetEnumeration s : Fin q → Fin n) ∈ Q} : ℝ) /
    (n.choose q : ℝ)

/-- The conventional normalized q-subset frequency equals actual distinct ordered sampling.
The formula also gives zero when q>n and the unique empty-subset convention when q=0. -/
theorem injectionPatternLabelLaw_eq_subset_frequency (n q : ℕ) (Q : Set (Fin q → Fin n))
    (hQ : ∀ (f : Fin q → Fin n) (p : Equiv.Perm (Fin q)), f ∘ p ∈ Q ↔ f ∈ Q) :
    (injectionPatternLabelLaw n q).real Q = patternSubsetFrequency n q Q := by
  rw [injectionPatternLabelLaw_count_descFactorial, invariant_injection_count n q Q hQ,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul]
  unfold patternSubsetFrequency
  rw [mul_comm (q.factorial : ℝ) (n.choose q : ℝ)]
  exact mul_div_mul_right _ _ (by positivity : (q.factorial : ℝ) ≠ 0)

end Antichain
