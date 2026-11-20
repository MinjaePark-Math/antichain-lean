import Antichain.RankIndependence
import Antichain.RankCounting
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases

/-! Actual weak-Bruhat intervals, the dimension-three avoidance bijection,
and exact independent-uniform comparison probabilities. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal Topology

def permutationInversions {n : ℕ} (π : Equiv.Perm (Fin n)) : Set (Fin n × Fin n) :=
  {p | p.1 < p.2 ∧ π p.2 < π p.1}

def WeakBruhatLE {n : ℕ} (π σ : Equiv.Perm (Fin n)) : Prop :=
  permutationInversions π ⊆ permutationInversions σ

theorem weakBruhatLE_refl {n : ℕ} (π : Equiv.Perm (Fin n)) : WeakBruhatLE π π := Set.Subset.refl _

theorem weakBruhatLE_trans {n : ℕ} {π σ τ : Equiv.Perm (Fin n)}
    (hπσ : WeakBruhatLE π σ) (hστ : WeakBruhatLE σ τ) : WeakBruhatLE π τ := hπσ.trans hστ

theorem weakBruhatLE_antisymm {n : ℕ} {π σ : Equiv.Perm (Fin n)}
    (hπσ : WeakBruhatLE π σ) (hσπ : WeakBruhatLE σ π) : π = σ := by
  have hforward {α β : Equiv.Perm (Fin n)} (hαβ : WeakBruhatLE α β)
      (hβα : WeakBruhatLE β α) {k l : Fin n} (hα : α k < α l) : β k < β l := by
    by_contra hβ
    have hne : k ≠ l := fun h ↦ (ne_of_lt hα) (congrArg α h)
    have hβrev : β l < β k := lt_of_le_of_ne (le_of_not_gt hβ) (β.injective.ne hne.symm)
    by_cases hkl : k < l
    · have hαrev := hβα (show (k, l) ∈ permutationInversions β from ⟨hkl, hβrev⟩)
      exact (not_lt_of_gt hα) hαrev.2
    · have hlk : l < k := lt_of_le_of_ne (le_of_not_gt hkl) hne.symm
      have hβlt := hαβ (show (l, k) ∈ permutationInversions α from ⟨hlk, hα⟩)
      exact hβ hβlt.2
  let e : Equiv.Perm (Fin n) := π.symm.trans σ
  have he : StrictMono e := by
    intro x y hxy
    apply hforward hπσ hσπ
    simpa only [Equiv.apply_symm_apply] using hxy
  let o : Fin n ≃o Fin n := {e with map_rel_iff' := he.le_iff_le}
  have hid (x : Fin n) : e x = x := Fin.ext (Fin.coe_orderIso_apply o x)
  apply Equiv.ext
  intro k
  have hh := hid (π k)
  simpa only [e, Equiv.trans_apply, Equiv.symm_apply_apply] using hh.symm

def reversePermutationValues {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.trans Fin.revPerm

@[simp] theorem reversePermutationValues_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    reversePermutationValues π k = (π k).rev := rfl

@[simp] theorem reversePermutationValues_involutive {n : ℕ} (π : Equiv.Perm (Fin n)) :
    reversePermutationValues (reversePermutationValues π) = π := by
  ext k
  simp

theorem permutationInversions_reverse_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (k l : Fin n) :
    (k, l) ∈ permutationInversions (reversePermutationValues π) ↔ k < l ∧ π k < π l := by
  simp only [permutationInversions, mem_setOf_eq, reversePermutationValues_apply, Fin.rev_lt_rev]

theorem permutationInversions_reverse_complement {n : ℕ} (π : Equiv.Perm (Fin n)) :
    permutationInversions (reversePermutationValues π) =
      {p : Fin n × Fin n | p.1 < p.2} \ permutationInversions π := by
  ext p
  rcases p with ⟨k, l⟩
  rw [permutationInversions_reverse_iff]
  simp only [mem_diff, mem_setOf_eq, permutationInversions]
  constructor
  · rintro ⟨hkl, hp⟩
    exact ⟨hkl, fun h ↦ (not_lt_of_gt hp) h.2⟩
  · rintro ⟨hkl, hp⟩
    have hn : ¬ π l < π k := fun hh ↦ hp ⟨hkl, hh⟩
    exact ⟨hkl, lt_of_le_of_ne (le_of_not_gt hn) (π.injective.ne hkl.ne)⟩

theorem avoidsIncreasingPair_iff_weakBruhat {n : ℕ} (π : Fin 2 → Equiv.Perm (Fin n)) :
    AvoidsIncreasingPair π ↔ WeakBruhatLE (reversePermutationValues (π 1)) (π 0) := by
  constructor
  · intro h p hp
    rcases p with ⟨k, l⟩
    obtain ⟨hkl, hthird⟩ := (permutationInversions_reverse_iff (π 1) k l).mp hp
    have hnot : ¬ π 0 k < π 0 l := by
      intro hsecond
      apply h k l hkl
      intro i
      fin_cases i
      · exact hsecond
      · exact hthird
    exact ⟨hkl, lt_of_le_of_ne (le_of_not_gt hnot) ((π 0).injective.ne hkl.ne')⟩
  · intro h k l hkl hall
    have hthird := hall 1
    have hsecond := hall 0
    have hi := h ((permutationInversions_reverse_iff (π 1) k l).mpr ⟨hkl, hthird⟩)
    exact (not_lt_of_gt hi.2) hsecond

abbrev WeakBruhatInterval (n : ℕ) :=
  {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) // WeakBruhatLE p.1 p.2}

instance weakBruhatInterval_fintype (n : ℕ) : Fintype (WeakBruhatInterval n) := Fintype.ofFinite _

instance weakBruhatInterval_nonempty (n : ℕ) : Nonempty (WeakBruhatInterval n) :=
  ⟨⟨(Equiv.refl _, Equiv.refl _), Set.Subset.refl _⟩⟩

def avoidanceWeakBruhatEquiv (n : ℕ) : AvoidancePermutation n 2 ≃ WeakBruhatInterval n where
  toFun π := ⟨(reversePermutationValues (π.val 1), π.val 0),
    (avoidsIncreasingPair_iff_weakBruhat π.val).mp π.property⟩
  invFun I := ⟨![I.val.2, reversePermutationValues I.val.1],
    (avoidsIncreasingPair_iff_weakBruhat _).mpr (by simpa using I.property)⟩
  left_inv π := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  right_inv I := by
    apply Subtype.ext
    exact Prod.ext (by simp) rfl

instance avoidancePermutation3_nonempty (n : ℕ) : Nonempty (AvoidancePermutation n 2) :=
  ⟨(avoidanceWeakBruhatEquiv n).symm (Classical.choice (weakBruhatInterval_nonempty n))⟩

def weakBruhatIntervalCount (n : ℕ) : ℕ := Fintype.card (WeakBruhatInterval n)

def weakBruhatIntervalElements {n : ℕ} (I : WeakBruhatInterval n) : Set (Equiv.Perm (Fin n)) :=
  {π | WeakBruhatLE I.val.1 π ∧ WeakBruhatLE π I.val.2}

theorem weakBruhatIntervalElements_injective (n : ℕ) :
    Function.Injective (weakBruhatIntervalElements (n := n)) := by
  intro I J hIJ
  have hIl : I.val.1 ∈ weakBruhatIntervalElements I := ⟨weakBruhatLE_refl _, I.property⟩
  have hIu : I.val.2 ∈ weakBruhatIntervalElements I := ⟨I.property, weakBruhatLE_refl _⟩
  have hJl : J.val.1 ∈ weakBruhatIntervalElements J := ⟨weakBruhatLE_refl _, J.property⟩
  have hJu : J.val.2 ∈ weakBruhatIntervalElements J := ⟨J.property, weakBruhatLE_refl _⟩
  have hIlJ := hIJ ▸ hIl
  have hIuJ := hIJ ▸ hIu
  have hJlI := hIJ.symm ▸ hJl
  have hJuI := hIJ.symm ▸ hJu
  apply Subtype.ext
  exact Prod.ext (weakBruhatLE_antisymm hJlI.1 hIlJ.1) (weakBruhatLE_antisymm hIuJ.2 hJuI.2)

/-- Actual interval subsets, with duplicate endpoint representations collapsed. -/
def WeakBruhatIntervalSet (n : ℕ) :=
  {S : Set (Equiv.Perm (Fin n)) // ∃ I : WeakBruhatInterval n, weakBruhatIntervalElements I = S}

def weakBruhatIntervalSetEquiv (n : ℕ) : WeakBruhatInterval n ≃ WeakBruhatIntervalSet n :=
  Equiv.ofBijective (fun I ↦ ⟨weakBruhatIntervalElements I, ⟨I, rfl⟩⟩) (by
    constructor
    · intro I J hIJ
      exact weakBruhatIntervalElements_injective n (congrArg Subtype.val hIJ)
    · rintro ⟨S, I, hI⟩
      exact ⟨I, Subtype.ext hI⟩)

instance weakBruhatIntervalSet_fintype (n : ℕ) : Fintype (WeakBruhatIntervalSet n) :=
  Fintype.ofEquiv (WeakBruhatInterval n) (weakBruhatIntervalSetEquiv n)

theorem weakBruhatIntervalCount_eq_actual_interval_sets (n : ℕ) :
    weakBruhatIntervalCount n = Fintype.card (WeakBruhatIntervalSet n) :=
  Fintype.card_congr (weakBruhatIntervalSetEquiv n)

theorem weakBruhatIntervalCount_eq_avoidanceClassCard (n : ℕ) :
    weakBruhatIntervalCount n = avoidanceClassCard n 3 := by
  exact (Fintype.card_congr (avoidanceWeakBruhatEquiv n)).symm

theorem weakBruhatIntervalCount_pos (n : ℕ) : 0 < weakBruhatIntervalCount n := Fintype.card_pos

/-- The proved actual bijection carries uniform avoidance tuples to uniform intervals. -/
theorem avoidanceWeakBruhatEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (avoidanceWeakBruhatEquiv n)
      (PMF.uniformOfFintype (AvoidancePermutation n 2)).toMeasure
      (PMF.uniformOfFintype (WeakBruhatInterval n)).toMeasure :=
  finite_uniform_equiv_measurePreserving _

def weakBruhatPermutationPairLaw (n : ℕ) :
    Measure (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.prod
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance weakBruhatPermutationPairLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (weakBruhatPermutationPairLaw n) := by
  unfold weakBruhatPermutationPairLaw
  infer_instance

theorem weakBruhatPermutationPairLaw_eq_uniform (n : ℕ) :
    weakBruhatPermutationPairLaw n =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨l, u⟩
  calc
    _ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure {l} *
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure {u} := by
      change (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.prod
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure {(l, u)} = _
      rw [← singleton_prod_singleton, Measure.prod_prod]
    _ = _ := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
      exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))).symm

def weakBruhatComparabilityMass (n : ℕ) : ℝ≥0∞ :=
  weakBruhatPermutationPairLaw n {p | WeakBruhatLE p.1 p.2}

def weakBruhatComparabilityProbability (n : ℕ) : ℝ := (weakBruhatComparabilityMass n).toReal

/-- The comparison probability is computed under two actual independent uniform permutations. -/
theorem weakBruhatComparabilityMass_exact (n : ℕ) :
    weakBruhatComparabilityMass n = (weakBruhatIntervalCount n : ℝ≥0∞) /
      (n.factorial : ℝ≥0∞) ^ 2 := by
  letI : Fintype {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) | WeakBruhatLE p.1 p.2} :=
    weakBruhatInterval_fintype n
  unfold weakBruhatComparabilityMass
  rw [weakBruhatPermutationPairLaw_eq_uniform,
    PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Nat.cast_mul, pow_two]
  rfl

theorem weakBruhatComparabilityProbability_exact (n : ℕ) :
    weakBruhatComparabilityProbability n = (weakBruhatIntervalCount n : ℝ) / (n.factorial : ℝ) ^ 2 := by
  rw [weakBruhatComparabilityProbability, weakBruhatComparabilityMass_exact,
    ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

theorem weakBruhatComparabilityProbability_pos (n : ℕ) : 0 < weakBruhatComparabilityProbability n := by
  rw [weakBruhatComparabilityProbability_exact]
  exact div_pos (by exact_mod_cast weakBruhatIntervalCount_pos n) (by positivity)

/-- Proposition 6.3 for actual interval counts and actual iid-uniform comparisons.
The only external input is the same explicit Coxeter alcove input as the counting theorem. -/
theorem weakBruhat_counting_exponential_source (H : HumphreysAlcoveInput 3) :
    ∃ beta betaPrime : ℝ, betaPrime = Real.exp (beta - 1 / 2) ∧ 0 < betaPrime ∧
      ∃ r : ℕ → ℝ, r =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
        ∀ n : ℕ,
          (weakBruhatIntervalCount n : ℝ) = (n.factorial : ℝ) ^ ((3 : ℝ) / 2) *
            betaPrime ^ n * Real.exp (r n) ∧
          weakBruhatComparabilityProbability n = (n.factorial : ℝ) ^ (-(1 : ℝ) / 2) *
            betaPrime ^ n * Real.exp (r n) := by
  obtain ⟨beta, betaPrime, hdef, hpos, r, hr, hcount⟩ :=
    avoidance_counting_exponential_source (d := 3) (by norm_num) H
  norm_num at hdef hcount
  refine ⟨beta, betaPrime, hdef, hpos, r, hr, ?_⟩
  intro n
  have hI : (weakBruhatIntervalCount n : ℝ) =
      (n.factorial : ℝ) ^ ((3 : ℝ) / 2) * betaPrime ^ n * Real.exp (r n) := by
    rw [weakBruhatIntervalCount_eq_avoidanceClassCard]
    exact hcount n
  refine ⟨hI, ?_⟩
  rw [weakBruhatComparabilityProbability_exact, hI]
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hpow : (n.factorial : ℝ) ^ ((3 : ℝ) / 2) / (n.factorial : ℝ) ^ 2 =
      (n.factorial : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast (n.factorial : ℝ) 2, ← Real.rpow_sub hf]
    norm_num
  calc
    _ = ((n.factorial : ℝ) ^ ((3 : ℝ) / 2) / (n.factorial : ℝ) ^ 2) *
      betaPrime ^ n * Real.exp (r n) := by ring
    _ = _ := by rw [hpow]

theorem weakBruhat_counting_log_source (H : HumphreysAlcoveInput 3) :
    ∃ betaPrime : ℝ, 0 < betaPrime ∧
      ((fun n : ℕ ↦ Real.log (weakBruhatIntervalCount n : ℝ) -
        (3 / 2 : ℝ) * Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log betaPrime)
          =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ))) ∧
      ((fun n : ℕ ↦ Real.log (weakBruhatComparabilityProbability n) +
        (1 / 2 : ℝ) * Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log betaPrime)
          =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ))) := by
  obtain ⟨_, betaPrime, _, hpos, r, hr, heq⟩ := weakBruhat_counting_exponential_source H
  have hlogI (n : ℕ) : Real.log (weakBruhatIntervalCount n : ℝ) =
      (3 / 2 : ℝ) * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log betaPrime + r n := by
    rw [(heq n).1, Real.log_mul (mul_ne_zero (by positivity) (by positivity)) (Real.exp_ne_zero _),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_pow, Real.log_exp]
  have hlogP (n : ℕ) : Real.log (weakBruhatComparabilityProbability n) =
      -(1 / 2 : ℝ) * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log betaPrime + r n := by
    rw [(heq n).2, Real.log_mul (mul_ne_zero (by positivity) (by positivity)) (Real.exp_ne_zero _),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_pow, Real.log_exp]
    ring
  refine ⟨betaPrime, hpos, ?_, ?_⟩
  · convert hr using 1
    funext n
    rw [hlogI]
    ring
  · convert hr using 1
    funext n
    rw [hlogP]
    ring

end Antichain
