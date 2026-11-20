import Antichain.WeakBruhatIntervals
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! The actual random intersection order and its linear-extension expectation identity. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The strict order obtained by intersecting the actual ranking orders. -/
def intersectionRankLT {n k : ℕ} (π : Fin k → Equiv.Perm (Fin n)) (a b : Fin n) : Prop :=
  ∀ i, (π i a).val < (π i b).val

/-- This is genuinely a partial order when at least one linear order is intersected. -/
def intersectionRankingOrder {n k : ℕ} (hk : 0 < k) (π : Fin k → Equiv.Perm (Fin n)) : PartialOrder (Fin n) where
  le a b := ∀ i, (π i a).val ≤ (π i b).val
  lt := intersectionRankLT π
  le_refl _ _ := Nat.le_refl _
  le_trans _ _ _ hab hbc i := Nat.le_trans (hab i) (hbc i)
  le_antisymm _ _ hab hba := (π ⟨0, hk⟩).injective (Fin.ext (Nat.le_antisymm (hab _) (hba _)))
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      exact ⟨fun i ↦ (h i).le, fun hr ↦ (Nat.not_le_of_lt (h ⟨0, hk⟩)) (hr _)⟩
    · rintro ⟨hle, hn⟩ i
      have hab : a ≠ b := fun heq ↦ hn (by simpa only [heq] using hle)
      exact Nat.lt_of_le_of_ne (hle i) (fun heq ↦ hab ((π i).injective (Fin.ext heq)))

/-- A linear extension is an actual bijective total ranking respecting every comparison. -/
def PosetLinearExtension {n k : ℕ} (π : Fin k → Equiv.Perm (Fin n)) :=
  {τ : Equiv.Perm (Fin n) // ∀ a b, intersectionRankLT π a b → (τ a).val < (τ b).val}

instance posetLinearExtension_fintype {n k : ℕ} (π : Fin k → Equiv.Perm (Fin n)) :
    Fintype (PosetLinearExtension π) := by
  unfold PosetLinearExtension
  exact Fintype.ofFinite _

def posetLinearExtensionCount {n k : ℕ} (π : Fin k → Equiv.Perm (Fin n)) : ℕ :=
  Fintype.card (PosetLinearExtension π)

/-- Independent uniform total ranking orders: the literal P_k(n) model. -/
def randomIntersectionOrderLaw (n k : ℕ) : Measure (Fin k → Equiv.Perm (Fin n)) :=
  Measure.pi (fun _ : Fin k ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)

instance randomIntersectionOrderLaw_isProbabilityMeasure (n k : ℕ) :
    IsProbabilityMeasure (randomIntersectionOrderLaw n k) := by unfold randomIntersectionOrderLaw; infer_instance

def rankingTupleAntichain {n d : ℕ} (r : Fin d → Equiv.Perm (Fin n)) : Prop :=
  ∀ a b : Fin n, a ≠ b → ¬ ∀ i, (r i a).val < (r i b).val

def FullRankingAntichain (n d : ℕ) :=
  {r : Fin d → Equiv.Perm (Fin n) // rankingTupleAntichain r}

instance fullRankingAntichain_fintype (n d : ℕ) : Fintype (FullRankingAntichain n d) := by
  unfold FullRankingAntichain
  exact Fintype.ofFinite _

theorem cube_antichain_iff_full_ranks (n d : ℕ) (x : CubeSample n d)
    (hx : CoordinateTieFree n d x) :
    IsAntichain x ↔ rankingTupleAntichain (coordinateRankPermutations n d x) := by
  have hcoord (i : Fin d) (a b : Fin n) :
      coordinateRankPermutations n d x i a < coordinateRankPermutations n d x i b ↔ x a i < x b i :=
    sampleRankPermutation_lt_iff (fun j ↦ x j i) (hx i) a b
  constructor
  · intro h a b hab hlt
    exact h a b hab (fun i ↦ (hcoord i a b).mp (hlt i))
  · intro h a b hab hlt
    exact h a b hab (fun i ↦ (hcoord i a b).mpr (hlt i))

theorem antichainMass_eq_full_rank_count (n d : ℕ) :
    antichainMass n d = (Fintype.card (FullRankingAntichain n d) : ℝ≥0∞) / (n.factorial : ℝ≥0∞) ^ d := by
  let E : Set (Fin d → Equiv.Perm (Fin n)) := {r | rankingTupleAntichain r}
  letI : Fintype E := fullRankingAntichain_fintype n d
  have hae : strictAntichainEvent n d =ᵐ[cubeSampleLaw n d]
      (coordinateRankPermutations n d) ⁻¹' E := by
    filter_upwards [cubeSample_coordinateTieFree_ae n d] with x hx
    exact propext (cube_antichain_iff_full_ranks n d x hx)
  change cubeSampleLaw n d (strictAntichainEvent n d) = _
  rw [measure_congr hae, ← Measure.map_apply (coordinateRankPermutations_measurable n d) E.toFinite.measurableSet,
    cube_coordinateRanks_uniform_law]
  change (Measure.pi (fun _ : Fin d ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)) E = _
  rw [finite_uniform_pi_law, PMF.toMeasure_uniformOfFintype_apply E E.toFinite.measurableSet]
  simp only [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Nat.cast_pow]
  rfl

theorem antichainProbability_eq_full_rank_count (n d : ℕ) :
    antichainProbability n d = (Fintype.card (FullRankingAntichain n d) : ℝ) / (n.factorial : ℝ) ^ d := by
  rw [antichainProbability, antichainMass_eq_full_rank_count, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

def linearExtensionFullRankPairEquiv (n k : ℕ) (hk : 0 < k) :
    {p : (Fin k → Equiv.Perm (Fin n)) × Equiv.Perm (Fin n) //
      ∀ a b, intersectionRankLT p.1 a b → (p.2 a).val < (p.2 b).val} ≃ FullRankingAntichain n (k + 1) where
  toFun p := ⟨Fin.snoc p.val.1 (reversePermutationValues p.val.2), by
    intro a b hab hall
    have hfirst : intersectionRankLT p.val.1 a b := fun i ↦ by
      simpa only [Fin.snoc_castSucc] using hall i.castSucc
    have hlast : reversePermutationValues p.val.2 a < reversePermutationValues p.val.2 b := by
      simpa only [Fin.snoc_last] using hall (Fin.last k)
    have hext := p.property a b hfirst
    have hrev : p.val.2 b < p.val.2 a := Fin.rev_lt_rev.mp hlast
    exact (not_lt_of_gt hext) hrev⟩
  invFun r := ⟨(Fin.init r.val, reversePermutationValues (r.val (Fin.last k))), by
    intro a b hfirst
    have hab : a ≠ b := fun heq ↦ (Nat.ne_of_lt (hfirst ⟨0, hk⟩)) (by rw [heq])
    have hn : ¬ r.val (Fin.last k) a < r.val (Fin.last k) b := by
      intro hlast
      apply r.property a b hab
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact hlast
      · exact hfirst j
    apply Fin.rev_lt_rev.mpr
    exact lt_of_le_of_ne (le_of_not_gt hn) ((r.val (Fin.last k)).injective.ne hab.symm)⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change Fin.init (Fin.snoc (α := fun _ : Fin (k + 1) ↦ Equiv.Perm (Fin n))
        p.val.1 (reversePermutationValues p.val.2)) = p.val.1
      exact Fin.init_snoc _ _
    · simp only [Fin.snoc_last, reversePermutationValues_involutive]
  right_inv r := by
    apply Subtype.ext
    simpa only [reversePermutationValues_involutive] using Fin.snoc_init_self r.val

def linearExtensionFullRankEquiv (n k : ℕ) (hk : 0 < k) :
    (Σ π : Fin k → Equiv.Perm (Fin n), PosetLinearExtension π) ≃ FullRankingAntichain n (k + 1) :=
  (Equiv.subtypeProdEquivSigmaSubtype (fun (π : Fin k → Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin n)) ↦
    ∀ a b, intersectionRankLT π a b → (τ a).val < (τ b).val)).symm.trans
      (linearExtensionFullRankPairEquiv n k hk)

theorem sum_posetLinearExtensionCount (n k : ℕ) (hk : 0 < k) :
    (∑ π : Fin k → Equiv.Perm (Fin n), posetLinearExtensionCount π) =
      Fintype.card (FullRankingAntichain n (k + 1)) := by
  simpa only [Fintype.card_sigma, posetLinearExtensionCount] using
    Fintype.card_congr (linearExtensionFullRankEquiv n k hk)

theorem expected_posetLinearExtensionCount (n k : ℕ) :
    (∫ π, (posetLinearExtensionCount π : ℝ) ∂randomIntersectionOrderLaw n k) =
      (∑ π : Fin k → Equiv.Perm (Fin n), (posetLinearExtensionCount π : ℝ)) /
        (n.factorial : ℝ) ^ k := by
  rw [randomIntersectionOrderLaw, finite_uniform_pi_law, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Nat.cast_pow, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- The introduction's exact random-poset formula, for the actual random
intersection of k independent uniform orders and its actual extension count. -/
theorem antichainProbability_eq_expected_linearExtensions (n k : ℕ) (hk : 0 < k) :
    antichainProbability n (k + 1) =
      (∫ π, (posetLinearExtensionCount π : ℝ) ∂randomIntersectionOrderLaw n k) / (n.factorial : ℝ) := by
  rw [expected_posetLinearExtensionCount, antichainProbability_eq_full_rank_count]
  have hc := congrArg (fun a : ℕ ↦ (a : ℝ)) (sum_posetLinearExtensionCount n k hk)
  simp only [Nat.cast_sum] at hc
  rw [hc, pow_succ]
  ring

theorem antichainProbability_random_poset_source (n d : ℕ) (hd : 2 ≤ d) :
    antichainProbability n d =
      (∫ π, (posetLinearExtensionCount π : ℝ) ∂randomIntersectionOrderLaw n (d - 1)) /
        (n.factorial : ℝ) := by
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using
    antichainProbability_eq_expected_linearExtensions n (d - 1) (by omega)

end Antichain
