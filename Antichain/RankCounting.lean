import Antichain.RankIndependence
import Antichain.WeightedLimit
import Mathlib.Data.Fin.Rev

/-! Exact reflection bijections and actual enumeration asymptotics. -/

noncomputable section

namespace Antichain

open Filter Asymptotics
open scoped Topology BoundedContinuousFunction

def reflectRankTuple {n m : ℕ} (sign : Fin m → Bool)
    (pi : Fin m → Equiv.Perm (Fin n)) : Fin m → Equiv.Perm (Fin n) :=
  fun i => if sign i then pi i else (pi i).trans Fin.revPerm

theorem reflectRankTuple_involutive {n m : ℕ} (sign : Fin m → Bool) :
    Function.Involutive (reflectRankTuple (n := n) sign) := by
  intro pi
  funext i
  apply Equiv.ext
  intro j
  cases hs : sign i <;> simp [reflectRankTuple, hs, Equiv.trans_apply]

def AvoidsSignedPair {n m : ℕ} (sign : Fin m → Bool) (pi : Fin m → Equiv.Perm (Fin n)) : Prop :=
  ∀ j k : Fin n, j < k → ¬ ∀ i : Fin m,
    if sign i then pi i j < pi i k else pi i k < pi i j

theorem avoidsSignedPair_iff_reflect {n m : ℕ} (sign : Fin m → Bool)
    (pi : Fin m → Equiv.Perm (Fin n)) :
    AvoidsSignedPair sign pi ↔ AvoidsIncreasingPair (reflectRankTuple sign pi) := by
  unfold AvoidsSignedPair AvoidsIncreasingPair
  apply forall_congr'
  intro j
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hjk
  apply not_congr
  apply forall_congr'
  intro i
  cases hs : sign i <;> simp [reflectRankTuple, hs, Equiv.trans_apply, Fin.rev_lt_rev]

abbrev SignedAvoidancePermutation (n m : ℕ) (sign : Fin m → Bool) :=
  {pi : Fin m → Equiv.Perm (Fin n) // AvoidsSignedPair sign pi}

instance signedAvoidancePermutation_fintype (n m : ℕ) (sign : Fin m → Bool) :
    Fintype (SignedAvoidancePermutation n m sign) := Fintype.ofFinite _

/-- Reversing precisely the decreasing coordinates is a literal bijection from
avoidance of any prescribed two-point orientation to increasing-pair avoidance. -/
def signedAvoidanceEquiv (n m : ℕ) (sign : Fin m → Bool) :
    SignedAvoidancePermutation n m sign ≃ AvoidancePermutation n m where
  toFun pi := ⟨reflectRankTuple sign pi.val, (avoidsSignedPair_iff_reflect sign pi.val).mp pi.property⟩
  invFun pi := ⟨reflectRankTuple sign pi.val, (avoidsSignedPair_iff_reflect sign _).mpr
    (by rw [reflectRankTuple_involutive]; exact pi.property)⟩
  left_inv pi := Subtype.ext (reflectRankTuple_involutive sign pi.val)
  right_inv pi := Subtype.ext (reflectRankTuple_involutive sign pi.val)

theorem signed_avoidance_card_eq (n m : ℕ) (sign : Fin m → Bool) :
    Fintype.card (SignedAvoidancePermutation n m sign) = Fintype.card (AvoidancePermutation n m) :=
  Fintype.card_congr (signedAvoidanceEquiv n m sign)

theorem dimension_two_avoidance_unique (n : ℕ) (pi : AvoidancePermutation n 1) :
    pi.val = fun _ : Fin 1 => Fin.revPerm := by
  have hanti : StrictAnti (pi.val 0) := by
    intro j k hjk
    have hnlt : ¬ pi.val 0 j < pi.val 0 k := by
      intro hlt
      apply pi.property j k hjk
      intro i
      simpa only [Subsingleton.elim i 0] using hlt
    have hne : pi.val 0 k ≠ pi.val 0 j :=
      fun hh => (ne_of_lt hjk) ((pi.val 0).injective hh.symm)
    exact lt_of_le_of_ne (le_of_not_gt hnlt) hne
  have hval : (pi.val 0 : Fin n → Fin n) = Fin.rev := by
    apply (hanti.range_inj Fin.rev_strictAnti).mp
    rw [Set.range_eq_univ.mpr (pi.val 0).surjective, Set.range_eq_univ.mpr Fin.rev_surjective]
  funext i
  apply Equiv.ext
  intro j
  simpa only [Subsingleton.elim i 0, Fin.revPerm_apply] using congrFun hval j

theorem avoidanceClassCard_dimension_two (n : ℕ) : avoidanceClassCard n 2 = 1 := by
  have hrev : AvoidsIncreasingPair (fun _ : Fin 1 => (Fin.revPerm : Equiv.Perm (Fin n))) := by
    intro j k hjk h
    exact (not_lt_of_gt (Fin.rev_strictAnti hjk)) (h 0)
  change Fintype.card (AvoidancePermutation n 1) = 1
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨fun _ => Fin.revPerm, hrev⟩, ?_⟩
  intro pi
  exact Subtype.ext (dimension_two_avoidance_unique n pi)

/-- Proposition 6.2's actual enumeration statement in exact logarithmic
little-o form. The same beta as in the actual cube-probability asymptotic is
used, with beta-prime equal to exp(beta - 1/(d-1)). -/
theorem avoidance_counting_source {d : ℕ} [NeZero d] (hd : 2 ≤ d) (H : HumphreysAlcoveInput d) :
    ∃ beta : ℝ,
      ((fun n : ℕ => Real.log (antichainProbability n d) +
        (n : ℝ) / ((d : ℝ) - 1) * Real.log (n : ℝ) - beta * (n : ℝ))
          =o[atTop] (fun n : ℕ => (n : ℝ))) ∧
      (let betaPrime := Real.exp (beta - 1 / ((d : ℝ) - 1))
       0 < betaPrime ∧
       (fun n : ℕ => Real.log (avoidanceClassCard n d : ℝ) -
         ((d : ℝ) - 1 - 1 / ((d : ℝ) - 1)) * Real.log (n.factorial : ℝ) -
         (n : ℝ) * Real.log betaPrime) =o[atTop] (fun n : ℕ => (n : ℝ))) := by
  obtain ⟨beta, hbeta⟩ := antichain_counting_source hd H
  refine ⟨beta, hbeta, Real.exp_pos _, ?_⟩
  have hcount (n : ℕ) : (avoidanceClassCard n d : ℝ) =
      (n.factorial : ℝ) ^ ((d : ℝ) - 1) * antichainProbability n d := by
    have hcast : (d : ℝ) - 1 = ((d - 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ d)).symm
    rw [hcast, Real.rpow_natCast]
    exact avoidanceClassCard_exact n d (by omega)
  simpa only [Real.log_exp] using counting_conversion_from_log_probability (d : ℝ) beta
    (fun n => antichainProbability n d) (fun n => (avoidanceClassCard n d : ℝ))
    (fun n => antichainProbability_pos n d hd) hcount hbeta

theorem avoidance_counting_exponential_source {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) :
    ∃ beta betaPrime : ℝ, betaPrime = Real.exp (beta - 1 / ((d : ℝ) - 1)) ∧
      0 < betaPrime ∧ ∃ r : ℕ → ℝ,
        r =o[atTop] (fun n : ℕ => (n : ℝ)) ∧
        ∀ n : ℕ, (avoidanceClassCard n d : ℝ) =
          (n.factorial : ℝ) ^ ((d : ℝ) - 1 - 1 / ((d : ℝ) - 1)) *
            betaPrime ^ n * Real.exp (r n) := by
  obtain ⟨beta, _, hpos, hrem⟩ := avoidance_counting_source hd H
  let betaPrime := Real.exp (beta - 1 / ((d : ℝ) - 1))
  let q := (d : ℝ) - 1 - 1 / ((d : ℝ) - 1)
  let r : ℕ → ℝ := fun n => Real.log (avoidanceClassCard n d : ℝ) -
    q * Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log betaPrime
  refine ⟨beta, betaPrime, rfl, hpos, r, hrem, ?_⟩
  intro n
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hcard : 0 < (avoidanceClassCard n d : ℝ) := by
    rw [avoidanceClassCard_exact n d (by omega)]
    exact mul_pos (pow_pos hf _) (antichainProbability_pos n d hd)
  have hbpow : betaPrime ^ n = Real.exp ((n : ℝ) * Real.log betaPrime) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  rw [Real.rpow_def_of_pos hf, hbpow, ← Real.exp_add, ← Real.exp_add]
  rw [show Real.log (n.factorial : ℝ) * q + (n : ℝ) * Real.log betaPrime + r n =
      Real.log (avoidanceClassCard n d : ℝ) by dsimp [r]; ring,
    Real.exp_log hcard]

theorem signed_avoidance_counting_exponential_source {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (sign : Fin (d - 1) → Bool) :
    ∃ beta betaPrime : ℝ, betaPrime = Real.exp (beta - 1 / ((d : ℝ) - 1)) ∧
      0 < betaPrime ∧ ∃ r : ℕ → ℝ,
        r =o[atTop] (fun n : ℕ => (n : ℝ)) ∧
        ∀ n : ℕ, (Fintype.card (SignedAvoidancePermutation n (d - 1) sign) : ℝ) =
          (n.factorial : ℝ) ^ ((d : ℝ) - 1 - 1 / ((d : ℝ) - 1)) *
            betaPrime ^ n * Real.exp (r n) := by
  simpa only [signed_avoidance_card_eq, avoidanceClassCard] using
    avoidance_counting_exponential_source hd H

theorem antichainProbability_dimension_two (n : ℕ) :
    antichainProbability n 2 = 1 / (n.factorial : ℝ) := by
  have h := avoidanceClassCard_exact n 2 (by norm_num)
  rw [avoidanceClassCard_dimension_two] at h
  norm_num at h
  apply (eq_div_iff (by positivity : (n.factorial : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h.symm

/-- The two-dimensional constants are beta_2 = 1 and beta-prime_2 = 1;
the probability asymptotic is proved directly from exact reversal counting. -/
theorem antichain_counting_dimension_two :
    (fun n : ℕ => Real.log (antichainProbability n 2) +
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have h := log_factorial_remainder_isLittleO.const_mul_left (-1 : ℝ)
  convert h using 1
  funext n
  rw [antichainProbability_dimension_two, Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by positivity : (n.factorial : ℝ) ≠ 0), Real.log_one]
  ring

end Antichain
