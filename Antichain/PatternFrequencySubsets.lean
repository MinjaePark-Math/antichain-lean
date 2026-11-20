import Antichain.PatternFrequency
import Antichain.PatternSubsets

/-! The usual unordered-subset spelling of the literal pattern-frequency remark. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

def permutationSubsetPatternFrequency (n m q : ℕ) (tau : Fin m → Equiv.Perm (Fin q))
    (pi : Fin m → Equiv.Perm (Fin n)) : ℝ :=
  patternSubsetFrequency n q {f | (fun j => permutationRankCloud n m pi (f j)) ∈ patternEvent q m tau}

theorem permutationSubsetPatternFrequency_eq (n m q : ℕ)
    (tau : Fin m → Equiv.Perm (Fin q)) (pi : Fin m → Equiv.Perm (Fin n)) :
    permutationSubsetPatternFrequency n m q tau pi = permutationPatternFrequency n m q tau pi := by
  symm
  apply injectionPatternLabelLaw_eq_subset_frequency
  intro f p
  exact patternEvent_relabel_iff q m tau (fun j => permutationRankCloud n m pi (f j)) p

theorem permutationSubsetPatternFrequency_box_error (n m q : ℕ) [NeZero n]
    (tau : Fin m → Equiv.Perm (Fin q)) (pi : Fin m → Equiv.Perm (Fin n)) :
    |permutationSubsetPatternFrequency n m q tau pi -
      patternProbability q m tau (permutationRankBoxProbability n m pi)| ≤ (q.choose 2 : ℝ) / n := by
  rw [permutationSubsetPatternFrequency_eq]
  exact permutationPatternFrequency_box_error n m q tau pi

/-- Remark 6.2 for the ordinary number of q-element subsets inducing the
fixed multidimensional pattern, divided by choose(n,q). -/
theorem fixed_pattern_frequency_source {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationSubsetPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  simp_rw [permutationSubsetPatternFrequency_eq]
  exact permutation_pattern_frequency_exponential_concentration hm H DKW q tau hepsilon

end Antichain
