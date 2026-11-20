import Antichain.Applications
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Analytic implication certificates. These prove consequences of explicitly stated
asymptotic inputs; they do not certify the paper's volume theorem or Stirling's
formula for the antichain model.
-/

open Filter Asymptotics
open scoped Topology

namespace Antichain

/-- The logarithmic form of the exact rank-count identity. -/
theorem log_rank_count_identity (d : ℝ) (a count : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hcount : ∀ n, count n = (n.factorial : ℝ) ^ (d - 1) * a n) (n : ℕ) :
    Real.log (count n) = (d - 1) * Real.log (n.factorial : ℝ) + Real.log (a n) := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [hcount n, Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hf _)) (ne_of_gt (ha n)),
    Real.log_rpow hf]

/-- Conditional enumeration certificate for Proposition 6.2: the paper's
log-probability asymptotic and a Stirling remainder imply exactly the claimed
linear coefficient after removing the factorial scale. Both analytic inputs are
visible hypotheses, rather than axioms or hidden dependencies. -/
theorem counting_conversion_of_log_asymptotics (d β : ℝ) (a count : ℕ → ℝ)
    (hlog : ∀ n, Real.log (count n) =
      (d - 1) * Real.log (n.factorial : ℝ) + Real.log (a n))
    (ha : (fun n : ℕ ↦ Real.log (a n) + (n : ℝ) / (d - 1) * Real.log (n : ℝ) -
      β * (n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)))
    (hStirling : (fun n : ℕ ↦ Real.log (n.factorial : ℝ) -
      (n : ℝ) * Real.log (n : ℝ) + (n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ))) :
    (fun n : ℕ ↦ Real.log (count n) -
      (d - 1 - 1 / (d - 1)) * Real.log (n.factorial : ℝ) -
      (n : ℝ) * (β - 1 / (d - 1))) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  have h := ha.add (hStirling.const_mul_left (1 / (d - 1)))
  convert h using 1
  ext n
  rw [hlog n]
  ring

/-- Factoring a nonnegative real power when the exponent is at least one,
including the zero-base and exponent-one endpoints. -/
theorem rpow_eq_mul_rpow_sub_one {x q : ℝ} (hx : 0 ≤ x) (hq : 1 ≤ q) :
    x ^ q = x * x ^ (q - 1) := by
  calc
    x ^ q = x ^ (1 + (q - 1)) := by congr 1; ring
    _ = x ^ (1 : ℝ) * x ^ (q - 1) := Real.rpow_add' hx (by linarith)
    _ = _ := by rw [Real.rpow_one]

/-- The finite power-sum inequality used in the one-tile series estimate. -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i ∈ s, (a i) ^ q) ≤ (∑ i ∈ s, a i) ^ q := by
  have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  calc
    (∑ i ∈ s, (a i) ^ q) ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) ^ (q - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [rpow_eq_mul_rpow_sub_one (ha i hi) hq]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (ha i hi) (Finset.single_le_sum ha hi) (by linarith)) (ha i hi)
    _ = (∑ i ∈ s, a i) * (∑ i ∈ s, a i) ^ (q - 1) := by rw [Finset.sum_mul]
    _ = _ := (rpow_eq_mul_rpow_sub_one hS hq).symm

/-- For a summable nonnegative sequence, raising every term to a power at
least one preserves summability and bounds its sum by the same power of the
original sum. This is the infinite-series step in Lemma 4.4. -/
theorem summable_rpow_and_tsum_le {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) {q : ℝ} (hq : 1 ≤ q) :
    Summable (fun i ↦ (a i) ^ q) ∧ (∑' i, (a i) ^ q) ≤ (∑' i, a i) ^ q := by
  have hS : 0 ≤ ∑' i, a i := tsum_nonneg ha
  have hcomp : ∀ i, (a i) ^ q ≤ a i * (∑' j, a j) ^ (q - 1) := by
    intro i
    rw [rpow_eq_mul_rpow_sub_one (ha i) hq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (ha i) (hs.le_tsum i (fun j _ ↦ ha j)) (by linarith)) (ha i)
  have hmajor := hs.mul_right ((∑' i, a i) ^ (q - 1))
  have hp : Summable (fun i ↦ (a i) ^ q) :=
    Summable.of_nonneg_of_le (fun i ↦ Real.rpow_nonneg (ha i) q) hcomp hmajor
  refine ⟨hp, ?_⟩
  calc
    (∑' i, (a i) ^ q) ≤ ∑' i, a i * (∑' j, a j) ^ (q - 1) :=
      hp.tsum_le_tsum hcomp hmajor
    _ = (∑' i, a i) * (∑' j, a j) ^ (q - 1) := hs.tsum_mul_right _
    _ = _ := (rpow_eq_mul_rpow_sub_one hS hq).symm

/-- The factorial-power majorant in the one-tile generating-function proof.
Convergence and the exponential bound are proved for every nonnegative `s`. -/
theorem factorial_rpow_series_bound {s q : ℝ} (hs : 0 ≤ s) (hq : 1 ≤ q) :
    Summable (fun n : ℕ ↦ (s ^ n / (n.factorial : ℝ)) ^ q) ∧
      (∑' n : ℕ, (s ^ n / (n.factorial : ℝ)) ^ q) ≤ Real.exp (q * s) := by
  have he : HasSum (fun n : ℕ ↦ s ^ n / (n.factorial : ℝ)) (Real.exp s) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ s
  have hnonneg : ∀ n : ℕ, 0 ≤ s ^ n / (n.factorial : ℝ) := by
    intro n
    exact div_nonneg (pow_nonneg hs n) (by positivity)
  obtain ⟨hp, hb⟩ := summable_rpow_and_tsum_le _ hnonneg he.summable hq
  refine ⟨hp, ?_⟩
  simpa only [he.tsum_eq, ← Real.exp_mul, mul_comm s q] using hb

/-- Any nonnegative coefficient series bounded term by term by the paper's
factorial-power majorant converges, with the stated explicit exponential bound. -/
theorem dominated_factorial_rpow_series_bound (v : ℕ → ℝ) {C s q : ℝ}
    (hv : ∀ n, 0 ≤ v n) (hC : 0 ≤ C) (hs : 0 ≤ s) (hq : 1 ≤ q)
    (hbound : ∀ n, v n ≤ C * (s ^ n / (n.factorial : ℝ)) ^ q) :
    Summable v ∧ (∑' n, v n) ≤ C * Real.exp (q * s) := by
  obtain ⟨hp, hb⟩ := factorial_rpow_series_bound hs hq
  have hm := hp.mul_left C
  have hvsum : Summable v := Summable.of_nonneg_of_le hv hbound hm
  refine ⟨hvsum, ?_⟩
  calc
    (∑' n, v n) ≤ ∑' n : ℕ, C * (s ^ n / (n.factorial : ℝ)) ^ q :=
      hvsum.tsum_le_tsum hbound hm
    _ = C * (∑' n : ℕ, (s ^ n / (n.factorial : ℝ)) ^ q) := hp.tsum_mul_left C
    _ ≤ C * Real.exp (q * s) := mul_le_mul_of_nonneg_left hb hC

/-- The analytic Chernoff step: a subexponential moment factor turns an
exponential Markov bound into a uniform exponential tail. No logarithm of the
tail probability is taken, so zero probabilities cause no exception. The moment
factor is also allowed to be zero. The probabilistic Markov inequality and the
model-specific moment asymptotic remain explicit inputs to this certificate. -/
theorem exponential_tail_of_log_moment_limit (p M : ℕ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hM : ∀ n, 0 ≤ M n)
    (hbound : ∀ n, p n ≤ Real.exp (-δ * (n : ℝ)) * M n)
    (hlimit : Tendsto (fun n : ℕ ↦ Real.log (M n) / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, p n ≤ Real.exp (-(δ / 2) * (n : ℝ)) := by
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.log (M n) / (n : ℝ) ≤ δ / 2 :=
    (hlimit.eventually_lt_const (half_pos hδ)).mono (fun _ h ↦ h.le)
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnpos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  by_cases hmpos : 0 < M n
  · have hlog : Real.log (M n) ≤ δ / 2 * (n : ℝ) := (div_le_iff₀ hnR).mp hn
    calc
      p n ≤ Real.exp (-δ * (n : ℝ)) * M n := hbound n
      _ ≤ Real.exp (-δ * (n : ℝ)) * Real.exp (δ / 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left ((Real.log_le_iff_le_exp hmpos).mp hlog)
          (Real.exp_nonneg _)
      _ = Real.exp (-(δ / 2) * (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  · have hmzero : M n = 0 := le_antisymm (le_of_not_gt hmpos) (hM n)
    have hpzero : p n ≤ 0 := by simpa only [hmzero, mul_zero] using hbound n
    exact hpzero.trans (Real.exp_nonneg _)

end Antichain
