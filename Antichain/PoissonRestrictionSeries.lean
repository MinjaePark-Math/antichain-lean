import Antichain.PoissonConfiguration
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Finiteness

/-! Exact exponential-series factorization for actual Poisson restrictions.
The scalar identity is unconditional for nonnegative extended-real sequences;
it uses the proved factorial/binomial identity and nonnegative Cauchy product. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

theorem poisson_ennreal_tsum_cauchy (f g : ℕ → ℝ≥0∞) :
    (∑' n, f n) * (∑' n, g n) =
      ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
  classical
  calc
    _ = ∑' p : ℕ × ℕ, f p.1 * g p.2 := by
      rw [ENNReal.tsum_prod (f := fun n m => f n * g m)]
      simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ = ∑' n : ℕ, ∑' p : Finset.antidiagonal n, f p.val.1 * g p.val.2 := by
      rw [← (Finset.sigmaAntidiagonalEquivProd :
        (Σ n : ℕ, Finset.antidiagonal n) ≃ ℕ × ℕ).tsum_eq]
      change (∑' p : (Σ n : ℕ, Finset.antidiagonal n), f p.2.val.1 * g p.2.val.2) = _
      exact ENNReal.tsum_sigma (fun (n : ℕ) (p : Finset.antidiagonal n) => f p.val.1 * g p.val.2)
    _ = _ := by
      apply tsum_congr
      intro n
      letI : Fintype (Finset.antidiagonal n) := Finset.fintypeCoeSort _
      rw [tsum_fintype]
      change (∑ p : Finset.antidiagonal n, (fun p : ℕ × ℕ => f p.1 * g p.2) p.val) = _
      rw [Finset.sum_coe_sort (Finset.antidiagonal n) (fun p : ℕ × ℕ => f p.1 * g p.2)]
      exact Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => f k * g l) n

theorem poisson_ennreal_binomial_egf_term (n k : ℕ) (hkn : k ≤ n) (t A B : ℝ≥0∞) :
    t ^ n / (n.factorial : ℝ≥0∞) * ((n.choose k : ℝ≥0∞) * (A * B)) =
      (t ^ k / (k.factorial : ℝ≥0∞) * A) *
        (t ^ (n - k) / ((n - k).factorial : ℝ≥0∞) * B) := by
  have hreal : (n.choose k : ℝ) / (n.factorial : ℝ) =
      1 / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    simpa only [one_mul, mul_assoc, ← Nat.cast_mul] using
      congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_mul_factorial_mul_factorial hkn)
  have hconst : (n.choose k : ℝ≥0∞) / (n.factorial : ℝ≥0∞) =
      1 / ((k.factorial : ℝ≥0∞) * ((n - k).factorial : ℝ≥0∞)) := by
    have hh := congrArg ENNReal.ofReal hreal
    simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < n.factorial),
      ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) <
        (k.factorial : ℝ) * ((n - k).factorial : ℝ)), ENNReal.ofReal_natCast,
      ENNReal.ofReal_one, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ k.factorial)] using hh
  calc
    _ = t ^ n * ((n.choose k : ℝ≥0∞) / (n.factorial : ℝ≥0∞)) * (A * B) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = _ := by
      rw [hconst, ← Nat.add_sub_of_le hkn, pow_add]
      simp only [Nat.add_sub_cancel_left]
      simp only [div_eq_mul_inv, one_mul]
      rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
      ac_rfl

theorem poisson_restriction_series_factorization (t : ℝ≥0∞) (A B : ℕ → ℝ≥0∞) :
    (∑' n : ℕ, t ^ n / (n.factorial : ℝ≥0∞) *
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * (A k * B (n - k))) =
      (∑' k : ℕ, t ^ k / (k.factorial : ℝ≥0∞) * A k) *
        (∑' l : ℕ, t ^ l / (l.factorial : ℝ≥0∞) * B l) := by
  rw [poisson_ennreal_tsum_cauchy]
  apply tsum_congr
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact poisson_ennreal_binomial_egf_term n k
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) t (A k) (B (n - k))

variable {X : Type*} [MeasurableSpace X]

theorem configurationSeriesMeasure_univ_exp (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] :
    configurationSeriesMeasure (t : ℝ≥0∞) mu Set.univ =
      ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) := by
  let r : ℝ := (t : ℝ) * (mu Set.univ).toReal
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : HasSum (fun n : ℕ => r ^ n / (n.factorial : ℝ)) (Real.exp r) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ r
  rw [configurationSeriesMeasure, Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_configurationMk _) MeasurableSet.univ,
    Set.preimage_univ, Measure.pi_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum.summable]
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < n.factorial),
    ENNReal.ofReal_pow hr, ENNReal.ofReal_natCast]
  have heq : ENNReal.ofReal r = (t : ℝ≥0∞) * mu Set.univ := by
    dsimp [r]
    rw [ENNReal.ofReal_mul t.coe_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp
  rw [heq, mul_pow]
  simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem configurationSeriesMeasure_isFinite (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] : IsFiniteMeasure (configurationSeriesMeasure (t : ℝ≥0∞) mu) := by
  constructor
  rw [configurationSeriesMeasure_univ_exp]
  exact ENNReal.ofReal_lt_top

theorem intensity_eq_mass_smul_normalized_all (mu : Measure X) [IsFiniteMeasure mu] :
    mu = (mu Set.univ).toNNReal • normalizedMarkLaw mu := by
  by_cases hz : mu = 0
  · simp [hz, normalizedMarkLaw]
  · letI : NeZero mu := ⟨hz⟩
    exact intensity_eq_mass_smul_normalized mu

/-- The existing actual Poisson/iid normalization formula remains valid for
zero cell intensity as well; no nonzero restriction law is assumed. -/
theorem finiteIntensityPoissonLaw_event_expansion_all (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu]
    (A : ∀ n : ℕ, Set (Fin n → X)) (hA : ∀ n, MeasurableSet (A n)) :
    ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) *
        finiteIntensityPoissonLaw t mu (configurationEvent A) =
      ∑' n : ℕ, (t : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) *
        Measure.pi (fun _ : Fin n => mu) (A n) := by
  letI : IsFiniteMeasure (normalizedMarkLaw mu) := by
    unfold normalizedMarkLaw
    infer_instance
  have h := poissonConfigurationLaw_event_expansion (t * (mu Set.univ).toNNReal)
    (normalizedMarkLaw mu) (configurationEvent A) (configurationEvent_measurable A hA)
  change _ = _ at h
  rw [show ((t * (mu Set.univ).toNNReal : ℝ≥0) : ℝ) =
      (t : ℝ) * (mu Set.univ).toReal by simp [ENNReal.toReal]] at h
  unfold finiteIntensityPoissonLaw
  rw [h]
  apply tsum_congr
  intro n
  have hpi : Measure.pi (fun _ : Fin n => mu) =
      ((mu Set.univ).toNNReal : ℝ≥0∞) ^ n •
        Measure.pi (fun _ : Fin n => normalizedMarkLaw mu) := by
    conv_lhs => rw [intensity_eq_mass_smul_normalized_all mu]
    exact pi_nnreal_smul _ _ _
  rw [hpi, Measure.smul_apply, smul_eq_mul]
  simp only [ENNReal.coe_mul, mul_pow, configurationMk_preimage_event]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem configurationSeriesMeasure_eq_exp_smul_poisson_all (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] :
    configurationSeriesMeasure (t : ℝ≥0∞) mu =
      ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) •
        finiteIntensityPoissonLaw t mu := by
  apply Measure.ext
  intro S hS
  let A : ∀ n : ℕ, Set (Fin n → X) := fun n => configurationMk n ⁻¹' S
  have hA (n : ℕ) : MeasurableSet (A n) := (measurable_configurationMk n) hS
  have heq : configurationEvent A = S := by
    ext z
    cases z
    rfl
  rw [Measure.smul_apply, smul_eq_mul]
  rw [← heq, configurationSeriesMeasure_event _ _ A hA]
  exact (finiteIntensityPoissonLaw_event_expansion_all t mu A hA).symm

theorem finiteIntensityPoissonLaw_probability_all (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] : IsProbabilityMeasure (finiteIntensityPoissonLaw t mu) := by
  constructor
  have h := congrArg (fun nu : Measure (FiniteConfiguration X) => nu Set.univ)
    (configurationSeriesMeasure_eq_exp_smul_poisson_all t mu)
  dsimp only at h
  rw [configurationSeriesMeasure_univ_exp, Measure.smul_apply, smul_eq_mul] at h
  have hc0 : ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) ≠ 0 := by positivity
  have hct : ENNReal.ofReal (Real.exp ((t : ℝ) * (mu Set.univ).toReal)) ≠ ∞ := by simp
  apply (ENNReal.mul_right_inj hc0 hct).mp
  simpa only [mul_one] using h.symm

end Antichain
