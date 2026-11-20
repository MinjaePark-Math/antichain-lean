import Antichain.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LiminfLimsup

/-!
The analytic generating-function argument from the paper, isolated from its
geometric coefficient theorem. Hypotheses on coefficient rates are explicit.
-/

open Filter Asymptotics
open scoped Topology

namespace Antichain

/-- The normalized logarithmic Stirling remainder, proved from Mathlib's actual
factorial theorem rather than supplied as an asymptotic hypothesis. -/
theorem tendsto_log_factorial_remainder :
    Tendsto (fun n : ℕ ↦ Real.log (n.factorial : ℝ) / (n : ℝ) -
      Real.log (n : ℝ) + 1) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hsd := hs.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ ↦ Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := hsd.add ((hc.add hlog).const_mul (1 / 2 : ℝ))
  simp only [zero_add, mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne',
    Real.log_div hnR.ne' (Real.exp_ne_zero 1), Real.log_exp]
  field_simp
  ring

/-- The actual factorial Stirling remainder in the little-o form used by the
enumeration application. -/
theorem log_factorial_remainder_isLittleO :
    (fun n : ℕ ↦ Real.log (n.factorial : ℝ) -
      (n : ℝ) * Real.log (n : ℝ) + (n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop 0] with n hn hz
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact False.elim (hnR.ne' hz)
  · apply tendsto_log_factorial_remainder.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp

/-- The counting conversion now needs only the actual rank-count identity and
the model's log-probability asymptotic; Stirling is proved inside the dependency
chain. This does not establish those two model-specific hypotheses. -/
theorem counting_conversion_from_log_probability (d β : ℝ) (a count : ℕ → ℝ)
    (hapos : ∀ n, 0 < a n)
    (hcount : ∀ n, count n = (n.factorial : ℝ) ^ (d - 1) * a n)
    (ha : (fun n : ℕ ↦ Real.log (a n) + (n : ℝ) / (d - 1) * Real.log (n : ℝ) -
      β * (n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ))) :
    (fun n : ℕ ↦ Real.log (count n) -
      (d - 1 - 1 / (d - 1)) * Real.log (n.factorial : ℝ) -
      (n : ℝ) * (β - 1 / (d - 1))) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
  counting_conversion_of_log_asymptotics d β a count
    (log_rank_count_identity d a count hapos hcount) ha log_factorial_remainder_isLittleO

/-- An upper logarithmic coefficient rate and the actual factorial asymptotic
give the exponentially bounded factorial-reweighted coefficients used in the
generating-function proof. Finitely many exceptional terms are absorbed in a
single positive constant. -/
theorem coefficient_factorial_majorant_of_upper_rate (v : ℕ → ℝ) {q b δ : ℝ}
    (hv : ∀ n, 0 < v n) (hδ : 0 < δ)
    (hrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (v n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ) ≤ b + ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ,
      v n * (n.factorial : ℝ) ^ (q - 1) ≤
        C * Real.exp ((b - (q - 1) + δ) * (n : ℝ)) := by
  have hg : ∀ᶠ n : ℕ in atTop,
      (q - 1) * (Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ) + 1) ≤ δ / 2 := by
    have hlim := tendsto_log_factorial_remainder.const_mul (q - 1)
    simp only [mul_zero] at hlim
    exact (hlim.eventually_lt_const (half_pos hδ)).mono fun _ h ↦ h.le
  have hevent : ∀ᶠ n : ℕ in atTop,
      v n * (n.factorial : ℝ) ^ (q - 1) ≤
        Real.exp ((b - (q - 1) + δ) * (n : ℝ)) := by
    filter_upwards [hrate (δ / 2) (half_pos hδ), hg, eventually_gt_atTop 0] with n hf hg hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hnorm : (Real.log (v n) + (q - 1) * Real.log (n.factorial : ℝ)) / (n : ℝ) ≤
        b - (q - 1) + δ := by
      calc
        _ = Real.log (v n) / (n : ℝ) +
            (q - 1) * (Real.log (n.factorial : ℝ) / (n : ℝ)) := by ring
        _ ≤ _ := by linarith
    have hlog := (div_le_iff₀ hnR).mp hnorm
    have hp : 0 < v n * (n.factorial : ℝ) ^ (q - 1) :=
      mul_pos (hv n) (Real.rpow_pos_of_pos hfac _)
    apply (Real.log_le_iff_le_exp hp).mp
    simpa only [Real.log_mul (hv n).ne' (Real.rpow_pos_of_pos hfac _).ne',
      Real.log_rpow hfac] using hlog
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let a : ℕ → ℝ := fun n ↦ v n * (n.factorial : ℝ) ^ (q - 1) /
    Real.exp ((b - (q - 1) + δ) * (n : ℝ))
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    exact div_nonneg (mul_nonneg (hv n).le (Real.rpow_nonneg (by positivity) _))
      (Real.exp_nonneg _)
  let C : ℝ := 1 + ∑ n ∈ Finset.range N, a n
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, a n := Finset.sum_nonneg (fun n _ ↦ ha n)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun n ↦ ?_⟩
  by_cases hn : n < N
  · have hratio : a n ≤ C := by
      have hsum := Finset.single_le_sum (fun i _ ↦ ha i) (Finset.mem_range.mpr hn)
      dsimp [C]
      linarith
    exact (div_le_iff₀ (Real.exp_pos _)).mp hratio
  · exact (hN n (le_of_not_gt hn)).trans
      (le_mul_of_one_le_left (Real.exp_nonneg _) hC)

/-- The exponential generating function of the nonnegative coefficients. -/
noncomputable def exponentialGeneratingFunction (v : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, v n * t ^ n / (n.factorial : ℝ)

/-- Algebraic passage from factorial-reweighted coefficients to the precise
factorial-power majorant, including `t = 0`. -/
theorem egf_term_le_factorial_power (v : ℕ → ℝ) {q C K t : ℝ}
    (hq : 1 < q) (ht : 0 ≤ t)
    (hcoeff : ∀ n : ℕ, v n * (n.factorial : ℝ) ^ (q - 1) ≤
      C * Real.exp (K * (n : ℝ))) (n : ℕ) :
    v n * t ^ n / (n.factorial : ℝ) ≤
      C * ((Real.exp (K / q) * t ^ (1 / q)) ^ n / (n.factorial : ℝ)) ^ q := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  let x : ℝ := Real.exp (K / q) * t ^ (1 / q)
  have hx : 0 ≤ x := mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht _)
  have hxq : x ^ q = Real.exp K * t := by
    dsimp [x]
    rw [Real.mul_rpow (Real.exp_nonneg _) (Real.rpow_nonneg ht _),
      ← Real.exp_mul, one_div, Real.rpow_inv_rpow ht hq0, div_mul_cancel₀ _ hq0]
  have hpower : (x ^ n / (n.factorial : ℝ)) ^ q =
      Real.exp (K * (n : ℝ)) * t ^ n / (n.factorial : ℝ) ^ q := by
    rw [Real.div_rpow (pow_nonneg hx n) hfac.le,
      ← Real.rpow_pow_comm hx, hxq, mul_pow, ← Real.exp_nat_mul, mul_comm (n : ℝ) K]
  change _ ≤ C * (x ^ n / (n.factorial : ℝ)) ^ q
  rw [hpower, ← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hfac q)).mpr
  have hfq : (n.factorial : ℝ) ^ q = (n.factorial : ℝ) ^ (q - 1) * (n.factorial : ℝ) := by
    rw [rpow_eq_mul_rpow_sub_one hfac.le hq.le]
    ring
  calc
    v n * t ^ n / (n.factorial : ℝ) * (n.factorial : ℝ) ^ q =
        (v n * (n.factorial : ℝ) ^ (q - 1)) * t ^ n := by
      rw [hfq]
      field_simp
    _ ≤ C * (Real.exp (K * (n : ℝ)) * t ^ n) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg ht n)

/-- A uniform factorial majorant implies convergence and the explicit entire
generating-function bound, with the exact real-power rescaling. -/
theorem egf_bound_of_factorial_majorant (v : ℕ → ℝ) {q C K : ℝ}
    (hv : ∀ n, 0 ≤ v n) (hq : 1 < q) (hC : 0 ≤ C)
    (hcoeff : ∀ n : ℕ, v n * (n.factorial : ℝ) ^ (q - 1) ≤
      C * Real.exp (K * (n : ℝ))) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n : ℕ ↦ v n * t ^ n / (n.factorial : ℝ)) ∧
      exponentialGeneratingFunction v t ≤
        C * Real.exp (q * Real.exp (K / q) * t ^ (1 / q)) := by
  have hterm : ∀ n : ℕ, 0 ≤ v n * t ^ n / (n.factorial : ℝ) := by
    intro n
    exact div_nonneg (mul_nonneg (hv n) (pow_nonneg ht n)) (by positivity)
  have hx : 0 ≤ Real.exp (K / q) * t ^ (1 / q) :=
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht _)
  have h := dominated_factorial_rpow_series_bound _ hterm hC hx hq.le
    (egf_term_le_factorial_power v hq ht hcoeff)
  simpa only [exponentialGeneratingFunction, mul_assoc] using h

/-- End-to-end entire-series bound from the coefficient upper rate. The
Stirling input and the global majorant are derived inside this proof. -/
theorem egf_uniform_bound_of_upper_rate (v : ℕ → ℝ) {q b δ : ℝ}
    (hv : ∀ n, 0 < v n) (hq : 1 < q) (hδ : 0 < δ)
    (hrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (v n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ) ≤ b + ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      Summable (fun n : ℕ ↦ v n * t ^ n / (n.factorial : ℝ)) ∧
        exponentialGeneratingFunction v t ≤
          C * Real.exp (q * Real.exp ((b - (q - 1) + δ) / q) * t ^ (1 / q)) := by
  obtain ⟨C, hC, hc⟩ := coefficient_factorial_majorant_of_upper_rate v hv hδ hrate
  exact ⟨C, hC, fun t ht ↦ egf_bound_of_factorial_majorant v (fun n ↦ (hv n).le) hq
    (le_trans zero_le_one hC) hc ht⟩

/-- Positivity needed for logarithms follows from the constant term `v₀ = 1`.
No positivity of a formal infinite sum is presumed. -/
theorem one_le_egf_of_summable (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n) (hv0 : v 0 = 1)
    {t : ℝ} (ht : 0 ≤ t)
    (hs : Summable (fun n : ℕ ↦ v n * t ^ n / (n.factorial : ℝ))) :
    1 ≤ exponentialGeneratingFunction v t := by
  have hterm : ∀ n : ℕ, 0 ≤ v n * t ^ n / (n.factorial : ℝ) := by
    intro n
    exact div_nonneg (mul_nonneg (hv n) (pow_nonneg ht n)) (by positivity)
  have h := hs.le_tsum 0 (fun n _ ↦ hterm n)
  simpa only [exponentialGeneratingFunction, hv0, pow_zero, mul_one,
    Nat.factorial_zero, Nat.cast_one, div_one] using h

/-- The complete analytic logarithmic generating-function upper rate. Its
coefficient-rate hypothesis is the paper's preceding one-tile input, not a
hypothesis about the series conclusion. -/
theorem egf_log_limsup_of_upper_rate (v : ℕ → ℝ) {q b : ℝ}
    (hv : ∀ n, 0 < v n) (hv0 : v 0 = 1) (hq : 1 < q)
    (hrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (v n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ) ≤ b + ε) :
    Filter.limsup (fun t : ℝ ↦ Real.log (exponentialGeneratingFunction v t) /
      t ^ (1 / q)) atTop ≤ q * Real.exp ((b - (q - 1)) / q) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hppos : 0 < 1 / q := one_div_pos.mpr hqpos
  obtain ⟨C₀, hC₀, hbound₀⟩ := egf_uniform_bound_of_upper_rate v hv hq zero_lt_one hrate
  have hlower : ∀ᶠ t : ℝ in atTop,
      0 ≤ Real.log (exponentialGeneratingFunction v t) / t ^ (1 / q) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hs := (hbound₀ t ht.le).1
    exact div_nonneg (Real.log_nonneg (one_le_egf_of_summable v (fun n ↦ (hv n).le)
      hv0 ht.le hs)) (Real.rpow_nonneg ht.le _)
  have hcobdd := isCoboundedUnder_le_of_eventually_le atTop hlower
  have hδ : ∀ δ : ℝ, 0 < δ →
      Filter.limsup (fun t : ℝ ↦ Real.log (exponentialGeneratingFunction v t) /
        t ^ (1 / q)) atTop ≤ q * Real.exp ((b - (q - 1) + δ) / q) := by
    intro δ hδ
    obtain ⟨C, hC, hbound⟩ := egf_uniform_bound_of_upper_rate v hv hq hδ hrate
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hlim : Tendsto (fun t : ℝ ↦ Real.log C / t ^ (1 / q) +
        q * Real.exp ((b - (q - 1) + δ) / q)) atTop
        (𝓝 (q * Real.exp ((b - (q - 1) + δ) / q))) := by
      have hc : Tendsto (fun t : ℝ ↦ Real.log C / t ^ (1 / q)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hppos)
      have h := hc.add_const
        (q * Real.exp ((b - (q - 1) + δ) / q))
      simpa only [zero_add] using h
    have hupper : ∀ᶠ t : ℝ in atTop,
        Real.log (exponentialGeneratingFunction v t) / t ^ (1 / q) ≤
          Real.log C / t ^ (1 / q) + q * Real.exp ((b - (q - 1) + δ) / q) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      obtain ⟨hs, hb⟩ := hbound t ht.le
      have hpos : 0 < exponentialGeneratingFunction v t :=
        lt_of_lt_of_le zero_lt_one (one_le_egf_of_summable v (fun n ↦ (hv n).le) hv0 ht.le hs)
      have hlog := Real.log_le_log hpos hb
      rw [Real.log_mul hCpos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
      have htpos : 0 < t ^ (1 / q) := Real.rpow_pos_of_pos ht _
      apply (div_le_iff₀ htpos).mpr
      have heq : (Real.log C / t ^ (1 / q) +
          q * Real.exp ((b - (q - 1) + δ) / q)) * t ^ (1 / q) =
            Real.log C + q * Real.exp ((b - (q - 1) + δ) / q) * t ^ (1 / q) := by
        field_simp
      rw [heq]
      exact hlog
    exact (Filter.limsup_le_limsup hupper hcobdd hlim.isBoundedUnder_le).trans_eq hlim.limsup_eq
  have hlimδ : Tendsto (fun n : ℕ ↦
      q * Real.exp ((b - (q - 1) + 1 / ((n : ℝ) + 1)) / q)) atTop
      (𝓝 (q * Real.exp ((b - (q - 1)) / q))) := by
    have hbase : Tendsto (fun n : ℕ ↦ (b - (q - 1) + 1 / ((n : ℝ) + 1)) / q)
        atTop (𝓝 ((b - (q - 1) + 0) / q)) :=
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).div_const q
    have h := (Real.continuous_exp.tendsto _ |>.comp hbase).const_mul q
    simpa only [add_zero] using h
  exact ge_of_tendsto hlimδ (Eventually.of_forall (fun n ↦ hδ _ (by positivity)))

/-- A limsup formulation of the complete generic series theorem. The boundedness
hypothesis excludes the undefined/junk real limsup of an unbounded sequence. -/
theorem egf_growth_of_coefficient_limsup (v : ℕ → ℝ) {q b : ℝ}
    (hv : ∀ n, 0 < v n) (hv0 : v 0 = 1) (hq : 1 < q)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ ↦
      Real.log (v n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ)))
    (hlim : Filter.limsup (fun n : ℕ ↦ Real.log (v n) / (n : ℝ) +
      (q - 1) * Real.log (n : ℝ)) atTop ≤ b) :
    (∀ t : ℝ, 0 ≤ t → Summable (fun n : ℕ ↦ v n * t ^ n / (n.factorial : ℝ))) ∧
      Filter.limsup (fun t : ℝ ↦ t ^ (-(1 / q)) *
        Real.log (exponentialGeneratingFunction v t)) atTop ≤
          q * Real.exp ((b - (q - 1)) / q) := by
  have hrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (v n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ) ≤ b + ε := by
    intro ε hε
    exact (eventually_lt_add_pos_of_limsup_le hbdd hlim hε).mono (fun _ h ↦ h.le)
  obtain ⟨C, hC, hb⟩ := egf_uniform_bound_of_upper_rate v hv hq zero_lt_one hrate
  refine ⟨fun t ht ↦ (hb t ht).1, ?_⟩
  calc
    Filter.limsup (fun t : ℝ ↦ t ^ (-(1 / q)) *
        Real.log (exponentialGeneratingFunction v t)) atTop =
      Filter.limsup (fun t : ℝ ↦ Real.log (exponentialGeneratingFunction v t) /
        t ^ (1 / q)) atTop := by
      apply Filter.limsup_congr
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [Real.rpow_neg ht.le, div_eq_mul_inv]
      ring
    _ ≤ _ := egf_log_limsup_of_upper_rate v hv hv0 hq hrate

/-- The exact dimension-dependent constant and power from Lemma 4.4, deduced
from a positive coefficient sequence with the preceding coefficient upper rate.
This remains a generic analytic theorem until instantiated with the paper's
geometric coefficients. -/
theorem egf_dimension_growth_of_coefficient_limsup (v : ℕ → ℝ) {d b : ℝ}
    (hd : 2 ≤ d) (hv : ∀ n, 0 < v n) (hv0 : v 0 = 1)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ ↦
      Real.log (v n) / (n : ℝ) + Real.log (n : ℝ) / (d - 1)))
    (hlim : Filter.limsup (fun n : ℕ ↦ Real.log (v n) / (n : ℝ) +
      Real.log (n : ℝ) / (d - 1)) atTop ≤ b) :
    (∀ t : ℝ, 0 ≤ t → Summable (fun n : ℕ ↦ v n * t ^ n / (n.factorial : ℝ))) ∧
      Filter.limsup (fun t : ℝ ↦ t ^ (-((d - 1) / d)) *
        Real.log (exponentialGeneratingFunction v t)) atTop ≤
          d / (d - 1) * Real.exp ((d - 1) / d * b - 1 / d) := by
  have hd0 : d ≠ 0 := by linarith
  have hd1 : d - 1 ≠ 0 := by linarith
  let q : ℝ := d / (d - 1)
  have hq : 1 < q := by
    dsimp [q]
    exact (lt_div_iff₀ (by linarith)).mpr (by linarith)
  have hqrel : q - 1 = 1 / (d - 1) := by dsimp [q]; field_simp; ring
  have hfun : (fun n : ℕ ↦ Real.log (v n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ)) =
      (fun n : ℕ ↦ Real.log (v n) / (n : ℝ) + Real.log (n : ℝ) / (d - 1)) := by
    funext n
    rw [hqrel]
    ring
  have hbddq : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ ↦
      Real.log (v n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ)) := by rw [hfun]; exact hbdd
  have hlimq : Filter.limsup (fun n : ℕ ↦ Real.log (v n) / (n : ℝ) +
      (q - 1) * Real.log (n : ℝ)) atTop ≤ b := by rw [hfun]; exact hlim
  obtain ⟨hs, hg⟩ := egf_growth_of_coefficient_limsup v hv hv0 hq hbddq hlimq
  refine ⟨hs, ?_⟩
  have hp : 1 / q = (d - 1) / d := by dsimp [q]; field_simp
  have hk : (b - (q - 1)) / q = (d - 1) / d * b - 1 / d := by
    dsimp [q]
    field_simp
    ring
  simpa only [hp, hk, q] using hg

end Antichain
