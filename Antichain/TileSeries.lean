import Antichain.CoefficientRate

/-!
The full generating-function lemma for the paper's actual one-tile coefficients.
Every geometric rate and positivity input is produced by the preceding modules.
-/

noncomputable section

namespace Antichain

open Filter
open scoped Topology

def tileGeneratingFunction (d : ℕ) (epsilon c : ℝ) (t : ℝ) : ℝ :=
  exponentialGeneratingFunction (tileCoefficient d epsilon c) t

/-- Complete Lemma 4.4: genuine convergence of the actual one-tile series,
and the precise dimension-dependent logarithmic growth bound. -/
theorem tileSeries_growth {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    (∀ t : ℝ, 0 ≤ t → Summable (fun n : ℕ =>
      tileCoefficient d epsilon c n * t ^ n / (n.factorial : ℝ))) ∧
      Filter.limsup (fun t : ℝ => t ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
        Real.log (tileGeneratingFunction d epsilon c t)) atTop ≤
          (d : ℝ) / ((d : ℝ) - 1) * Real.exp ((((d : ℝ) - 1) / (d : ℝ)) *
            tileCoefficientRate d hd epsilon - 1 / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact egf_dimension_growth_of_coefficient_limsup (tileCoefficient d epsilon c)
    hdR (tileCoefficient_pos hd hepsilon hc) (tileCoefficient_zero d epsilon c)
    (normalizedTileLog_bounded hd hepsilon hc).1.isBoundedUnder_of_range
    (tileCoefficient_log_limsup hd hepsilon hc).le

theorem tileSeries_summable {d : ℕ} (hd : 2 ≤ d) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (ht : 0 ≤ t) :
    Summable (fun n : ℕ => tileCoefficient d epsilon c n * t ^ n / (n.factorial : ℝ)) :=
  (tileSeries_growth hd hepsilon hc).1 t ht

/-- The actual generating function is at least its degree-zero term one. -/
theorem tileGeneratingFunction_one_le {d : ℕ} (hd : 2 ≤ d) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (ht : 0 ≤ t) :
    1 ≤ tileGeneratingFunction d epsilon c t :=
  one_le_egf_of_summable (tileCoefficient d epsilon c)
    (fun n => (tileCoefficient_pos hd hepsilon hc n).le)
    (tileCoefficient_zero d epsilon c) ht (tileSeries_summable hd hepsilon hc ht)

theorem tileSeries_log_limsup {d : ℕ} (hd : 2 ≤ d) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) :
    Filter.limsup (fun t : ℝ => t ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
      Real.log (tileGeneratingFunction d epsilon c t)) atTop ≤
        (d : ℝ) / ((d : ℝ) - 1) * Real.exp ((((d : ℝ) - 1) / (d : ℝ)) *
          tileCoefficientRate d hd epsilon - 1 / (d : ℝ)) :=
  (tileSeries_growth hd hepsilon hc).2

/-- An all-t bound for the actual series, used before summing logarithms over
infinitely many floor tiles. Its coefficient majorant is derived internally. -/
theorem tileSeries_uniform_bound {d : ℕ} (hd : 2 ≤ d) {epsilon c delta : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (hdelta : 0 < delta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      Summable (fun n : ℕ => tileCoefficient d epsilon c n * t ^ n / (n.factorial : ℝ)) ∧
        tileGeneratingFunction d epsilon c t ≤ C * Real.exp
          ((d : ℝ) / ((d : ℝ) - 1) *
            Real.exp ((((d : ℝ) - 1) / (d : ℝ)) *
              (tileCoefficientRate d hd epsilon + delta) - 1 / (d : ℝ)) *
            t ^ (((d : ℝ) - 1) / (d : ℝ))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hm0 : (d : ℝ) - 1 ≠ 0 := by linarith
  let q : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  have hq : 1 < q := by
    dsimp [q]
    exact (lt_div_iff₀ (by linarith)).mpr (by linarith)
  have hqrel : q - 1 = 1 / ((d : ℝ) - 1) := by
    dsimp [q]
    field_simp
    ring
  have hfun : (fun n : ℕ => Real.log (tileCoefficient d epsilon c n) / (n : ℝ) +
      (q - 1) * Real.log (n : ℝ)) = normalizedTileLog d epsilon c := by
    funext n
    rw [hqrel]
    unfold normalizedTileLog
    ring
  have hrate : ∀ eta : ℝ, 0 < eta → ∀ᶠ n : ℕ in atTop,
      Real.log (tileCoefficient d epsilon c n) / (n : ℝ) + (q - 1) * Real.log (n : ℝ) ≤
        tileCoefficientRate d hd epsilon + eta := by
    intro eta heta
    have hevent := eventually_lt_add_pos_of_limsup_le
      (normalizedTileLog_bounded hd hepsilon hc).1.isBoundedUnder_of_range
      (tileCoefficient_log_limsup hd hepsilon hc).le heta
    filter_upwards [hevent] with n hn
    rw [congrFun hfun n]
    exact hn.le
  have h := egf_uniform_bound_of_upper_rate (tileCoefficient d epsilon c)
    (tileCoefficient_pos hd hepsilon hc) hq hdelta hrate
  have hp : 1 / q = ((d : ℝ) - 1) / (d : ℝ) := by dsimp [q]; field_simp
  have hk : (tileCoefficientRate d hd epsilon - (q - 1) + delta) / q =
      (((d : ℝ) - 1) / (d : ℝ)) * (tileCoefficientRate d hd epsilon + delta) - 1 / (d : ℝ) := by
    dsimp [q]
    field_simp
    ring
  simpa only [hp, hk, q, tileGeneratingFunction] using h

end Antichain
