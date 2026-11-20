import Antichain.GaussianSample
import Antichain.EmpiricalTopology
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Order.Interval.Set.Union

/-! An elementary finite-grid replacement for the cited sharp DKW bound.
Only the actual iid restricted-volume uniform law is used. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 800000

/-- Actual empirical CDF of an independent uniform real-coordinate sample. -/
def uniformEmpiricalCDF (n : ℕ) (x : Fin n → ℝ) (s : ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => x j ≤ s)).card : ℝ) / (n : ℝ)

def uniformCDFIndicator (s u : ℝ) : ℝ := (Iic s).indicator (fun _ => 1) u

theorem uniformCDFIndicator_measurable (s : ℝ) : Measurable (uniformCDFIndicator s) :=
  measurable_const.indicator measurableSet_Iic

theorem uniformCDFIndicator_mem_Icc (s u : ℝ) : uniformCDFIndicator s u ∈ Icc (0 : ℝ) 1 := by
  by_cases h : u ≤ s <;> simp [uniformCDFIndicator, h]

theorem uniformCDFIndicator_integral {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ u, uniformCDFIndicator s u ∂cubeCoordinateLaw = s := by
  change ∫ u, (Iic s).indicator (1 : ℝ → ℝ) u ∂cubeCoordinateLaw = s
  rw [integral_indicator_one measurableSet_Iic, measureReal_def,
    cubeCoordinateLaw_Iic, min_eq_left hs.2, ENNReal.toReal_ofReal hs.1]

def centeredCDFIndicator (s : ℝ) (positive : Bool) (u : ℝ) : ℝ :=
  if positive then uniformCDFIndicator s u - s else s - uniformCDFIndicator s u

theorem centeredCDFIndicator_measurable (s : ℝ) (positive : Bool) :
    Measurable (centeredCDFIndicator s positive) := by
  cases positive
  · exact measurable_const.sub (uniformCDFIndicator_measurable s)
  · exact (uniformCDFIndicator_measurable s).sub_const s

theorem centeredCDFIndicator_subgaussian {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (positive : Bool) :
    HasSubgaussianMGF (centeredCDFIndicator s positive) 1 cubeCoordinateLaw := by
  have hb : ∀ᵐ u ∂cubeCoordinateLaw, centeredCDFIndicator s positive u ∈ Icc (-1 : ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro u
    have hu := uniformCDFIndicator_mem_Icc s u
    cases positive <;> change _ ∈ Icc (-1 : ℝ) 1 <;> constructor <;> dsimp [centeredCDFIndicator] <;>
      linarith [hu.1, hu.2, hs.1, hs.2]
  have hi : Integrable (uniformCDFIndicator s) cubeCoordinateLaw :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hm : ∫ u, centeredCDFIndicator s positive u ∂cubeCoordinateLaw = 0 := by
    cases positive
    · change ∫ u, s - uniformCDFIndicator s u ∂cubeCoordinateLaw = 0
      rw [integral_sub (integrable_const s) hi, integral_const, measureReal_univ_eq_one,
        one_smul, uniformCDFIndicator_integral hs, sub_self]
    · change ∫ u, uniformCDFIndicator s u - s ∂cubeCoordinateLaw = 0
      rw [integral_sub hi (integrable_const s), integral_const, measureReal_univ_eq_one,
        one_smul, uniformCDFIndicator_integral hs, sub_self]
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (centeredCDFIndicator_measurable s positive).aemeasurable hb hm
  norm_num at h
  exact h

theorem uniformCDFIndicator_sum (n : ℕ) (x : Fin n → ℝ) (s : ℝ) :
    (∑ j, uniformCDFIndicator s (x j)) =
      ((univ.filter (fun j => x j ≤ s)).card : ℝ) := by
  classical
  simp [uniformCDFIndicator, Set.indicator_apply, Finset.sum_boole]

theorem centeredCDFIndicator_sum (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (s : ℝ) (positive : Bool) :
    (∑ j, centeredCDFIndicator s positive (x j)) =
      (n : ℝ) * (if positive then uniformEmpiricalCDF n x s - s else s - uniformEmpiricalCDF n x s) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  cases positive <;> simp only [centeredCDFIndicator, Bool.false_eq_true, ↓reduceIte,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, uniformCDFIndicator_sum, uniformEmpiricalCDF]
  all_goals field_simp

/-- A pointwise Hoeffding bound with a deliberately nonsharp constant. -/
theorem uniform_cdf_one_sided_bound (n : ℕ) (hn : 0 < n) {s delta : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hdelta : 0 < delta) (positive : Bool) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      {x | delta ≤ if positive then uniformEmpiricalCDF n x s - s else s - uniformEmpiricalCDF n x s} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * delta ^ 2 / 2)) := by
  let X : Fin n → (Fin n → ℝ) → ℝ := fun j x => centeredCDFIndicator s positive (x j)
  have hind : iIndepFun X (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) :=
    iIndepFun_pi (fun _ => (centeredCDFIndicator_measurable s positive).aemeasurable)
  have hsg (j : Fin n) : HasSubgaussianMGF (X j) 1 (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) := by
    have h := centeredCDFIndicator_subgaussian hs positive
    rw [← (measurePreserving_eval (fun _ : Fin n => cubeCoordinateLaw) j).map_eq] at h
    exact HasSubgaussianMGF.of_map (μ := Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      (X := centeredCDFIndicator s positive) (Y := fun x : Fin n → ℝ => x j)
      (measurable_pi_apply j).aemeasurable h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := univ) (c := fun _ => (1 : ℝ≥0)) (fun j _ => hsg j)
    (show 0 ≤ (n : ℝ) * delta by positivity)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {x : Fin n → ℝ | delta ≤ if positive then uniformEmpiricalCDF n x s - s
      else s - uniformEmpiricalCDF n x s} = {x | (n : ℝ) * delta ≤ ∑ j, X j x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [show (∑ j, X j x) = (n : ℝ) *
      (if positive then uniformEmpiricalCDF n x s - s else s - uniformEmpiricalCDF n x s) from
        centeredCDFIndicator_sum n hn x s positive]
    constructor <;> intro hle <;> nlinarith
  have hexp : -((n : ℝ) * delta) ^ 2 / (2 * (n : ℝ)) = -(n : ℝ) * delta ^ 2 / 2 := by
    field_simp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, NNReal.coe_natCast, hexp] at h
  rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

theorem uniformEmpiricalCDF_monotone (n : ℕ) (x : Fin n → ℝ) : Monotone (uniformEmpiricalCDF n x) := by
  classical
  intro a b hab
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast Finset.card_le_card (show univ.filter (fun j => x j ≤ a) ⊆
    univ.filter (fun j => x j ≤ b) from fun _ hj =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.trans hab⟩)

def cdfGridPoint (K : ℕ) (i : Fin (K + 1)) : ℝ := (i.val : ℝ) / K

theorem cdfGridPoint_mem_Icc (K : ℕ) (hK : 0 < K) (i : Fin (K + 1)) :
    cdfGridPoint K i ∈ Icc (0 : ℝ) 1 := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hKR.le
  · apply (div_le_one hKR).mpr
    exact_mod_cast Nat.lt_succ_iff.mp i.isLt

theorem uniformEmpiricalCDF_bound_of_grid (n K : ℕ) (hK : 0 < K) (x : Fin n → ℝ)
    {delta : ℝ} (hmesh : (1 : ℝ) / K ≤ delta / 2)
    (hgrid : ∀ i : Fin (K + 1), |uniformEmpiricalCDF n x (cdfGridPoint K i) - cdfGridPoint K i| ≤ delta / 2) :
    ∀ s ∈ Icc (0 : ℝ) 1, |uniformEmpiricalCDF n x s - s| ≤ delta := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hd : 0 ≤ delta / 2 := (div_nonneg (by norm_num) hKR.le).trans hmesh
  intro s hs
  by_cases hs1 : s = 1
  · subst s
    have hg := hgrid ⟨K, Nat.lt_succ_self K⟩
    simp only [cdfGridPoint, div_self hKR.ne'] at hg
    linarith
  · have hscell : s ∈ Ico (0 : ℝ) ((K : ℝ) / K) := by
      rw [div_self hKR.ne']
      exact ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
    have hc := Ico_subset_biUnion_Ico K (fun k : ℕ => (k : ℝ) / K)
    simp only [Nat.cast_zero, zero_div] at hc
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hc hscell)
    obtain ⟨hk, hsk⟩ := Set.mem_iUnion.mp hk
    have hkK := Finset.mem_range.mp hk
    let lo : Fin (K + 1) := ⟨k, by omega⟩
    let hi : Fin (K + 1) := ⟨k + 1, by omega⟩
    have hlow : cdfGridPoint K lo ≤ s := hsk.1
    have hhigh : s ≤ cdfGridPoint K hi := hsk.2.le
    have hgap : cdfGridPoint K hi - cdfGridPoint K lo = (1 : ℝ) / K := by
      simp only [cdfGridPoint, lo, hi, Nat.cast_add, Nat.cast_one]
      ring
    have hlo := abs_le.mp (hgrid lo)
    have hhi := abs_le.mp (hgrid hi)
    have hmonoLo := uniformEmpiricalCDF_monotone n x hlow
    have hmonoHi := uniformEmpiricalCDF_monotone n x hhigh
    apply abs_le.mpr
    constructor <;> linarith

/-- The actual uniform empirical CDF has an exponential tail at each fixed
tolerance, proved from bounded iid indicators and a finite deterministic grid.
This is sufficient for the paper; no sharp DKW constant is asserted. -/
theorem elementary_uniform_cdf_exponential_tail {delta : ℝ} (hdelta : 0 < delta) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
        {x | ∃ s ∈ Icc (0 : ℝ) 1, delta < |uniformEmpiricalCDF n x s - s|} ≤
          ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨K, hK⟩ := exists_nat_gt ((2 : ℝ) / delta)
  have hKpos : 0 < K := by exact_mod_cast (lt_trans (by positivity : (0 : ℝ) < 2 / delta) hK)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hmesh : (1 : ℝ) / K ≤ delta / 2 := by
    have hh := (div_lt_iff₀ hdelta).mp hK
    apply (div_le_iff₀ hKR).mpr
    nlinarith
  let A : (Fin (K + 1) × Bool) → ∀ n : ℕ, Set (Fin n → ℝ) := fun z n =>
    {x | delta / 2 ≤ if z.2 then uniformEmpiricalCDF n x (cdfGridPoint K z.1) - cdfGridPoint K z.1
      else cdfGridPoint K z.1 - uniformEmpiricalCDF n x (cdfGridPoint K z.1)}
  have hA (z : Fin (K + 1) × Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (A z n) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    refine ⟨(delta / 2) ^ 2 / 2, by positivity, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    convert uniform_cdf_one_sided_bound n hn (cdfGridPoint_mem_Icc K hKpos z.1)
      (show 0 < delta / 2 by positivity) z.2 using 1
    congr 2
    ring
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail
    (fun n => Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) A hA
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  apply le_trans (measure_mono ?_) hn
  intro x hbad
  by_contra hnot
  have hgrid (i : Fin (K + 1)) :
      |uniformEmpiricalCDF n x (cdfGridPoint K i) - cdfGridPoint K i| ≤ delta / 2 := by
    have hp : uniformEmpiricalCDF n x (cdfGridPoint K i) - cdfGridPoint K i < delta / 2 :=
      lt_of_not_ge (fun h => hnot (Set.mem_iUnion.mpr ⟨(i, true), h⟩))
    have hm : cdfGridPoint K i - uniformEmpiricalCDF n x (cdfGridPoint K i) < delta / 2 :=
      lt_of_not_ge (fun h => hnot (Set.mem_iUnion.mpr ⟨(i, false), h⟩))
    apply abs_le.mpr
    constructor <;> linarith
  obtain ⟨s, hs, hbad⟩ := hbad
  exact not_lt_of_ge (uniformEmpiricalCDF_bound_of_grid n K hKpos x hmesh hgrid s hs) hbad

end Antichain
