import Antichain.RankCDF
import Antichain.ShapeGeometry
import Mathlib.Order.Interval.Set.Union

/-! Literal uniform rank boxes, their probability laws and uniform marginals. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

def scalarRankBoxMap (n : ℕ) (r : Fin n) (u : ℝ) : ℝ := ((r.val : ℝ) + u) / (n : ℝ)

theorem scalarRankBoxMap_continuous (n : ℕ) (r : Fin n) : Continuous (scalarRankBoxMap n r) := by
  unfold scalarRankBoxMap
  fun_prop

def scalarRankBoxLaw (n : ℕ) (r : Fin n) : Measure ℝ :=
  cubeCoordinateLaw.map (scalarRankBoxMap n r)

instance scalarRankBoxLaw_isProbabilityMeasure (n : ℕ) (r : Fin n) :
    IsProbabilityMeasure (scalarRankBoxLaw n r) :=
  Measure.isProbabilityMeasure_map (scalarRankBoxMap_continuous n r).measurable.aemeasurable

theorem scalarRankBoxMap_volume (n : ℕ) (hn : 0 < n) (r : Fin n) :
    (volume : Measure ℝ).map (scalarRankBoxMap n r) = (n : ℝ≥0∞) • volume := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : scalarRankBoxMap n r =
      (fun u : ℝ => u * (n : ℝ)⁻¹) ∘ (fun u : ℝ => (r.val : ℝ) + u) := by
    funext u
    simp [scalarRankBoxMap, div_eq_mul_inv]
  rw [heq, ← Measure.map_map (measurable_mul_const _) (measurable_const_add _),
    (measurePreserving_add_left (volume : Measure ℝ) (r.val : ℝ)).map_eq,
    Real.map_volume_mul_right (inv_ne_zero hnR.ne'), inv_inv, abs_of_pos hnR,
    ENNReal.ofReal_natCast]

theorem scalarRankBoxLaw_eq_uniform_interval (n : ℕ) (hn : 0 < n) (r : Fin n) :
    scalarRankBoxLaw n r = (n : ℝ≥0∞) • (volume : Measure ℝ).restrict
      (Icc ((r.val : ℝ) / n) (((r.val : ℝ) + 1) / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpre : scalarRankBoxMap n r ⁻¹'
      Icc ((r.val : ℝ) / n) (((r.val : ℝ) + 1) / n) = Icc (0 : ℝ) 1 := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Icc, scalarRankBoxMap,
      div_le_div_iff_of_pos_right hnR]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [scalarRankBoxLaw, cubeCoordinateLaw, ← hpre, ← Measure.restrict_map
    (scalarRankBoxMap_continuous n r).measurable measurableSet_Icc,
    scalarRankBoxMap_volume n hn r, Measure.restrict_smul]

theorem scalar_rank_intervals_sum (n : ℕ) (hn : 0 < n) :
    (∑ r : Fin n, (volume : Measure ℝ).restrict
      (Ico ((r.val : ℝ) / n) (((r.val : ℝ) + 1) / n))) = cubeCoordinateLaw := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let I : Fin n → Set ℝ := fun r => Ico ((r.val : ℝ) / n) (((r.val : ℝ) + 1) / n)
  have hdisj : Pairwise (fun r s : Fin n => Disjoint (I r) (I s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro u hu hv
    rcases lt_or_gt_of_ne hrs with hlt | hgt
    · have hgap : (r.val : ℝ) + 1 ≤ s.val := by exact_mod_cast hlt
      have hh := div_le_div_of_nonneg_right hgap hnR.le
      exact (not_lt_of_ge (hh.trans hv.1)) hu.2
    · have hgap : (s.val : ℝ) + 1 ≤ r.val := by exact_mod_cast hgt
      have hh := div_le_div_of_nonneg_right hgap hnR.le
      exact (not_lt_of_ge (hh.trans hu.1)) hv.2
  have hcover : (⋃ r : Fin n, I r) = Ico (0 : ℝ) 1 := by
    apply Set.Subset.antisymm
    · intro u hu
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hu
      have hr0 : (0 : ℝ) ≤ (r.val : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hnR.le
      have hr1 : ((r.val : ℝ) + 1) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast r.isLt)
      exact ⟨hr0.trans hr.1, hr.2.trans_le hr1⟩
    · intro u hu
      have hh := Ico_subset_biUnion_Ico n (fun k : ℕ => (k : ℝ) / n)
      simp only [Nat.cast_zero, zero_div, div_self hnR.ne'] at hh
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hh hu)
      obtain ⟨hk, hu⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨⟨k, Finset.mem_range.mp hk⟩, by simpa [I] using hu⟩
  rw [← Measure.sum_fintype]
  change Measure.sum (fun r : Fin n => (volume : Measure ℝ).restrict (I r)) = _
  rw [← Measure.restrict_iUnion hdisj (fun _ => measurableSet_Ico), hcover,
    restrict_Ico_eq_restrict_Icc]
  rfl

theorem scalarRankBoxLaw_mixture (n : ℕ) (hn : 0 < n) :
    (n : ℝ≥0∞)⁻¹ • (∑ r : Fin n, scalarRankBoxLaw n r) = cubeCoordinateLaw := by
  simp_rw [scalarRankBoxLaw_eq_uniform_interval n hn,
    ← restrict_Ico_eq_restrict_Icc]
  rw [← Finset.smul_sum, smul_smul,
    ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by finiteness), one_smul]
  exact scalar_rank_intervals_sum n hn

def rankBoxPoint (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n)
    (u : CubePoint d) : CubePoint d := fun i => scalarRankBoxMap n (r i j) (u i)

theorem rankBoxPoint_continuous (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n) :
    Continuous (rankBoxPoint n d r j) :=
  continuous_pi (fun i => (scalarRankBoxMap_continuous n (r i j)).comp (continuous_apply i))

def rankBoxLaw (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n) : Measure (CubePoint d) :=
  (cubePointLaw d).map (rankBoxPoint n d r j)

instance rankBoxLaw_isProbabilityMeasure (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n) :
    IsProbabilityMeasure (rankBoxLaw n d r j) :=
  Measure.isProbabilityMeasure_map (rankBoxPoint_continuous n d r j).measurable.aemeasurable

/-- Each box is the genuine product of the uniform laws on its coordinate
intervals, so this is literal uniform spreading over the rank box. -/
theorem rankBoxLaw_eq_product (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n) :
    rankBoxLaw n d r j = Measure.pi (fun i : Fin d => scalarRankBoxLaw n (r i j)) := by
  exact Measure.pi_map_pi (fun i => (scalarRankBoxMap_continuous n (r i j)).measurable.aemeasurable)

def rankBoxMeasure (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) : Measure (CubePoint d) :=
  if n = 0 then cubePointLaw d else (n : ℝ≥0∞)⁻¹ • Measure.sum (fun j : Fin n => rankBoxLaw n d r j)

theorem rankBoxMeasure_isProbabilityMeasure (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) :
    IsProbabilityMeasure (rankBoxMeasure n d r) := by
  by_cases hn : n = 0
  · simp only [rankBoxMeasure, if_pos hn]
    infer_instance
  · constructor
    simp only [rankBoxMeasure, if_neg hn, Measure.smul_apply, smul_eq_mul,
      Measure.sum_apply_of_countable, measure_univ, tsum_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (by finiteness)

def rankBoxProbability (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) : ProbabilityMeasure (CubePoint d) :=
  ⟨rankBoxMeasure n d r, rankBoxMeasure_isProbabilityMeasure n d r⟩

/-- Every coordinate of the actual spread-out rank measure is exactly uniform
on [0,1], for every tuple of permutations. -/
theorem rankBoxMeasure_coordinate_uniform (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (i : Fin d) :
    (rankBoxMeasure n d r).map (fun x => x i) = cubeCoordinateLaw := by
  by_cases hn : n = 0
  · rw [rankBoxMeasure, if_pos hn]
    exact (measurePreserving_eval (fun _ : Fin d => cubeCoordinateLaw) i).map_eq
  · rw [rankBoxMeasure, if_neg hn, Measure.map_smul,
      Measure.map_sum (measurable_pi_apply i).aemeasurable]
    have hmap (j : Fin n) : (rankBoxLaw n d r j).map (fun x => x i) = scalarRankBoxLaw n (r i j) := by
      rw [rankBoxLaw_eq_product]
      exact (measurePreserving_eval (fun k : Fin d => scalarRankBoxLaw n (r k j)) i).map_eq
    simp_rw [hmap]
    rw [Measure.sum_fintype, Equiv.sum_comp (r i) (fun k => scalarRankBoxLaw n k)]
    exact scalarRankBoxLaw_mixture n (Nat.pos_of_ne_zero hn)

def rankCenterCloud (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) : CubeSample n d :=
  fun j i => rankMidpoint n (r i j)

theorem rankCenterCloud_mem_cube (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n) :
    rankCenterCloud n d r j ∈ cubePointSet d := fun i _ => rankMidpoint_mem_Icc (r i j)

theorem rankBoxPoint_mem_cube (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n)
    {u : CubePoint d} (hu : u ∈ cubePointSet d) : rankBoxPoint n d r j u ∈ cubePointSet d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  intro i _
  have hui : 0 ≤ u i ∧ u i ≤ 1 := hu i (mem_univ i)
  have hri : ((r i j).val : ℝ) + 1 ≤ n := by exact_mod_cast (r i j).isLt
  constructor
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) hui.1) hnR.le
  · exact (div_le_one hnR).mpr (by linarith)

theorem rankBoxPoint_dist_center_le (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n)
    {u : CubePoint d} (hu : u ∈ cubePointSet d) :
    dist (rankBoxPoint n d r j u) (rankCenterCloud n d r j) ≤ 1 / (2 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)))).mpr
  intro i
  rw [Real.dist_eq]
  have hui : 0 ≤ u i ∧ u i ≤ 1 := hu i (mem_univ i)
  change |(((r i j).val : ℝ) + u i) / n - (((r i j).val : ℝ) + 1 / 2) / n| ≤ _
  rw [← sub_div, show (((r i j).val : ℝ) + u i) - (((r i j).val : ℝ) + 1 / 2) =
    u i - 1 / 2 by ring, abs_div, abs_of_pos hnR]
  have hhalf : |u i - 1 / 2| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (div_le_div_of_nonneg_right hhalf hnR.le).trans_eq (by ring)

theorem ae_cubePointLaw_mem_cube (d : ℕ) : ∀ᵐ u ∂cubePointLaw d, u ∈ cubePointSet d := by
  rw [cubePointLaw_eq_volume_restrict]
  exact ae_restrict_mem (measurableSet_cubePointSet d)

theorem rankBoxLaw_ae_mem_cube (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) (j : Fin n) :
    ∀ᵐ u ∂rankBoxLaw n d r j, u ∈ cubePointSet d := by
  unfold rankBoxLaw
  apply (ae_map_iff (rankBoxPoint_continuous n d r j).measurable.aemeasurable
    (show MeasurableSet {u : CubePoint d | u ∈ cubePointSet d} from measurableSet_cubePointSet d)).mpr
  exact (ae_cubePointLaw_mem_cube d).mono (fun _ h => rankBoxPoint_mem_cube n d r j h)

theorem rankBoxMeasure_ae_mem_cube (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) :
    ∀ᵐ u ∂rankBoxMeasure n d r, u ∈ cubePointSet d := by
  by_cases hn : n = 0
  · rw [rankBoxMeasure, if_pos hn]
    exact ae_cubePointLaw_mem_cube d
  · rw [rankBoxMeasure, if_neg hn]
    apply Measure.ae_smul_measure
    exact (Measure.ae_sum_iff).mpr (fun j => rankBoxLaw_ae_mem_cube n d r j)

theorem rankBoxProbability_permuton_properties (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) :
    (rankBoxProbability n d r : Measure (CubePoint d)) (cubePointSet d) = 1 ∧
      ∀ i : Fin d, (rankBoxProbability n d r : Measure (CubePoint d)).map (fun x => x i) =
        cubeCoordinateLaw := by
  constructor
  · letI := rankBoxMeasure_isProbabilityMeasure n d r
    exact (mem_ae_iff_prob_eq_one (μ := rankBoxMeasure n d r)
      (measurableSet_cubePointSet d)).mp
      (rankBoxMeasure_ae_mem_cube n d r)
  · exact rankBoxMeasure_coordinate_uniform n d r

theorem rankBoxProbability_integral (n d : ℕ) (hn : 0 < n) (r : Fin d → Equiv.Perm (Fin n))
    (g : CubePoint d →ᵇ ℝ) :
    (∫ u, g u ∂(rankBoxProbability n d r : Measure (CubePoint d))) =
      (∑ j, ∫ u, g u ∂rankBoxLaw n d r j) / (n : ℝ) := by
  letI := rankBoxMeasure_isProbabilityMeasure n d r
  change (∫ u, g u ∂rankBoxMeasure n d r) = _
  rw [rankBoxMeasure, if_neg hn.ne', integral_smul_measure, Measure.sum_fintype,
    integral_finset_sum_measure (fun j _ => g.integrable (μ := rankBoxLaw n d r j))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _

/-- Uniform continuity on the cube controls the literal box spreading error,
uniformly over every rank tuple. No limiting permuton theorem is assumed. -/
theorem rankBoxProbability_test_error (d : ℕ) (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ r : Fin d → Equiv.Perm (Fin n),
      |(∫ u, g u ∂(rankBoxProbability n d r : Measure (CubePoint d))) -
        (∫ u, g u ∂(empiricalCubeProbability n d (rankCenterCloud n d r) : Measure (CubePoint d)))| ≤
          epsilon := by
  obtain ⟨delta, hd, huc⟩ := Metric.uniformContinuousOn_iff.mp
    ((cubePointSet_isCompact d).uniformContinuousOn_of_continuous g.continuous.continuousOn)
      epsilon hepsilon
  have hlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (2 * delta) < n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℕ)] with n hnlarge hn r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall : (1 : ℝ) / (2 * (n : ℝ)) < delta := by
    have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * delta)).mp hnlarge
    exact (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  have herr (j : Fin n) : |(∫ u, g u ∂rankBoxLaw n d r j) - g (rankCenterCloud n d r j)| ≤ epsilon := by
    rw [rankBoxLaw, integral_map (rankBoxPoint_continuous n d r j).measurable.aemeasurable
      g.continuous.aestronglyMeasurable]
    let f : CubePoint d →ᵇ ℝ := g.compContinuous ⟨rankBoxPoint n d r j, rankBoxPoint_continuous n d r j⟩
    change |(∫ u, f u ∂cubePointLaw d) - g (rankCenterCloud n d r j)| ≤ _
    have hconst : (∫ _u : CubePoint d, g (rankCenterCloud n d r j) ∂cubePointLaw d) =
        g (rankCenterCloud n d r j) := by simp
    rw [← hconst, ← integral_sub (f.integrable (μ := cubePointLaw d)) (integrable_const _)]
    calc
      _ ≤ ∫ u, |f u - g (rankCenterCloud n d r j)| ∂cubePointLaw d := abs_integral_le_integral_abs
      _ ≤ ∫ _u, epsilon ∂cubePointLaw d := by
        apply integral_mono_ae ((f.integrable (μ := cubePointLaw d)).sub (integrable_const _)).abs
          (integrable_const _)
        filter_upwards [ae_cubePointLaw_mem_cube d] with u hu
        have hh := huc (rankBoxPoint n d r j u) (rankBoxPoint_mem_cube n d r j hu)
          (rankCenterCloud n d r j) (rankCenterCloud_mem_cube n d r j)
          ((rankBoxPoint_dist_center_le n d r j hu).trans_lt hsmall)
        exact hh.le
      _ = epsilon := by simp
  rw [rankBoxProbability_integral n d hn r g,
    empiricalCubeProbability_integral n d hn (rankCenterCloud n d r) g]
  calc
    _ = |∑ j, ((∫ u, g u ∂rankBoxLaw n d r j) - g (rankCenterCloud n d r j))| / n := by
      rw [Finset.sum_sub_distrib, ← sub_div, abs_div, abs_of_pos hnR]
    _ ≤ (∑ j, |(∫ u, g u ∂rankBoxLaw n d r j) - g (rankCenterCloud n d r j)|) / n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ (∑ _j : Fin n, epsilon) / n :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => herr j)) hnR.le
    _ = epsilon := by simp [hnR.ne']

def cubeRankBoxProbability (n d : ℕ) (x : CubeSample n d) : ProbabilityMeasure (CubePoint d) :=
  rankBoxProbability n d (coordinateRankPermutations n d x)

def rankEmpiricalProbability (n d : ℕ) (x : CubeSample n d) : ProbabilityMeasure (CubePoint d) :=
  empiricalCubeProbability n d (cubeRankCloud n d x)

end Antichain
