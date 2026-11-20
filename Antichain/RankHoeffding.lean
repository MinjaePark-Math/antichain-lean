import Antichain.RankCDF
import Antichain.UniformCDFConcentration
import Antichain.ShapeGeometry

/-! The revised manuscript's fixed-order-statistic Hoeffding proof.
The actual iid uniform and conditioned sorted-coordinate laws are used. -/
noncomputable section
namespace Antichain
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology

theorem centeredCDFIndicator_sharp_subgaussian {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (positive : Bool) :
    HasSubgaussianMGF (centeredCDFIndicator s positive) (1 / 4) cubeCoordinateLaw := by
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
  cases positive
  · have hb : ∀ᵐ u ∂cubeCoordinateLaw, centeredCDFIndicator s false u ∈ Icc (s - 1) s := by
      apply Filter.Eventually.of_forall
      intro u
      have hu := uniformCDFIndicator_mem_Icc s u
      change s - uniformCDFIndicator s u ∈ Icc (s - 1) s
      constructor <;> linarith [hu.1, hu.2]
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (centeredCDFIndicator_measurable s false).aemeasurable hb hm
    rw [show s - (s - 1) = 1 by ring] at h
    norm_num at h
    exact h
  · have hb : ∀ᵐ u ∂cubeCoordinateLaw, centeredCDFIndicator s true u ∈ Icc (-s) (1 - s) := by
      apply Filter.Eventually.of_forall
      intro u
      have hu := uniformCDFIndicator_mem_Icc s u
      change uniformCDFIndicator s u - s ∈ Icc (-s) (1 - s)
      constructor <;> linarith [hu.1, hu.2]
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (centeredCDFIndicator_measurable s true).aemeasurable hb hm
    rw [show 1 - s - -s = 1 by ring] at h
    norm_num at h
    exact h

theorem uniform_cdf_hoeffding_one_sided (n : ℕ) (hn : 0 < n) {s delta : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hdelta : 0 < delta) (positive : Bool) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      {x | delta ≤ if positive then uniformEmpiricalCDF n x s - s else s - uniformEmpiricalCDF n x s} ≤
      ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * delta ^ 2)) := by
  let X : Fin n → (Fin n → ℝ) → ℝ := fun j x => centeredCDFIndicator s positive (x j)
  have hind : iIndepFun X (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) :=
    iIndepFun_pi (fun _ => (centeredCDFIndicator_measurable s positive).aemeasurable)
  have hsg (j : Fin n) : HasSubgaussianMGF (X j) (1 / 4) (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) := by
    have h := centeredCDFIndicator_sharp_subgaussian hs positive
    rw [← (measurePreserving_eval (fun _ : Fin n => cubeCoordinateLaw) j).map_eq] at h
    exact HasSubgaussianMGF.of_map (μ := Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      (X := centeredCDFIndicator s positive) (Y := fun x : Fin n → ℝ => x j)
      (measurable_pi_apply j).aemeasurable h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := univ) (c := fun _ => (1 / 4 : ℝ≥0)) (fun j _ => hsg j)
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
  have hexp : -((n : ℝ) * delta) ^ 2 / (2 * ((n : ℝ) * (1 / 4))) =
      -2 * (n : ℝ) * delta ^ 2 := by field_simp; ring
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat] at h
  rw [hexp] at h
  rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

theorem sorted_upper_cdf_le {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (r : Fin n) {t : ℝ}
    (ht : t < sampleSortedValues x r) :
    uniformEmpiricalCDF n x t ≤ (r.val : ℝ) / n := by
  classical
  let e := sampleSortPermutation x
  have he := sampleSortPermutation_strictMono x hx
  have hsub : univ.filter (fun j => x j ≤ t) ⊆ (Finset.Iio r).map e.toEmbedding := by
    intro j hj
    refine Finset.mem_map.mpr ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    apply Finset.mem_Iio.mpr
    apply he.lt_iff_lt.mp
    have hlt : x j < x (e r) := (Finset.mem_filter.mp hj).2.trans_lt ht
    change x (e (e.symm j)) < x (e r)
    simpa only [Equiv.apply_symm_apply] using hlt
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_map, Fin.card_Iio] at hc
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg n)

theorem sorted_lower_cdf_ge {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (r : Fin n) {t : ℝ}
    (ht : sampleSortedValues x r < t) :
    ((r.val : ℝ) + 1) / n ≤ uniformEmpiricalCDF n x t := by
  classical
  let e := sampleSortPermutation x
  have he := sampleSortPermutation_strictMono x hx
  have hsub : (Finset.Iic r).map e.toEmbedding ⊆ univ.filter (fun j => x j ≤ t) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (he.monotone (Finset.mem_Iic.mp hk)).trans ht.le
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_map, Fin.card_Iic] at hc
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast hc

theorem iidUniform_ae_mem_cube (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => cubeCoordinateLaw),
      ∀ j, x j ∈ Icc (0 : ℝ) 1 := by
  rw [show Measure.pi (fun _ : Fin n => cubeCoordinateLaw) =
      (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi (fun _ => Icc (0 : ℝ) 1)) from
        (Measure.restrict_pi_pi (fun _ => (volume : Measure ℝ)) _).symm]
  exact (ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))).mono
    (fun _ h j => h j (Set.mem_univ j))

theorem scalarSortedLaw_midpoint_upper_hoeffding {n : ℕ} (hn : 0 < n)
    (r : Fin n) {s : ℝ} (hs : 0 < s) :
    scalarSortedLaw n {y | rankMidpoint n r + s < y r} ≤
      ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * s ^ 2)) := by
  let t := rankMidpoint n r + s
  have hmeas : MeasurableSet {y : Fin n → ℝ | t < y r} :=
    (isOpen_lt continuous_const (continuous_apply r)).measurableSet
  rw [scalarSortedLaw, Measure.map_apply (sampleSortedValues_measurable n) hmeas]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases ht : t ≤ 1
  · have ht0 : 0 ≤ t := (rankMidpoint_mem_Icc r).1.trans (le_add_of_nonneg_right hs.le)
    apply le_trans (measure_mono_ae ?_) (uniform_cdf_hoeffding_one_sided n hn ⟨ht0, ht⟩ hs false)
    filter_upwards [iid_scalar_injective_ae n cubeCoordinateLaw] with x hx
    intro hbad
    have hc := sorted_upper_cdf_le x hx r hbad
    change s ≤ t - uniformEmpiricalCDF n x t
    dsimp [t, rankMidpoint] at *
    have hfrac : (r.val : ℝ) / n ≤ ((r.val : ℝ) + 1 / 2) / n :=
      div_le_div_of_nonneg_right (by linarith) hnR.le
    linarith
  · apply le_trans (b := (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) ∅)
      (measure_mono_ae ?_) (by simp)
    filter_upwards [iidUniform_ae_mem_cube n] with x hx
    intro hbad
    have hy := (hx (sampleSortPermutation x r)).2
    change t < sampleSortedValues x r at hbad
    change sampleSortedValues x r ≤ 1 at hy
    exact False.elim (not_lt_of_ge hy ((lt_of_not_ge ht).trans hbad))

theorem scalarSortedLaw_midpoint_lower_hoeffding {n : ℕ} (hn : 0 < n)
    (r : Fin n) {s : ℝ} (hs : 0 < s) :
    scalarSortedLaw n {y | y r < rankMidpoint n r - s} ≤
      ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * s ^ 2)) := by
  let t := rankMidpoint n r - s
  have hmeas : MeasurableSet {y : Fin n → ℝ | y r < t} :=
    (isOpen_lt (continuous_apply r) continuous_const).measurableSet
  rw [scalarSortedLaw, Measure.map_apply (sampleSortedValues_measurable n) hmeas]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases ht : 0 ≤ t
  · have ht1 : t ≤ 1 := (sub_le_self _ hs.le).trans (rankMidpoint_mem_Icc r).2
    apply le_trans (measure_mono_ae ?_) (uniform_cdf_hoeffding_one_sided n hn ⟨ht, ht1⟩ hs true)
    filter_upwards [iid_scalar_injective_ae n cubeCoordinateLaw] with x hx
    intro hbad
    have hc := sorted_lower_cdf_ge x hx r hbad
    change s ≤ uniformEmpiricalCDF n x t - t
    dsimp [t, rankMidpoint] at *
    have hfrac : ((r.val : ℝ) + 1 / 2) / n ≤ ((r.val : ℝ) + 1) / n :=
      div_le_div_of_nonneg_right (by linarith) hnR.le
    linarith
  · apply le_trans (b := (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) ∅)
      (measure_mono_ae ?_) (by simp)
    filter_upwards [iidUniform_ae_mem_cube n] with x hx
    intro hbad
    have hy := (hx (sampleSortPermutation x r)).1
    change sampleSortedValues x r < t at hbad
    change 0 ≤ sampleSortedValues x r at hy
    exact False.elim (not_lt_of_ge hy (hbad.trans (lt_of_not_ge ht)))

theorem scalarSortedLaw_midpoint_hoeffding {n : ℕ} (hn : 0 < n)
    (r : Fin n) {s : ℝ} (hs : 0 < s) :
    scalarSortedLaw n {y | s < |y r - rankMidpoint n r|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * s ^ 2)) := by
  have hsub : {y : Fin n → ℝ | s < |y r - rankMidpoint n r|} ⊆
      {y | rankMidpoint n r + s < y r} ∪ {y | y r < rankMidpoint n r - s} := by
    intro y hy
    change s < |y r - rankMidpoint n r| at hy
    change rankMidpoint n r + s < y r ∨ y r < rankMidpoint n r - s
    rcases lt_abs.mp hy with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (scalarSortedLaw_midpoint_upper_hoeffding hn r hs)
      (scalarSortedLaw_midpoint_lower_hoeffding hn r hs)
    _ = _ := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring

theorem scalarSortedLaw_all_midpoints_hoeffding {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 0 < s) :
    scalarSortedLaw n (sortedMidpointBad n s) ≤
      ENNReal.ofReal (2 * (n : ℝ) * Real.exp (-2 * (n : ℝ) * s ^ 2)) := by
  have hset : sortedMidpointBad n s =
      ⋃ r : Fin n, {y | s < |y r - rankMidpoint n r|} := by ext y; simp [sortedMidpointBad]
  rw [hset]
  calc
    _ ≤ _ := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _r : Fin n, ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * s ^ 2)) :=
      Finset.sum_le_sum (fun r _ => scalarSortedLaw_midpoint_hoeffding hn r hs)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

theorem conditional_sorted_midpoint_hoeffding (d : ℕ) (hd : 2 ≤ d)
    {n : ℕ} (hn : 0 < n) (i : Fin d) (r : Fin n) {s : ℝ} (hs : 0 < s) :
    cubeAntichainLaw n d {x | s < |coordinateSortedValues n d x i r - rankMidpoint n r|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * s ^ 2)) := by
  have hm : Measurable (fun x : CubeSample n d => coordinateSortedValues n d x i) :=
    (measurable_pi_apply i).comp (coordinateSortedValues_measurable n d)
  have hA : MeasurableSet {y : Fin n → ℝ | s < |y r - rankMidpoint n r|} :=
    (isOpen_lt continuous_const (((continuous_apply r).sub continuous_const).abs)).measurableSet
  change cubeAntichainLaw n d ((fun x => coordinateSortedValues n d x i) ⁻¹'
    {y : Fin n → ℝ | s < |y r - rankMidpoint n r|}) ≤ _
  rw [← Measure.map_apply hm hA, cubeAntichain_sortedCoordinate_law n d hd i]
  exact scalarSortedLaw_midpoint_hoeffding hn r hs

theorem rank_coordinate_displacement_hoeffding (d : ℕ) (hd : 2 ≤ d)
    {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    cubeAntichainLaw n d (rankDisplacementEvent n d s) ≤
      ENNReal.ofReal (2 * (d : ℝ) * n * Real.exp (-2 * (n : ℝ) * s ^ 2)) := by
  rw [rankDisplacementEvent_eq_sorted_union]
  calc
    _ ≤ _ := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin d, ENNReal.ofReal (2 * (n : ℝ) * Real.exp (-2 * (n : ℝ) * s ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      have hm : Measurable (fun x : CubeSample n d => coordinateSortedValues n d x i) :=
        (measurable_pi_apply i).comp (coordinateSortedValues_measurable n d)
      rw [← Measure.map_apply hm (measurableSet_sortedMidpointBad n s),
        cubeAntichain_sortedCoordinate_law n d hd i]
      exact scalarSortedLaw_all_midpoints_hoeffding hn hs
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      congr 1
      ring

def rankEuclideanDisplacement (n d : ℕ) (x : CubeSample n d) : ℝ :=
  (Finset.univ.sup (fun j : Fin n =>
    nndist (WithLp.toLp 2 (x j) : EuclideanSpace ℝ (Fin d))
      (WithLp.toLp 2 (cubeRankCloud n d x j))) : ℝ≥0)

theorem rankEuclideanDisplacement_le (n d : ℕ) (x : CubeSample n d)
    {s : ℝ} (hs : 0 ≤ s) (hclose : ∀ j i, |x j i - cubeRankCloud n d x j i| ≤ s) :
    rankEuclideanDisplacement n d x ≤ Real.sqrt (d : ℝ) * s := by
  unfold rankEuclideanDisplacement
  change _ ≤ ((⟨Real.sqrt (d : ℝ) * s, mul_nonneg (Real.sqrt_nonneg _) hs⟩ : ℝ≥0) : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro j _
  have hc : dist (x j) (cubeRankCloud n d x j) ≤ s :=
    (dist_pi_le_iff hs).mpr (fun i => by simpa only [Real.dist_eq] using hclose j i)
  have h := (cube_euclidean_dist_le d (x j) (cubeRankCloud n d x j)).trans
    (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _))
  exact_mod_cast h

theorem rank_euclidean_displacement_hoeffding (d : ℕ) (hd : 2 ≤ d)
    {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    cubeAntichainLaw n d {x | s < rankEuclideanDisplacement n d x} ≤
      ENNReal.ofReal (2 * (d : ℝ) * n * Real.exp (-2 * (n : ℝ) * s ^ 2 / d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hsub : {x : CubeSample n d | s < rankEuclideanDisplacement n d x} ⊆
      rankDisplacementEvent n d (s / Real.sqrt (d : ℝ)) := by
    intro x hx
    by_contra hnclose
    have hclose : ∀ j i, |x j i - cubeRankCloud n d x j i| ≤ s / Real.sqrt (d : ℝ) := by
      intro j i
      exact le_of_not_gt (fun h => hnclose ⟨j, i, h⟩)
    have h := rankEuclideanDisplacement_le n d x (div_nonneg hs.le hsqrt.le) hclose
    rw [mul_div_cancel₀ _ hsqrt.ne'] at h
    exact not_lt_of_ge h hx
  apply (measure_mono hsub).trans
  convert rank_coordinate_displacement_hoeffding d hd hn (div_pos hs hsqrt) using 1
  congr 3
  rw [div_pow, Real.sq_sqrt hdR.le]
  ring

theorem linear_prefactor_exp_eventually_le {C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, C * n * Real.exp (-2 * (n : ℝ) * a) ≤
      Real.exp (-a * (n : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := hconst.add hlog
  simp only [zero_add] at hsum
  filter_upwards [hsum.eventually (Iio_mem_nhds ha), eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hb : Real.log C + Real.log (n : ℝ) ≤ a * n := by
    have hdiv : (Real.log C + Real.log (n : ℝ)) / n < a := by rwa [add_div]
    exact ((div_lt_iff₀ hnR).mp hdiv).le
  rw [show C * n * Real.exp (-2 * (n : ℝ) * a) =
    Real.exp (Real.log C + Real.log (n : ℝ) + -2 * (n : ℝ) * a) by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hC, Real.exp_log hnR]]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem rank_displacement_exponential_tail_hoeffding (d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (rankDisplacementEvent n d epsilon) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨epsilon ^ 2, sq_pos_of_pos hepsilon, ?_⟩
  filter_upwards [linear_prefactor_exp_eventually_le
    (show 0 < 2 * (d : ℝ) by positivity) (sq_pos_of_pos hepsilon),
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  exact (rank_coordinate_displacement_hoeffding d hd hnpos hepsilon).trans
    (ENNReal.ofReal_le_ofReal hn)

end Antichain
