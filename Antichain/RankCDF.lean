import Antichain.RankIndependence
import Antichain.EmpiricalTopology
import Mathlib.Order.Interval.Finset.Fin

/-!
The cited Dvoretzky--Kiefer--Wolfowitz input is stated only for the actual
unconditional iid uniform sample and its empirical CDF. Rank displacement and
all conditioned statements are derived below.
-/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology

def scalarEmpiricalCDF (n : ℕ) (x : Fin n → ℝ) (s : ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun j => x j ≤ s)).card : ℝ) / (n : ℝ)

/-- Exactly the unconditional uniform-sample CDF inequality of Massart's sharp
DKW theorem. The existential event is `sup |D_n(s)-s| > delta` on [0,1]. -/
structure DKWInput : Prop where
  bound : ∀ n : ℕ, 0 < n → ∀ delta : ℝ, 0 < delta →
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      {x | ∃ s ∈ Icc (0 : ℝ) 1, delta < |scalarEmpiricalCDF n x s - s|} ≤
        ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * delta ^ 2))

/-- Source ranks are one-based; a zero-based finite rank r has midpoint
((r+1)-1/2)/n = (r+1/2)/n. -/
def rankMidpoint (n : ℕ) (r : Fin n) : ℝ := ((r.val : ℝ) + 1 / 2) / (n : ℝ)

theorem rankMidpoint_mem_Icc {n : ℕ} (r : Fin n) : rankMidpoint n r ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  have hr : (r.val : ℝ) + 1 ≤ n := by exact_mod_cast r.isLt
  constructor
  · exact div_nonneg (by positivity) hn.le
  · exact (div_le_one hn).mpr (by linarith)

theorem scalarEmpiricalCDF_at_sorted_value {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (r : Fin n) :
    scalarEmpiricalCDF n x (sampleSortedValues x r) = ((r.val : ℝ) + 1) / (n : ℝ) := by
  classical
  let e := sampleSortPermutation x
  have he := sampleSortPermutation_strictMono x hx
  have hset : Finset.univ.filter (fun j => x j ≤ x (e r)) = (Finset.Iic r).map e.toEmbedding := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      apply Finset.mem_Iic.mpr
      apply he.le_iff_le.mp
      simpa only [e, Equiv.apply_symm_apply] using hj
    · rintro ⟨k, hk, rfl⟩
      exact he.monotone (Finset.mem_Iic.mp hk)
  change ((Finset.univ.filter (fun j => x j ≤ x (e r))).card : ℝ) / n = _
  rw [hset, Finset.card_map, Fin.card_Iic]
  simp

/-- The deterministic order-statistic midpoint bound used in the paper. -/
theorem sorted_midpoint_error_le {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hxcube : ∀ j, x j ∈ Icc (0 : ℝ) 1) {delta : ℝ}
    (hCDF : ∀ s ∈ Icc (0 : ℝ) 1, |scalarEmpiricalCDF n x s - s| ≤ delta) :
    ∀ r : Fin n, |sampleSortedValues x r - rankMidpoint n r| ≤ delta + 1 / (2 * (n : ℝ)) := by
  intro r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy := hxcube (sampleSortPermutation x r)
  have hc := hCDF (sampleSortedValues x r) hy
  have hm : |scalarEmpiricalCDF n x (sampleSortedValues x r) - rankMidpoint n r| =
      1 / (2 * (n : ℝ)) := by
    rw [scalarEmpiricalCDF_at_sorted_value x hx, rankMidpoint]
    have heq : ((r.val : ℝ) + 1) / n - ((r.val : ℝ) + 1 / 2) / n = 1 / (2 * (n : ℝ)) := by
      field_simp
      ring
    rw [heq, abs_of_nonneg (by positivity)]
  have htri := abs_sub_le (sampleSortedValues x r)
    (scalarEmpiricalCDF n x (sampleSortedValues x r)) (rankMidpoint n r)
  rw [abs_sub_comm (sampleSortedValues x r) (scalarEmpiricalCDF n x (sampleSortedValues x r)), hm] at htri
  exact htri.trans (add_le_add_right hc _)

def sortedMidpointBad (n : ℕ) (epsilon : ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ r : Fin n, epsilon < |y r - rankMidpoint n r|}

theorem measurableSet_sortedMidpointBad (n : ℕ) (epsilon : ℝ) :
    MeasurableSet (sortedMidpointBad n epsilon) := by
  unfold sortedMidpointBad
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion (fun r =>
    (isOpen_lt continuous_const (((continuous_apply r).sub continuous_const).abs)).measurableSet)

theorem scalarSortedLaw_midpoint_exponential_tail (DKW : DKWInput) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      scalarSortedLaw n (sortedMidpointBad n epsilon) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  let delta := epsilon / 2
  have hd : 0 < delta := half_pos hepsilon
  have ha : 0 < delta ^ 2 := sq_pos_of_pos hd
  have hlarge1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / epsilon ≤ n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlarge2 : ∀ᶠ n : ℕ in atTop, Real.log 2 / delta ^ 2 ≤ n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨delta ^ 2, ha, ?_⟩
  filter_upwards [hlarge1, hlarge2, eventually_gt_atTop (0 : ℕ)] with n hnlarge hnlog hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall : delta + 1 / (2 * (n : ℝ)) ≤ epsilon := by
    have hnε : 1 ≤ (n : ℝ) * epsilon := (div_le_iff₀ hepsilon).mp hnlarge
    have hf : (1 : ℝ) / (2 * (n : ℝ)) ≤ epsilon / 2 :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    dsimp [delta]
    linarith
  have hcube : ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => cubeCoordinateLaw),
      ∀ j, x j ∈ Icc (0 : ℝ) 1 := by
    rw [show Measure.pi (fun _ : Fin n => cubeCoordinateLaw) =
      (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi (fun _ => Icc (0 : ℝ) 1)) from
        (Measure.restrict_pi_pi (fun _ => (volume : Measure ℝ)) _).symm]
    exact (ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))).mono
      (fun _ h j => h j (Set.mem_univ j))
  rw [scalarSortedLaw, Measure.map_apply (sampleSortedValues_measurable n)
    (measurableSet_sortedMidpointBad n epsilon)]
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
        {x | ∃ s ∈ Icc (0 : ℝ) 1, delta < |scalarEmpiricalCDF n x s - s|} := by
      apply measure_mono_ae
      filter_upwards [iid_scalar_injective_ae n cubeCoordinateLaw, hcube] with x hx hxcube
      intro hbad
      by_contra hnot
      have hCDF : ∀ s ∈ Icc (0 : ℝ) 1, |scalarEmpiricalCDF n x s - s| ≤ delta := by
        intro s hs
        exact le_of_not_gt (fun h => hnot ⟨s, hs, h⟩)
      obtain ⟨r, hr⟩ := hbad
      exact not_lt_of_ge ((sorted_midpoint_error_le hn x hx hxcube hCDF r).trans hsmall) hr
    _ ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * delta ^ 2)) := DKW.bound n hn delta hd
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [show 2 * Real.exp (-2 * (n : ℝ) * delta ^ 2) =
          Real.exp (Real.log 2 + -2 * (n : ℝ) * delta ^ 2) by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
      apply Real.exp_le_exp.mpr
      have hh := (div_le_iff₀ ha).mp hnlog
      nlinarith

def cubeRankCloud (n d : ℕ) (x : CubeSample n d) : CubeSample n d :=
  fun j i => rankMidpoint n (coordinateRankPermutations n d x i j)

def rankDisplacementEvent (n d : ℕ) (epsilon : ℝ) : Set (CubeSample n d) :=
  {x | ∃ j i, epsilon < |x j i - cubeRankCloud n d x j i|}

theorem cubeRankCloud_mem_cube (n d : ℕ) (x : CubeSample n d) (j : Fin n) :
    cubeRankCloud n d x j ∈ cubePointSet d :=
  fun i _ => rankMidpoint_mem_Icc (coordinateRankPermutations n d x i j)

theorem rankDisplacementEvent_eq_sorted_union (n d : ℕ) (epsilon : ℝ) :
    rankDisplacementEvent n d epsilon =
      ⋃ i : Fin d, (fun x => coordinateSortedValues n d x i) ⁻¹' sortedMidpointBad n epsilon := by
  ext x
  constructor
  · rintro ⟨j, i, hji⟩
    refine Set.mem_iUnion.mpr ⟨i, coordinateRankPermutations n d x i j, ?_⟩
    simpa only [coordinateSortedValues, coordinateRankPermutations, sampleSortedValues,
      sampleRankPermutation, Equiv.apply_symm_apply] using hji
  · intro hx
    obtain ⟨i, r, hr⟩ := Set.mem_iUnion.mp hx
    refine ⟨sampleSortPermutation (fun j => x j i) r, i, ?_⟩
    simpa only [cubeRankCloud, coordinateSortedValues, coordinateRankPermutations,
      sampleSortedValues, sampleRankPermutation, Equiv.symm_apply_apply] using hr

theorem cubeAntichain_sortedCoordinate_law (n d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    (cubeAntichainLaw n d).map (fun x => coordinateSortedValues n d x i) = scalarSortedLaw n := by
  have hdim : (cubeAntichainLaw n d).map (coordinateSortedValues n d) =
      Measure.pi (fun _ : Fin d => scalarSortedLaw n) := by
    cases d with
    | zero => omega
    | succ m =>
      have h := cubeAntichain_sortedCoordinates_law n m (by omega)
      rw [cube_sortedCoordinates_law] at h
      exact h
  change (cubeAntichainLaw n d).map ((fun y : Fin d → Fin n → ℝ => y i) ∘
    coordinateSortedValues n d) = _
  rw [← Measure.map_map (measurable_pi_apply i) (coordinateSortedValues_measurable n d), hdim]
  exact (measurePreserving_eval (fun _ : Fin d => scalarSortedLaw n) i).map_eq

/-- The rank cloud can be coupled to the actual conditioned cube sample with
an exponentially small probability of any fixed coordinate displacement. -/
theorem rank_displacement_exponential_tail (DKW : DKWInput) (d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d (rankDisplacementEvent n d epsilon) ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, hscalar⟩ := scalarSortedLaw_midpoint_exponential_tail DKW hepsilon
  have htail (i : Fin d) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      cubeAntichainLaw n d
        ((fun x => coordinateSortedValues n d x i) ⁻¹' sortedMidpointBad n epsilon) ≤
          ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    refine ⟨alpha, ha, hscalar.mono ?_⟩
    intro n hn
    have hmeas : Measurable (fun x : CubeSample n d => coordinateSortedValues n d x i) :=
      (measurable_pi_apply i).comp (coordinateSortedValues_measurable n d)
    rw [← Measure.map_apply hmeas
      (measurableSet_sortedMidpointBad n epsilon), cubeAntichain_sortedCoordinate_law n d hd i]
    exact hn
  obtain ⟨a, ha, htail⟩ := finite_union_exponential_tail
    (fun n => cubeAntichainLaw n d)
    (fun i n => (fun x => coordinateSortedValues n d x i) ⁻¹' sortedMidpointBad n epsilon) htail
  refine ⟨a, ha, ?_⟩
  simpa only [rankDisplacementEvent_eq_sorted_union] using htail

end Antichain
