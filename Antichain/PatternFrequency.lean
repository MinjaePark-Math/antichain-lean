import Antichain.RankPermuton
import Antichain.PatternWeakContinuity
import Antichain.PatternSampling
import Antichain.PatternBoxSampling

/-! Literal finite permutation pattern frequencies and their rank-box limits. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

set_option maxHeartbeats 800000

/-- A q-point pattern is recorded after sorting the first coordinate; the
remaining m coordinates are genuine permutations of the q ranks. -/
def patternEvent (q m : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) : Set (CubeSample q (m + 1)) :=
  {x | ∃ e : Equiv.Perm (Fin q), ∀ i : Fin (m + 1), ∀ j k : Fin q, j < k →
    if (Fin.cons (Equiv.refl (Fin q)) tau : Fin (m + 1) → Equiv.Perm (Fin q)) i j <
        (Fin.cons (Equiv.refl (Fin q)) tau : Fin (m + 1) → Equiv.Perm (Fin q)) i k
    then x (e j) i < x (e k) i else x (e k) i < x (e j) i}

theorem patternEvent_isOpen (q m : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) :
    IsOpen (patternEvent q m tau) := by
  classical
  simp only [patternEvent, Set.setOf_exists, Set.setOf_forall]
  apply isOpen_iUnion
  intro e
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro k
  apply isOpen_iInter_of_finite
  intro hjk
  split_ifs
  · exact isOpen_lt (show Continuous (fun x : CubeSample q (m + 1) => x (e j) i) by fun_prop)
      (show Continuous (fun x : CubeSample q (m + 1) => x (e k) i) by fun_prop)
  · exact isOpen_lt (show Continuous (fun x : CubeSample q (m + 1) => x (e k) i) by fun_prop)
      (show Continuous (fun x : CubeSample q (m + 1) => x (e j) i) by fun_prop)

theorem patternEvent_order_congr (q m : ℕ) (tau : Fin m → Equiv.Perm (Fin q))
    (x y : CubeSample q (m + 1))
    (h : ∀ i j k, (x j i < x k i ↔ y j i < y k i)) :
    x ∈ patternEvent q m tau ↔ y ∈ patternEvent q m tau := by
  simp only [patternEvent, Set.mem_setOf_eq]
  constructor <;> rintro ⟨e, he⟩ <;> refine ⟨e, ?_⟩ <;> intro i j k hjk
  · specialize he i j k hjk
    split_ifs at he ⊢
    · exact (h i (e j) (e k)).mp he
    · exact (h i (e k) (e j)).mp he
  · specialize he i j k hjk
    split_ifs at he ⊢
    · exact (h i (e j) (e k)).mpr he
    · exact (h i (e k) (e j)).mpr he

theorem patternEvent_not_frontier_of_tieFree (q m : ℕ)
    (tau : Fin m → Equiv.Perm (Fin q)) (x : CubeSample q (m + 1))
    (hx : CoordinateTieFree q (m + 1) x) : x ∉ frontier (patternEvent q m tau) := by
  let C : Set (CubeSample q (m + 1)) :=
    {y | ∀ i j k, x j i < x k i → y j i < y k i}
  have hCopen : IsOpen C := by
    simp only [C, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro h
    exact isOpen_lt (show Continuous (fun y : CubeSample q (m + 1) => y j i) by fun_prop)
      (show Continuous (fun y : CubeSample q (m + 1) => y k i) by fun_prop)
  have hxC : x ∈ C := fun _ _ _ h => h
  have heq (y : CubeSample q (m + 1)) (hy : y ∈ C) :
      x ∈ patternEvent q m tau ↔ y ∈ patternEvent q m tau := by
    apply patternEvent_order_congr
    intro i j k
    constructor
    · exact hy i j k
    · intro hylt
      by_contra hnot
      by_cases hjk : j = k
      · subst k
        exact lt_irrefl _ hylt
      · have hne : x j i ≠ x k i := fun h => hjk (hx i h)
        have hrev : x k i < x j i := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)
        exact (not_lt_of_gt (hy i k j hrev)) hylt
  intro hfront
  change x ∈ closure (patternEvent q m tau) ∧ x ∉ interior (patternEvent q m tau) at hfront
  by_cases hpat : x ∈ patternEvent q m tau
  · apply hfront.2
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (hCopen.mem_nhds hxC) (fun y hy => (heq y hy).mp hpat)
  · have hcompl : x ∈ interior (patternEvent q m tau)ᶜ := by
      apply mem_interior_iff_mem_nhds.mpr
      exact Filter.mem_of_superset (hCopen.mem_nhds hxC) (fun y hy h => hpat ((heq y hy).mpr h))
    have : x ∉ closure (patternEvent q m tau) := by
      simpa only [interior_compl, Set.mem_compl_iff] using hcompl
    exact this hfront.1

theorem iid_permuton_coordinateTieFree_ae (q d : ℕ) (nu : ProbabilityMeasure (CubePoint d))
    (hnu : ∀ i : Fin d, (nu : Measure (CubePoint d)).map (fun x => x i) = cubeCoordinateLaw) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin q => (nu : Measure (CubePoint d))), CoordinateTieFree q d x := by
  apply ae_all_iff.mpr
  intro i
  have hmap : (Measure.pi (fun _ : Fin q => (nu : Measure (CubePoint d)))).map
      (fun x j => x j i) = Measure.pi (fun _ : Fin q => cubeCoordinateLaw) := by
    rw [Measure.pi_map_pi (fun _ => (measurable_pi_apply i).aemeasurable)]
    simp_rw [hnu i]
  have ha := iid_scalar_injective_ae q cubeCoordinateLaw
  rw [← hmap] at ha
  exact (ae_map_iff (measurable_pi_lambda _ (fun j =>
    (measurable_pi_apply i).comp (measurable_pi_apply j))).aemeasurable
      (measurableSet_scalarInjective q)).mp ha

def patternProbability (q m : ℕ) (tau : Fin m → Equiv.Perm (Fin q))
    (nu : ProbabilityMeasure (CubePoint (m + 1))) : ℝ :=
  ((Measure.pi (fun _ : Fin q => (nu : Measure (CubePoint (m + 1))))) (patternEvent q m tau)).toReal

theorem patternProbability_continuousAt_permuton (q m : ℕ) (tau : Fin m → Equiv.Perm (Fin q))
    (nu : ProbabilityMeasure (CubePoint (m + 1)))
    (hnu : ∀ i : Fin (m + 1), (nu : Measure (CubePoint (m + 1))).map (fun x => x i) = cubeCoordinateLaw) :
    ContinuousAt (patternProbability q m tau) nu := by
  apply iidEventProbability_continuousAt
  apply measure_mono_null (fun x hx => ?_)
    (show (Measure.pi (fun _ : Fin q => (nu : Measure (CubePoint (m + 1)))))
      {x | ¬ CoordinateTieFree q (m + 1) x} = 0 from
      ae_iff.mp (iid_permuton_coordinateTieFree_ae q (m + 1) nu hnu))
  exact fun ht => patternEvent_not_frontier_of_tieFree q m tau x ht hx

theorem rankMidpoint_lt_iff {n : ℕ} (r s : Fin n) : rankMidpoint n r < rankMidpoint n s ↔ r < s := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  rw [rankMidpoint, rankMidpoint, div_lt_div_iff_of_pos_right hn, add_lt_add_iff_right]
  exact_mod_cast (Iff.rfl : r.val < s.val ↔ r.val < s.val)

theorem scalarRankBoxMap_order_iff {n : ℕ} (r s : Fin n) (hrs : r ≠ s)
    {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    scalarRankBoxMap n r u < scalarRankBoxMap n s v ↔ rankMidpoint n r < rankMidpoint n s := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt r.isLt
  rw [rankMidpoint_lt_iff]
  have hforward {a b : Fin n} (hab : a < b) {z w : ℝ}
      (hz : z ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
      scalarRankBoxMap n a z < scalarRankBoxMap n b w := by
    have hg : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast hab
    apply (div_lt_div_iff_of_pos_right hn).mpr
    linarith [hz.2, hw.1]
  constructor
  · intro h
    by_contra hnot
    have hsr : s < r := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hrs)
    exact (not_lt_of_gt (hforward hsr hv hu)) h
  · exact fun h => hforward h hu hv

theorem sampled_rank_box_pattern_iff {n q m : ℕ}
    (tau : Fin m → Equiv.Perm (Fin q)) (r : Fin (m + 1) → Equiv.Perm (Fin n))
    (f : Fin q → Fin n) (hf : Function.Injective f) (u : CubeSample q (m + 1))
    (hu : ∀ j i, u j i ∈ Ioo (0 : ℝ) 1) :
    (fun j => rankBoxPoint n (m + 1) r (f j) (u j)) ∈ patternEvent q m tau ↔
      (fun j => rankCenterCloud n (m + 1) r (f j)) ∈ patternEvent q m tau := by
  apply patternEvent_order_congr
  intro i j k
  by_cases hjk : j = k
  · subst k
    simp
  · exact scalarRankBoxMap_order_iff (r i (f j)) (r i (f k))
      (fun h => hjk (hf ((r i).injective h))) (hu j i) (hu k i)

theorem patternEvent_relabel_iff (q m : ℕ) (tau : Fin m → Equiv.Perm (Fin q))
    (x : CubeSample q (m + 1)) (p : Equiv.Perm (Fin q)) :
    (fun j => x (p j)) ∈ patternEvent q m tau ↔ x ∈ patternEvent q m tau := by
  simp only [patternEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.trans p, he⟩
  · rintro ⟨e, he⟩
    refine ⟨e.trans p.symm, ?_⟩
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using he

/-- The literal finite pattern frequency: draw q distinct source labels
uniformly without replacement and read their induced coordinate-order pattern.
The event is invariant under ordering these labels. -/
def permutationPatternFrequency (n m q : ℕ) (tau : Fin m → Equiv.Perm (Fin q))
    (pi : Fin m → Equiv.Perm (Fin n)) : ℝ :=
  (injectionPatternLabelLaw n q).real
    {f | (fun j => permutationRankCloud n m pi (f j)) ∈ patternEvent q m tau}

/-- An explicit normalized finite count, rather than an abstract functional
on probability measures. The denominator is the number of ordered selections
of q distinct labels. -/
theorem permutationPatternFrequency_count_formula (n m q : ℕ)
    (tau : Fin m → Equiv.Perm (Fin q)) (pi : Fin m → Equiv.Perm (Fin n)) :
    permutationPatternFrequency n m q tau pi =
      (Nat.card {f : Fin q → Fin n // Function.Injective f ∧
        (fun j => permutationRankCloud n m pi (f j)) ∈ patternEvent q m tau} : ℝ) /
          (n.descFactorial q : ℝ) :=
  injectionPatternLabelLaw_count_descFactorial n q _

/-- The exact collision error for the literal finite permutation frequency
and the actual uniform-box permuton probability. -/
theorem permutationPatternFrequency_box_error (n m q : ℕ) [NeZero n]
    (tau : Fin m → Equiv.Perm (Fin q)) (pi : Fin m → Equiv.Perm (Fin n)) :
    |permutationPatternFrequency n m q tau pi -
      patternProbability q m tau (permutationRankBoxProbability n m pi)| ≤ (q.choose 2 : ℝ) / n := by
  let r : Fin (m + 1) → Equiv.Perm (Fin n) := Fin.cons (Equiv.refl (Fin n)) pi
  let P : Set ((Fin q → Fin n) × CubeSample q (m + 1)) :=
    rankBoxSampleMap n q (m + 1) r ⁻¹' patternEvent q m tau
  let Q : Set (Fin q → Fin n) :=
    {f | (fun j => permutationRankCloud n m pi (f j)) ∈ patternEvent q m tau}
  have hsnd : MeasurePreserving
      (Prod.snd : ((Fin q → Fin n) × CubeSample q (m + 1)) → CubeSample q (m + 1))
      ((iidPatternLabelLaw n q).prod (cubeSampleLaw q (m + 1))) (cubeSampleLaw q (m + 1)) :=
    measurePreserving_snd
  have haux := hsnd.quasiMeasurePreserving.tendsto_ae.eventually
    (ae_cubeSample_mem_openCube q (m + 1))
  have hagree : ∀ᵐ z ∂(iidPatternLabelLaw n q).prod (cubeSampleLaw q (m + 1)),
      Function.Injective z.1 → (z ∈ P ↔ z.1 ∈ Q) := by
    filter_upwards [haux] with z hz
    intro hf
    exact sampled_rank_box_pattern_iff tau r z.1 hf z.2 hz
  have herr := iid_injection_aux_event_error n q (cubeSampleLaw q (m + 1)) P Q hagree
  change |(((iidPatternLabelLaw n q).prod (cubeSampleLaw q (m + 1)))
    ((rankBoxSampleMap n q (m + 1) r) ⁻¹' patternEvent q m tau)).toReal -
    permutationPatternFrequency n m q tau pi| ≤ _ at herr
  rw [← Measure.map_apply (rankBoxSampleMap_measurable n q (m + 1) r)
    (patternEvent_isOpen q m tau).measurableSet] at herr
  change |(((Measure.pi (fun _ : Fin q => (PMF.uniformOfFintype (Fin n)).toMeasure)).prod
      (cubeSampleLaw q (m + 1))).map (rankBoxSampleMap n q (m + 1) r)
        (patternEvent q m tau)).toReal - _| ≤ _ at herr
  rw [rankBoxSampleMap_law] at herr
  change |patternProbability q m tau (permutationRankBoxProbability n m pi) -
    permutationPatternFrequency n m q tau pi| ≤ _ at herr
  rwa [abs_sub_comm] at herr

/-- Every fixed genuine finite pattern frequency has the source's exponential
concentration under the actual uniform avoidance class. No pattern continuity,
sampling approximation, or concentration conclusion is an input. -/
theorem permutation_pattern_frequency_exponential_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput)
    (q : ℕ) (tau : Fin m → Equiv.Perm (Fin q)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.uniformOn (avoidanceRankSet n m)
        {pi | epsilon ≤ |permutationPatternFrequency n m q tau pi -
          patternProbability q m tau (limitingCubeProbability (m + 1))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hmu : ∀ i : Fin (m + 1),
      (limitingCubeProbability (m + 1) : Measure (CubePoint (m + 1))).map (fun x => x i) =
        cubeCoordinateLaw := fun i => limitingAntichainMeasure_coordinate_map (by simpa using (show 2 ≤ m + 1 by omega)) i
  have hcont := patternProbability_continuousAt_permuton q m tau (limitingCubeProbability (m + 1)) hmu
  let U : Set (ProbabilityMeasure (CubePoint (m + 1))) :=
    {nu | |patternProbability q m tau nu - patternProbability q m tau (limitingCubeProbability (m + 1))| < epsilon / 2}
  have hball : ∀ᶠ z : ℝ in 𝓝 (patternProbability q m tau (limitingCubeProbability (m + 1))),
      |z - patternProbability q m tau (limitingCubeProbability (m + 1))| < epsilon / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (Metric.ball_mem_nhds (patternProbability q m tau (limitingCubeProbability (m + 1)))
        (show 0 < epsilon / 2 by positivity))
  have hU : U ∈ 𝓝 (limitingCubeProbability (m + 1)) := hcont.eventually hball
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_permuton_exponential_concentration hm H DKW hU
  have hlarge : ∀ᶠ n : ℕ in atTop, (4 * (q.choose 2 : ℝ)) / epsilon ≤ n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, hlarge, eventually_gt_atTop (0 : ℕ)] with n hn hnlarge hnpos
  letI : NeZero n := ⟨hnpos.ne'⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsmall : (q.choose 2 : ℝ) / n ≤ epsilon / 4 := by
    have hh := (div_le_iff₀ hepsilon).mp hnlarge
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  apply le_trans (measure_mono ?_) hn
  intro pi hbad
  by_contra hnot
  have hbox : permutationRankBoxProbability n m pi ∈ U := not_not.mp (fun h => hnot (Or.inr h))
  have herr := (permutationPatternFrequency_box_error n m q tau pi).trans hsmall
  have htri := abs_sub_le (permutationPatternFrequency n m q tau pi)
    (patternProbability q m tau (permutationRankBoxProbability n m pi))
    (patternProbability q m tau (limitingCubeProbability (m + 1)))
  change |patternProbability q m tau (permutationRankBoxProbability n m pi) -
    patternProbability q m tau (limitingCubeProbability (m + 1))| < epsilon / 2 at hbox
  change epsilon ≤ _ at hbad
  linarith

end Antichain
