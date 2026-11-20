import Antichain.IntervalGaussianPredictor
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Order.IntermediateValue

/-! The manuscript's actual cube-coordinate-shift proof of the support lemma.
Endpoint divergence and the intermediate-value witness are derived for the
actual inverse normal CDF, without a comparable-witness premise.
-/

noncomputable section

namespace Antichain

open Set Filter Finset
open scoped Topology

theorem normalQuantile_tendsto_zero_right :
    Tendsto normalQuantile (𝓝[>] (0 : ℝ)) atBot := by
  apply tendsto_atBot.mpr
  intro M
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (normalCDF_mem_Ioo M).1).filter_mono nhdsWithin_le_nhds]
    with x hx hM
  have hxmem : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨hx, lt_of_le_of_lt hM (normalCDF_mem_Ioo M).2⟩
  simpa only [normalQuantile_normalCDF] using
    normalQuantile_strictMonoOn.monotoneOn hxmem (normalCDF_mem_Ioo M) hM

theorem normalQuantile_tendsto_one_left :
    Tendsto normalQuantile (𝓝[<] (1 : ℝ)) atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [self_mem_nhdsWithin,
    (eventually_ge_nhds (normalCDF_mem_Ioo M).2).filter_mono nhdsWithin_le_nhds]
    with x hx hM
  have hxmem : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (normalCDF_mem_Ioo M).1 hM, hx⟩
  simpa only [normalQuantile_normalCDF] using
    normalQuantile_strictMonoOn.monotoneOn (normalCDF_mem_Ioo M) hxmem hM

section FiniteCoordinateLimits

variable {ι A : Type*} [Fintype ι] {l : Filter A}

private theorem sum_tendsto_atBot_of_coordinate
    (f : A → ι → ℝ) (j : ι) (c : ι → ℝ)
    (hbound : ∀ᶠ a in l, ∀ i, f a i ≤ c i)
    (hj : Tendsto (fun a => f a j) l atBot) :
    Tendsto (fun a => ∑ i, f a i) l atBot := by
  classical
  have hlim : Tendsto (fun a => f a j + ∑ i ∈ univ.erase j, c i) l atBot :=
    hj.atBot_add tendsto_const_nhds
  apply tendsto_atBot_mono' l _ hlim
  filter_upwards [hbound] with a ha
  rw [← Finset.add_sum_erase _ _ (mem_univ j)]
  exact add_le_add_left (Finset.sum_le_sum (fun i _ => ha i)) _

private theorem sum_tendsto_atTop_of_coordinate
    (f : A → ι → ℝ) (j : ι) (c : ι → ℝ)
    (hbound : ∀ᶠ a in l, ∀ i, c i ≤ f a i)
    (hj : Tendsto (fun a => f a j) l atTop) :
    Tendsto (fun a => ∑ i, f a i) l atTop := by
  classical
  have hlim : Tendsto (fun a => f a j + ∑ i ∈ univ.erase j, c i) l atTop :=
    hj.atTop_add tendsto_const_nhds
  apply tendsto_atTop_mono' l _ hlim
  filter_upwards [hbound] with a ha
  rw [← Finset.add_sum_erase _ _ (mem_univ j)]
  exact add_le_add_left (Finset.sum_le_sum (fun i _ => ha i)) _

/-- At a zero boundary coordinate, with no one coordinates, the actual
inverse-normal sum diverges negatively along every approach through the open cube. -/
theorem quantile_sum_tendsto_atBot_of_zero
    (x : ι → ℝ) (f : A → ι → ℝ) (hf : Tendsto f l (𝓝 x))
    (hmem : ∀ᶠ a in l, ∀ i, f a i ∈ Ioo (0 : ℝ) 1)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (j : ι) (hj : x j = 0) :
    Tendsto (fun a => ∑ i, normalQuantile (f a i)) l atBot := by
  have hcoord (i : ι) : Tendsto (fun a => f a i) l (𝓝 (x i)) :=
    ((continuous_apply i).tendsto x).comp hf
  have hzero : Tendsto (fun a => f a j) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [hj] using hcoord j, hmem.mono (fun _ ha => (ha j).1)⟩
  let c : ι → ℝ := fun i => normalQuantile ((x i + 1) / 2)
  have hboundi : ∀ i, ∀ᶠ a in l, normalQuantile (f a i) ≤ c i := by
    intro i
    have hci : (x i + 1) / 2 ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    filter_upwards [hmem,
      (hcoord i).eventually_le_const (by linarith [(hx i).2] : x i < (x i + 1) / 2)]
      with a ha hle
    exact normalQuantile_strictMonoOn.monotoneOn (ha i) hci hle
  exact sum_tendsto_atBot_of_coordinate (fun a i => normalQuantile (f a i)) j c
    (Filter.eventually_all.mpr hboundi) (normalQuantile_tendsto_zero_right.comp hzero)

/-- At a one boundary coordinate, with no zero coordinates, the actual
inverse-normal sum diverges positively along every approach through the open cube. -/
theorem quantile_sum_tendsto_atTop_of_one
    (x : ι → ℝ) (f : A → ι → ℝ) (hf : Tendsto f l (𝓝 x))
    (hmem : ∀ᶠ a in l, ∀ i, f a i ∈ Ioo (0 : ℝ) 1)
    (hx : ∀ i, 0 < x i ∧ x i ≤ 1) (j : ι) (hj : x j = 1) :
    Tendsto (fun a => ∑ i, normalQuantile (f a i)) l atTop := by
  have hcoord (i : ι) : Tendsto (fun a => f a i) l (𝓝 (x i)) :=
    ((continuous_apply i).tendsto x).comp hf
  have hone : Tendsto (fun a => f a j) l (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [hj] using hcoord j, hmem.mono (fun _ ha => (ha j).2)⟩
  let c : ι → ℝ := fun i => normalQuantile (x i / 2)
  have hboundi : ∀ i, ∀ᶠ a in l, c i ≤ normalQuantile (f a i) := by
    intro i
    have hci : x i / 2 ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    filter_upwards [hmem,
      (hcoord i).eventually_const_le (by linarith [(hx i).1] : x i / 2 < x i)]
      with a ha hle
    exact normalQuantile_strictMonoOn.monotoneOn hci (ha i) hle
  exact sum_tendsto_atTop_of_coordinate (fun a i => normalQuantile (f a i)) j c
    (Filter.eventually_all.mpr hboundi) (normalQuantile_tendsto_one_left.comp hone)

end FiniteCoordinateLimits

section CubeShift

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def cubeShiftMin (x : ι → ℝ) : ℝ := univ.inf' univ_nonempty x

def cubeShiftMax (x : ι → ℝ) : ℝ := univ.sup' univ_nonempty x

theorem cubeShiftMin_le (x : ι → ℝ) (i : ι) : cubeShiftMin x ≤ x i :=
  Finset.inf'_le x (mem_univ i)

theorem le_cubeShiftMax (x : ι → ℝ) (i : ι) : x i ≤ cubeShiftMax x :=
  Finset.le_sup' x (mem_univ i)

theorem cubeShiftMin_attained (x : ι → ℝ) : ∃ j, cubeShiftMin x = x j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' univ_nonempty x
  exact ⟨j, hj⟩

theorem cubeShiftMax_attained (x : ι → ℝ) : ∃ j, cubeShiftMax x = x j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' univ_nonempty x
  exact ⟨j, hj⟩

def cubeShiftQuantileSum (x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, normalQuantile (x i + t)

theorem cubeShift_coordinate_mem (x : ι → ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-cubeShiftMin x) (1 - cubeShiftMax x)) (i : ι) :
    x i + t ∈ Ioo (0 : ℝ) 1 := by
  have hlo := cubeShiftMin_le x i
  have hhi := le_cubeShiftMax x i
  constructor <;> linarith [ht.1, ht.2]

theorem cubeShiftQuantileSum_continuousOn (x : ι → ℝ) :
    ContinuousOn (cubeShiftQuantileSum x)
      (Ioo (-cubeShiftMin x) (1 - cubeShiftMax x)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  change Tendsto (fun s => ∑ i, normalQuantile (x i + s)) (𝓝 t)
    (𝓝 (∑ i, normalQuantile (x i + t)))
  apply tendsto_finset_sum
  intro i _
  exact (normalQuantile_continuousAt (cubeShift_coordinate_mem x ht i)).tendsto.comp
    (tendsto_const_nhds.add tendsto_id)

theorem cubeShiftQuantileSum_strictMonoOn (x : ι → ℝ) :
    StrictMonoOn (cubeShiftQuantileSum x)
      (Ioo (-cubeShiftMin x) (1 - cubeShiftMax x)) := by
  intro t ht s hs hts
  apply Finset.sum_lt_sum_of_nonempty univ_nonempty
  intro i _
  exact normalQuantile_strictMonoOn (cubeShift_coordinate_mem x ht i)
    (cubeShift_coordinate_mem x hs i) (by linarith)

theorem cubeShiftQuantileSum_tendsto_lower (x : ι → ℝ)
    (hspan : cubeShiftMax x - cubeShiftMin x < 1) :
    Tendsto (cubeShiftQuantileSum x) (𝓝[>] (-cubeShiftMin x)) atBot := by
  have hab : -cubeShiftMin x < 1 - cubeShiftMax x := by linarith
  have hmem : ∀ᶠ t in 𝓝[>] (-cubeShiftMin x),
      ∀ i, x i + t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds] with t htlo hthi
    exact cubeShift_coordinate_mem x ⟨htlo, hthi⟩
  have hf : Tendsto (fun t i => x i + t) (𝓝[>] (-cubeShiftMin x))
      (𝓝 (fun i => x i + -cubeShiftMin x)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨j, hj⟩ := cubeShiftMin_attained x
  exact quantile_sum_tendsto_atBot_of_zero (fun i => x i + -cubeShiftMin x)
    (fun t i => x i + t) hf hmem
    (fun i => ⟨by linarith [cubeShiftMin_le x i],
      by linarith [le_cubeShiftMax x i]⟩) j (by linarith)

theorem cubeShiftQuantileSum_tendsto_upper (x : ι → ℝ)
    (hspan : cubeShiftMax x - cubeShiftMin x < 1) :
    Tendsto (cubeShiftQuantileSum x) (𝓝[<] (1 - cubeShiftMax x)) atTop := by
  have hab : -cubeShiftMin x < 1 - cubeShiftMax x := by linarith
  have hmem : ∀ᶠ t in 𝓝[<] (1 - cubeShiftMax x),
      ∀ i, x i + t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds] with t hthi htlo
    exact cubeShift_coordinate_mem x ⟨htlo, hthi⟩
  have hf : Tendsto (fun t i => x i + t) (𝓝[<] (1 - cubeShiftMax x))
      (𝓝 (fun i => x i + (1 - cubeShiftMax x))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨j, hj⟩ := cubeShiftMax_attained x
  exact quantile_sum_tendsto_atTop_of_one (fun i => x i + (1 - cubeShiftMax x))
    (fun t i => x i + t) hf hmem
    (fun i => ⟨by linarith [cubeShiftMin_le x i],
      by linarith [le_cubeShiftMax x i]⟩) j (by linarith)

/-- The manuscript's common cube-coordinate shift reaches the actual
inverse-normal surface, by the two endpoint limits and the IVT. -/
theorem exists_cubeShift_sum_zero (x : ι → ℝ)
    (hspan : cubeShiftMax x - cubeShiftMin x < 1) :
    ∃ t ∈ Ioo (-cubeShiftMin x) (1 - cubeShiftMax x), cubeShiftQuantileSum x t = 0 := by
  have hab : -cubeShiftMin x < 1 - cubeShiftMax x := by linarith
  have hl : 𝓝[>] (-cubeShiftMin x) ≤
      𝓟 (Ioo (-cubeShiftMin x) (1 - cubeShiftMax x)) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds] with t htl htr
    exact ⟨htl, htr⟩
  have hr : 𝓝[<] (1 - cubeShiftMax x) ≤
      𝓟 (Ioo (-cubeShiftMin x) (1 - cubeShiftMax x)) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds] with t htr htl
    exact ⟨htl, htr⟩
  exact isPreconnected_Ioo.intermediate_value_Iii hl hr
    (cubeShiftQuantileSum_continuousOn x) (cubeShiftQuantileSum_tendsto_lower x hspan)
    (cubeShiftQuantileSum_tendsto_upper x hspan) (mem_univ (0 : ℝ))

theorem exists_cubeShift_surface_point (x : ι → ℝ)
    (hspan : cubeShiftMax x - cubeShiftMin x < 1) :
    ∃ t : ℝ, (fun i => x i + t) ∈ normalQuantileSurface ι := by
  obtain ⟨t, ht, hsum⟩ := exists_cubeShift_sum_zero x hspan
  exact ⟨t, (cubeShift_coordinate_mem x ht), hsum⟩

omit [Nonempty ι] in
/-- The written closure inclusion: at a boundary point without both endpoint
values the inverse-normal sum diverges with one sign; at an interior point
continuity preserves its zero value. No comparable witness is used here. -/
theorem normalQuantile_surface_closure_subset_written :
    closure (normalQuantileSurface ι) ⊆ normalQuantileSurface ι ∪
      {x : ι → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        (∃ i, x i = 0) ∧ (∃ i, x i = 1)} := by
  intro x hx
  have hclosed : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    exact (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  have hsub : normalQuantileSurface ι ⊆
      {x : ι → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    intro y hy i
    exact ⟨(hy.1 i).1.le, (hy.1 i).2.le⟩
  have hcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := closure_minimal hsub hclosed hx
  let l := 𝓝[normalQuantileSurface ι] x
  haveI : NeBot l := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hf : Tendsto (fun y : ι → ℝ => y) l (𝓝 x) := nhdsWithin_le_nhds
  have hself : ∀ᶠ y in l, y ∈ normalQuantileSurface ι := self_mem_nhdsWithin
  have hmem : ∀ᶠ y in l, ∀ i, y i ∈ Ioo (0 : ℝ) 1 :=
    hself.mono (fun _ hy => hy.1)
  have hz : ∀ᶠ y in l, (∑ i, normalQuantile (y i)) = 0 :=
    hself.mono (fun _ hy => hy.2)
  have hzeroLim : Tendsto (fun y : ι → ℝ => ∑ i, normalQuantile (y i)) l (𝓝 0) :=
    tendsto_const_nhds.congr' (hz.mono (fun _ hy => hy.symm))
  by_cases hzero : ∃ i, x i = 0
  · by_cases hone : ∃ i, x i = 1
    · exact Or.inr ⟨hcube, hzero, hone⟩
    · obtain ⟨j, hj⟩ := hzero
      have hupper : ∀ i, x i < 1 := by
        intro i
        exact lt_of_le_of_ne (hcube i).2 (fun heq => hone ⟨i, heq⟩)
      have hdiv := quantile_sum_tendsto_atBot_of_zero x (fun y : ι → ℝ => y) hf hmem
        (fun i => ⟨(hcube i).1, hupper i⟩) j hj
      exact (not_tendsto_nhds_of_tendsto_atBot hdiv 0 hzeroLim).elim
  · have hlower : ∀ i, 0 < x i := by
      intro i
      exact lt_of_le_of_ne (hcube i).1 (fun heq => hzero ⟨i, heq.symm⟩)
    by_cases hone : ∃ i, x i = 1
    · obtain ⟨j, hj⟩ := hone
      have hdiv := quantile_sum_tendsto_atTop_of_one x (fun y : ι → ℝ => y) hf hmem
        (fun i => ⟨hlower i, (hcube i).2⟩) j hj
      exact (not_tendsto_nhds_of_tendsto_atTop hdiv 0 hzeroLim).elim
    · have hint : ∀ i, x i ∈ Ioo (0 : ℝ) 1 := by
        intro i
        exact ⟨hlower i, lt_of_le_of_ne (hcube i).2 (fun heq => hone ⟨i, heq⟩)⟩
      have hcont : ContinuousAt (fun y : ι → ℝ => ∑ i, normalQuantile (y i)) x := by
        apply tendsto_finset_sum
        intro i _
        exact (normalQuantile_continuousAt (hint i)).tendsto.comp
          ((continuous_apply i).tendsto x)
      have hsum : (∑ i, normalQuantile (x i)) = 0 :=
        tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hzeroLim
      exact Or.inl ⟨hint, hsum⟩

/-- The complete written closure formula. The reverse inclusion reuses the
explicit zero/one-coordinate approximation already present in the manuscript. -/
theorem normalQuantile_surface_closure_written :
    closure (normalQuantileSurface ι) = normalQuantileSurface ι ∪
      {x : ι → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        (∃ i, x i = 0) ∧ (∃ i, x i = 1)} := by
  apply subset_antisymm normalQuantile_surface_closure_subset_written
  intro x hx
  rcases hx with hx | ⟨hcube, hzero, hone⟩
  · exact subset_closure hx
  · simpa only [normalCDF_surface_eq_quantileSurface] using
      mixed_boundary_mem_normalCDF_surface_closure x hcube hzero hone

theorem cubeShift_span_lt_one_of_outside_closure (x : ι → ℝ)
    (hcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hout : x ∉ closure (normalQuantileSurface ι)) :
    cubeShiftMax x - cubeShiftMin x < 1 := by
  obtain ⟨j, hj⟩ := cubeShiftMin_attained x
  obtain ⟨k, hk⟩ := cubeShiftMax_attained x
  have hlo : 0 ≤ cubeShiftMin x := by rw [hj]; exact (hcube j).1
  have hhi : cubeShiftMax x ≤ 1 := by rw [hk]; exact (hcube k).2
  by_contra h
  have hmin : cubeShiftMin x = 0 := by linarith
  have hmax : cubeShiftMax x = 1 := by linarith
  apply hout
  rw [normalQuantile_surface_closure_written]
  exact Or.inr ⟨hcube, ⟨j, hj.symm.trans hmin⟩, ⟨k, hk.symm.trans hmax⟩⟩

/-- The actual nonzero scalar cube shift of the written proof, with the
resulting strict comparison in every coordinate. -/
theorem exists_nonzero_cubeShift_comparable (x : ι → ℝ)
    (hcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hout : x ∉ closure (normalQuantileSurface ι)) :
    ∃ t : ℝ, t ≠ 0 ∧ (fun i => x i + t) ∈ normalQuantileSurface ι ∧
      (StrictBelow x (fun i => x i + t) ∨ StrictBelow (fun i => x i + t) x) := by
  obtain ⟨t, ht⟩ := exists_cubeShift_surface_point x
    (cubeShift_span_lt_one_of_outside_closure x hcube hout)
  have ht0 : t ≠ 0 := by
    intro heq
    apply hout
    apply subset_closure
    simpa only [heq, add_zero] using ht
  refine ⟨t, ht0, ht, ?_⟩
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · right
    intro i
    change x i + t < x i
    linarith
  · left
    intro i
    change x i < x i + t
    linarith

theorem normalQuantile_cube_outside_closure_exists_comparable_cubeShift
    (x : ι → ℝ) (hcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hout : x ∉ closure (normalQuantileSurface ι)) :
    ∃ y ∈ normalQuantileSurface ι, StrictBelow x y ∨ StrictBelow y x := by
  obtain ⟨t, _, hsurface, hcomp⟩ := exists_nonzero_cubeShift_comparable x hcube hout
  exact ⟨fun i => x i + t, hsurface, hcomp⟩

/-- Full source support lemma using the written endpoint/IVT proof route.
The support identity itself is the existing continuous Gaussian pushforward
identity; neither the old centered witness nor its closure argument is used. -/
theorem limitingAntichainMeasure_support_cubeShift_source (hd : 2 ≤ Fintype.card ι) :
    (limitingAntichainMeasure ι).support = closure (normalQuantileSurface ι) ∧
    closure (normalQuantileSurface ι) = normalQuantileSurface ι ∪
      {x : ι → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        (∃ i, x i = 0) ∧ (∃ i, x i = 1)} ∧
    (∀ x : ι → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      x ∉ closure (normalQuantileSurface ι) →
      ∃ y ∈ normalQuantileSurface ι, StrictBelow x y ∨ StrictBelow y x) := by
  refine ⟨?_, normalQuantile_surface_closure_written,
    normalQuantile_cube_outside_closure_exists_comparable_cubeShift⟩
  simpa only [normalCDF_surface_eq_quantileSurface] using limitingAntichainMeasure_support hd

end CubeShift

end Antichain
