import Antichain.GaussianCDF
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Topological closure of the actual normal-coordinate antichain surface. -/

namespace Antichain

open Set Filter Finset
open scoped Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem isOpen_strictBelow_left (y : ι → ℝ) : IsOpen {x | StrictBelow x y} := by
  simp only [StrictBelow, setOf_forall]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i) continuous_const)

omit [Nonempty ι] in
theorem isOpen_strictBelow_right (y : ι → ℝ) : IsOpen {x | StrictBelow y x} := by
  simp only [StrictBelow, setOf_forall]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))

theorem closure_surface_not_strictly_comparable (Q : ℝ → ℝ) (hQ : StrictMono Q)
    {x y : ι → ℝ} (hx : x ∈ closure (coordinateImageSurface Q))
    (hy : y ∈ coordinateImageSurface Q) : ¬ StrictBelow x y ∧ ¬ StrictBelow y x := by
  constructor
  · have hc : IsClosed {x | ¬ StrictBelow x y} := (isOpen_strictBelow_left y).isClosed_compl
    exact closure_minimal (fun z hz => coordinateImageSurface_not_strictBelow Q hQ hz hy) hc hx
  · have hc : IsClosed {x | ¬ StrictBelow y x} := (isOpen_strictBelow_right y).isClosed_compl
    exact closure_minimal (fun z hz => coordinateImageSurface_not_strictBelow Q hQ hy hz) hc hx

theorem normalCDF_surface_closure_subset_candidate :
    closure (coordinateImageSurface (ι := ι) normalCDF) ⊆ candidateClosedSurface normalCDF := by
  have hclosed : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    exact (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  have hcube : coordinateImageSurface (ι := ι) normalCDF ⊆
      {x : ι → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    rintro x ⟨g, _, rfl⟩ i
    exact ⟨(normalCDF_mem_Ioo (g i)).1.le, (normalCDF_mem_Ioo (g i)).2.le⟩
  intro x hx
  by_contra hout
  obtain ⟨y, hy, hcomp⟩ := normalCDF_cube_outside_candidate_exists_comparable x
    (closure_minimal hcube hclosed hx) hout
  have hn := closure_surface_not_strictly_comparable normalCDF normalCDF_strictMono hx hy
  exact hcomp.elim hn.1 hn.2

omit [Nonempty ι] in
/-- Every mixed zero/one boundary point is approached by actual zero-sum Gaussian
coordinates; the other coordinates are held fixed. -/
theorem mixed_boundary_mem_normalCDF_surface_closure (x : ι → ℝ)
    (hcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hzero : ∃ i, x i = 0) (hone : ∃ i, x i = 1) :
    x ∈ closure (coordinateImageSurface normalCDF) := by
  classical
  let Z : Finset ι := Finset.univ.filter (fun i => x i = 0)
  let O : Finset ι := Finset.univ.filter (fun i => x i = 1)
  have hZ : Z.Nonempty := by
    obtain ⟨i, hi⟩ := hzero
    exact ⟨i, by simp [Z, hi]⟩
  have hO : O.Nonempty := by
    obtain ⟨i, hi⟩ := hone
    exact ⟨i, by simp [O, hi]⟩
  have hZpos : (0 : ℝ) < Z.card := by exact_mod_cast Finset.card_pos.mpr hZ
  have hOpos : (0 : ℝ) < O.card := by exact_mod_cast Finset.card_pos.mpr hO
  have hpre : ∀ i, ∃ t : ℝ, (x i ≠ 0 ∧ x i ≠ 1) → normalCDF t = x i := by
    intro i
    by_cases hi : x i ≠ 0 ∧ x i ≠ 1
    · obtain ⟨t, ht⟩ := normalCDF_onto_Ioo (x i)
        ⟨lt_of_le_of_ne (hcube i).1 (Ne.symm hi.1), lt_of_le_of_ne (hcube i).2 hi.2⟩
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => False.elim (hi h)⟩
  choose g hg using hpre
  let middle : ι → ℝ := fun i => if x i = 0 ∨ x i = 1 then 0 else g i
  let C : ℝ := ∑ i, middle i
  let f : ℝ → ι → ℝ := fun t i =>
    (if x i = 0 then -t / (Z.card : ℝ) else 0) +
    (if x i = 1 then (t - C) / (O.card : ℝ) else 0) + middle i
  have hsum : ∀ t, ∑ i, f t i = 0 := by
    intro t
    have hzs : (∑ i, if x i = 0 then -t / (Z.card : ℝ) else 0) = -t := by
      rw [← Finset.sum_filter]
      simp only [Z, Finset.sum_const, nsmul_eq_mul]
      exact mul_div_cancel₀ _ (ne_of_gt hZpos)
    have hos : (∑ i, if x i = 1 then (t - C) / (O.card : ℝ) else 0) = t - C := by
      rw [← Finset.sum_filter]
      simp only [O, Finset.sum_const, nsmul_eq_mul]
      exact mul_div_cancel₀ _ (ne_of_gt hOpos)
    simp only [f, Finset.sum_add_distrib, hzs, hos]
    dsimp [C]
    ring
  have hlim : Tendsto (fun t i => normalCDF (f t i)) atTop (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hi0 : x i = 0
    · have hi1 : x i ≠ 1 := by simp [hi0]
      have ht : Tendsto (fun t : ℝ => -t / (Z.card : ℝ)) atTop atBot := by
        simpa only [neg_div] using
          tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const hZpos)
      have h := normalCDF_tendsto_atBot.comp ht
      simpa [f, middle, hi0, hi1] using h
    · by_cases hi1 : x i = 1
      · have ht : Tendsto (fun t : ℝ => (t - C) / (O.card : ℝ)) atTop atTop := by
          have hsub : Tendsto (fun t : ℝ => t - C) atTop atTop := by
            simpa only [sub_eq_add_neg] using
              tendsto_atTop_add_const_right atTop (-C) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
          exact hsub.atTop_div_const hOpos
        have h := normalCDF_tendsto_atTop.comp ht
        simpa [f, middle, hi0, hi1] using h
      · have hgi := hg i ⟨hi0, hi1⟩
        simp [f, middle, hi0, hi1, hgi]
  apply mem_closure_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun t => ⟨f t, hsum t, rfl⟩)

/-- The complete topological closure formula in Lemma 2.2, for the actual normal CDF. -/
theorem normalCDF_surface_closure :
    closure (coordinateImageSurface (ι := ι) normalCDF) = candidateClosedSurface normalCDF := by
  apply subset_antisymm normalCDF_surface_closure_subset_candidate
  intro x hx
  rcases hx with hsurface | ⟨hcube, hzero, hone⟩
  · exact subset_closure hsurface
  · exact mixed_boundary_mem_normalCDF_surface_closure x hcube hzero hone

/-- The comparable-witness assertion, now expressed using the proved actual closure. -/
theorem normalCDF_cube_outside_closure_exists_comparable (x : ι → ℝ)
    (hcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hout : x ∉ closure (coordinateImageSurface normalCDF)) :
    ∃ y ∈ coordinateImageSurface normalCDF, StrictBelow x y ∨ StrictBelow y x := by
  rw [normalCDF_surface_closure] at hout
  exact normalCDF_cube_outside_candidate_exists_comparable x hcube hout

end Antichain
