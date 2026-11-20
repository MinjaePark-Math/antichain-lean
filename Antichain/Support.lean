import Antichain.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
Deterministic supporting geometry for Lemma 2.2.

The zero-sum hyperplane is a strict-coordinate antichain. Every point off
that hyperplane is strictly comparable with its centered projection, and
strictly increasing coordinate maps transport this witness to the image
surface. The final results cover boundary points of the cube as well.

This module does not identify Gaussian probability-measure support or prove
the topological closure formula. It uses an explicitly supplied coordinate
map, with monotonicity and its actual range recorded in the hypotheses.
-/

namespace Antichain

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Two zero-sum vectors cannot be strictly ordered in every coordinate. -/
theorem zeroSum_not_strictBelow (u v : ι → ℝ)
    (hu : ∑ i, u i = 0) (hv : ∑ i, v i = 0) :
    ¬ StrictBelow u v := by
  intro h
  have hs := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset ι)) Finset.univ_nonempty (fun i _ => h i)
  rw [hu, hv] at hs
  exact (lt_irrefl 0) hs

/-- Every family on the actual zero-sum hyperplane is an antichain. -/
theorem zeroSum_family_isAntichain {κ : Type*} (x : κ → ι → ℝ)
    (hx : ∀ j, ∑ i, x j i = 0) : IsAntichain x := by
  intro j k _
  exact zeroSum_not_strictBelow (x j) (x k) (hx j) (hx k)

/-- Subtracting the coordinate average gives a strictly comparable floor
point whenever the original point lies off the zero-sum hyperplane. -/
theorem offFloor_exists_strictly_comparable (x : ι → ℝ)
    (hx : ∑ i, x i ≠ 0) :
    ∃ y : ι → ℝ, (∑ i, y i = 0) ∧
      (StrictBelow x y ∨ StrictBelow y x) := by
  let m : ℝ := (∑ i, x i) / (Fintype.card ι : ℝ)
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm : m ≠ 0 := div_ne_zero hx (ne_of_gt hc)
  refine ⟨fun i => x i - m, sum_sub_mean_eq_zero x, ?_⟩
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · left
    intro i
    linarith
  · right
    intro i
    linarith

/-- Image of the zero-sum hyperplane under a scalar coordinate map. -/
def coordinateImageSurface (Q : ℝ → ℝ) : Set (ι → ℝ) :=
  {x | ∃ g : ι → ℝ, (∑ i, g i = 0) ∧ x = fun i => Q (g i)}

/-- Increasing coordinate maps preserve the antichain property of the floor. -/
theorem coordinateImageSurface_not_strictBelow (Q : ℝ → ℝ) (hQ : StrictMono Q)
    {x y : ι → ℝ} (hx : x ∈ coordinateImageSurface Q)
    (hy : y ∈ coordinateImageSurface Q) : ¬ StrictBelow x y := by
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  rw [strictBelow_coordinatewise_iff hQ]
  exact zeroSum_not_strictBelow u v hu hv

/-- Every coordinate-range point outside the image surface has a strictly
comparable point on the surface. No surface-comparability hypothesis is used. -/
theorem coordinateImageSurface_exists_comparable (Q : ℝ → ℝ) (hQ : StrictMono Q)
    (x : ι → ℝ) (hpre : ∀ i, ∃ t : ℝ, Q t = x i)
    (hx : x ∉ coordinateImageSurface Q) :
    ∃ y ∈ coordinateImageSurface Q, StrictBelow x y ∨ StrictBelow y x := by
  choose g hg using hpre
  have hsum : ∑ i, g i ≠ 0 := by
    intro hzero
    exact hx ⟨g, hzero, funext (fun i => (hg i).symm)⟩
  obtain ⟨f, hf, hcomp⟩ := offFloor_exists_strictly_comparable g hsum
  refine ⟨fun i => Q (f i), ⟨f, hf, rfl⟩, ?_⟩
  rcases hcomp with hlt | hlt
  · left
    intro i
    rw [← hg i]
    exact hQ (hlt i)
  · right
    intro i
    rw [← hg i]
    exact hQ (hlt i)

omit [Nonempty ι] in
/-- A zero boundary coordinate can absorb the zero-sum constraint. If all
other coordinates are below one, a point on the surface lies strictly above. -/
theorem cube_zero_boundary_exists_surface_above (Q : ℝ → ℝ)
    (hpos : ∀ t, 0 < Q t)
    (honto : ∀ a : ℝ, a ∈ Set.Ioo 0 1 → ∃ t, Q t = a)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (j : ι) (hj : x j = 0) :
    ∃ y ∈ coordinateImageSurface Q, StrictBelow x y := by
  classical
  have hchoices : ∀ i, ∃ t, x i < Q t := by
    intro i
    obtain ⟨t, ht⟩ := honto ((x i + 1) / 2) ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    exact ⟨t, by rw [ht]; linarith [(hx i).2]⟩
  choose g hg using hchoices
  let f : ι → ℝ := fun i => g i - if i = j then ∑ k, g k else 0
  have hf : ∑ i, f i = 0 := by
    simp [f, Finset.sum_sub_distrib]
  refine ⟨fun i => Q (f i), ⟨f, hf, rfl⟩, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    rw [hj]
    exact hpos (f j)
  · simpa [f, hij] using hg i

omit [Nonempty ι] in
/-- A one boundary coordinate similarly absorbs the zero-sum constraint,
giving a surface point strictly below when no coordinate is zero. -/
theorem cube_one_boundary_exists_surface_below (Q : ℝ → ℝ)
    (hlt : ∀ t, Q t < 1)
    (honto : ∀ a : ℝ, a ∈ Set.Ioo 0 1 → ∃ t, Q t = a)
    (x : ι → ℝ) (hx : ∀ i, 0 < x i ∧ x i ≤ 1)
    (j : ι) (hj : x j = 1) :
    ∃ y ∈ coordinateImageSurface Q, StrictBelow y x := by
  classical
  have hchoices : ∀ i, ∃ t, Q t < x i := by
    intro i
    obtain ⟨t, ht⟩ := honto (x i / 2) ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    exact ⟨t, by rw [ht]; linarith [(hx i).1]⟩
  choose g hg using hchoices
  let f : ι → ℝ := fun i => g i - if i = j then ∑ k, g k else 0
  have hf : ∑ i, f i = 0 := by
    simp [f, Finset.sum_sub_distrib]
  refine ⟨fun i => Q (f i), ⟨f, hf, rfl⟩, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    rw [hj]
    exact hlt (f j)
  · simpa [f, hij] using hg i

/-- The set appearing in the paper's closure formula, defined here without
assuming or asserting that it is the topological closure or measure support. -/
def candidateClosedSurface (Q : ℝ → ℝ) : Set (ι → ℝ) :=
  coordinateImageSurface Q ∪
    {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∃ i, x i = 0) ∧ (∃ i, x i = 1)}

/-- The full deterministic comparable-witness conclusion on the closed cube.
Range and strict monotonicity are explicit properties to instantiate for Phi.
The proof does not assume the closure formula or a comparable-witness axiom. -/
theorem cube_outside_candidateClosedSurface_exists_comparable
    (Q : ℝ → ℝ) (hQ : StrictMono Q)
    (hrange : ∀ t, Q t ∈ Set.Ioo 0 1)
    (honto : ∀ a : ℝ, a ∈ Set.Ioo 0 1 → ∃ t, Q t = a)
    (x : ι → ℝ) (hcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hx : x ∉ candidateClosedSurface Q) :
    ∃ y ∈ coordinateImageSurface Q, StrictBelow x y ∨ StrictBelow y x := by
  have hsurface : x ∉ coordinateImageSurface Q := fun h => hx (Or.inl h)
  by_cases hzero : ∃ j, x j = 0
  · obtain ⟨j, hj⟩ := hzero
    have hnoone : ¬ ∃ i, x i = 1 := fun hone => hx (Or.inr ⟨hcube, ⟨j, hj⟩, hone⟩)
    have hupper : ∀ i, x i < 1 := by
      intro i
      exact lt_of_le_of_ne (hcube i).2 (fun heq => hnoone ⟨i, heq⟩)
    obtain ⟨y, hy, hcomp⟩ := cube_zero_boundary_exists_surface_above Q
      (fun t => (hrange t).1) honto x (fun i => ⟨(hcube i).1, hupper i⟩) j hj
    exact ⟨y, hy, Or.inl hcomp⟩
  · have hlower : ∀ i, 0 < x i := by
      intro i
      exact lt_of_le_of_ne (hcube i).1 (fun heq => hzero ⟨i, heq.symm⟩)
    by_cases hone : ∃ j, x j = 1
    · obtain ⟨j, hj⟩ := hone
      obtain ⟨y, hy, hcomp⟩ := cube_one_boundary_exists_surface_below Q
        (fun t => (hrange t).2) honto x (fun i => ⟨hlower i, (hcube i).2⟩) j hj
      exact ⟨y, hy, Or.inr hcomp⟩
    · apply coordinateImageSurface_exists_comparable Q hQ x _ hsurface
      intro i
      apply honto (x i)
      exact ⟨hlower i, lt_of_le_of_ne (hcube i).2 (fun heq => hone ⟨i, heq⟩)⟩

end Antichain
