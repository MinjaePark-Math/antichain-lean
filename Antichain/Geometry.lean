import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Antichain.Basic

/-!
Finite-coordinate directed height gauge used in Section 3 of the paper.
The parameter `s` is the paper's `√d`; keeping it explicit makes clear
that the order equivalence needs only positivity, not a Gaussian model.
-/

namespace Antichain

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `maxᵢ (-s uᵢ)`, hence `-s minᵢ uᵢ` when `s ≥ 0`. -/
noncomputable def heightGauge (s : ℝ) (u : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => -s * u i)

theorem neg_mul_le_heightGauge (s : ℝ) (u : ι → ℝ) (i : ι) :
    -s * u i ≤ heightGauge s u := by
  unfold heightGauge
  exact Finset.le_sup' (f := fun i : ι => -s * u i) (Finset.mem_univ i)

theorem heightGauge_le_iff (s : ℝ) (u : ι → ℝ) (a : ℝ) :
    heightGauge s u ≤ a ↔ ∀ i, -s * u i ≤ a := by
  simp [heightGauge, Finset.sup'_le_iff]

theorem heightGauge_lt_iff (s : ℝ) (u : ι → ℝ) (a : ℝ) :
    heightGauge s u < a ↔ ∀ i, -s * u i < a := by
  simp [heightGauge, Finset.sup'_lt_iff]

/-- The max representation is exactly the manuscript's `-s minᵢ uᵢ`. -/
theorem heightGauge_eq_neg_mul_min (s : ℝ) (hs : 0 ≤ s) (u : ι → ℝ) :
    heightGauge s u = -s * Finset.univ.inf' Finset.univ_nonempty u := by
  apply le_antisymm
  · apply (heightGauge_le_iff _ _ _).mpr
    intro i
    exact mul_le_mul_of_nonpos_left (Finset.inf'_le u (Finset.mem_univ i))
      (neg_nonpos.mpr hs)
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty u
    rw [hi]
    exact neg_mul_le_heightGauge s u i

@[simp] theorem heightGauge_zero (s : ℝ) :
    heightGauge s (fun _ : ι => 0) = 0 := by
  simp [heightGauge]

/-- The exact comparison underlying Proposition 3.1, including its strict boundary. -/
theorem all_coordinates_lt_iff_heightGauge_lt (s : ℝ) (hs : 0 < s)
    (f g : ι → ℝ) (h k : ℝ) :
    (∀ i, g i + k / s < f i + h / s) ↔
      heightGauge s (fun i => f i - g i) < h - k := by
  rw [heightGauge_lt_iff]
  constructor
  · intro hlt i
    have hi := mul_lt_mul_of_pos_right (hlt i) hs
    simp only [add_mul, div_mul_cancel₀ _ hs.ne'] at hi
    nlinarith
  · intro hlt i
    apply (mul_lt_mul_iff_left₀ hs).mp
    simp only [add_mul, div_mul_cancel₀ _ hs.ne']
    have hi := hlt i
    nlinarith

/-- Proposition 3.1 for an arbitrary indexed family (all ordered pairs).
At `s = √d` these are exactly the floor/height points of the manuscript.
No zero-sum assumption is needed for this equivalence. -/
theorem antichain_iff_height_constraints {κ : Type*} (s : ℝ) (hs : 0 < s)
    (f : κ → ι → ℝ) (h : κ → ℝ) :
    (∀ j k, ¬ ∀ i, f k i + h k / s < f j i + h j / s) ↔
      ∀ j k, h j - h k ≤ heightGauge s (fun i => f j i - f k i) := by
  simp only [all_coordinates_lt_iff_heightGauge_lt s hs, not_lt]

/-- Subadditivity, the first assertion of (3.2). -/
theorem heightGauge_add_le (s : ℝ) (u v : ι → ℝ) :
    heightGauge s (fun i => u i + v i) ≤ heightGauge s u + heightGauge s v := by
  apply (heightGauge_le_iff _ _ _).mpr
  intro i
  have hu := neg_mul_le_heightGauge s u i
  have hv := neg_mul_le_heightGauge s v i
  nlinarith

/-- Positive homogeneity, the second assertion of (3.2). -/
theorem heightGauge_smul (s t : ℝ) (ht : 0 ≤ t) (u : ι → ℝ) :
    heightGauge s (fun i => t * u i) = t * heightGauge s u := by
  apply le_antisymm
  · apply (heightGauge_le_iff _ _ _).mpr
    intro i
    have hi := mul_le_mul_of_nonneg_left (neg_mul_le_heightGauge s u i) ht
    nlinarith
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : ι => -s * u i)
    have hb := neg_mul_le_heightGauge s (fun i => t * u i) i
    change heightGauge s u = -s * u i at hi
    rw [hi]
    nlinarith

/-- Coordinate permutation invariance in Lemma 3.2. -/
theorem heightGauge_equiv (s : ℝ) (u : ι → ℝ) (e : ι ≃ ι) :
    heightGauge s (fun i => u (e i)) = heightGauge s u := by
  apply le_antisymm
  · apply (heightGauge_le_iff _ _ _).mpr
    intro i
    exact neg_mul_le_heightGauge s u (e i)
  · apply (heightGauge_le_iff _ _ _).mpr
    intro i
    simpa using neg_mul_le_heightGauge s (fun i => u (e i)) (e.symm i)

/-- On the floor hyperplane the directed gauge is nonnegative. -/
theorem heightGauge_nonneg (s : ℝ) (u : ι → ℝ)
    (hu : ∑ i, u i = 0) : 0 ≤ heightGauge s u := by
  by_contra! hn
  have hall : ∀ i, 0 < s * u i := by
    intro i
    have hi := (neg_mul_le_heightGauge s u i).trans_lt hn
    nlinarith
  have hsum : 0 < ∑ i, s * u i :=
    Finset.sum_pos (fun i _ => hall i) Finset.univ_nonempty
  rw [← Finset.mul_sum, hu, mul_zero] at hsum
  exact (lt_irrefl 0 hsum)

/-- The sharp lower norm bound in squared form; `s² = d`. -/
theorem sum_sq_le_card_sub_one_mul_heightGauge_sq (s : ℝ)
    (hsq : s ^ 2 = (Fintype.card ι : ℝ)) (u : ι → ℝ)
    (hu : ∑ i, u i = 0) :
    ∑ i, u i ^ 2 ≤ ((Fintype.card ι : ℝ) - 1) * heightGauge s u ^ 2 := by
  let L := heightGauge s u
  have hm : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have ha : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ s * u i + L := by
    intro i _
    have hi := neg_mul_le_heightGauge s u i
    dsimp [L]
    linarith
  have hi := Finset.sum_sq_le_sq_sum_of_nonneg ha
  have hsum : ∑ i, (s * u i + L) = (Fintype.card ι : ℝ) * L := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hu]
    simp
  have hsum_sq : ∑ i, (s * u i + L) ^ 2 =
      s ^ 2 * (∑ i, u i ^ 2) + (Fintype.card ι : ℝ) * L ^ 2 := by
    calc
      _ = ∑ i, (s ^ 2 * u i ^ 2 + (2 * s * L) * u i + L ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hu]
        simp
  rw [hsum, hsum_sq, hsq] at hi
  have hout : (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ) - 1) * L ^ 2 -
      (Fintype.card ι : ℝ) * (∑ i, u i ^ 2) ≥ 0 := by
    nlinarith
  have hprod : 0 ≤ (Fintype.card ι : ℝ) *
      (((Fintype.card ι : ℝ) - 1) * L ^ 2 - ∑ i, u i ^ 2) := by
    nlinarith
  have := (mul_nonneg_iff_of_pos_left hm).mp hprod
  dsimp [L] at this
  linarith

/-- The sharp upper norm bound in squared form, using the zero-sum condition. -/
theorem heightGauge_sq_le_card_sub_one_mul_sum_sq (s : ℝ)
    (hsq : s ^ 2 = (Fintype.card ι : ℝ)) (u : ι → ℝ)
    (hu : ∑ i, u i = 0) :
    heightGauge s u ^ 2 ≤ ((Fintype.card ι : ℝ) - 1) * ∑ i, u i ^ 2 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i : ι => -s * u i)
  change heightGauge s u = -s * u i at hi
  have hsum : ∑ j ∈ Finset.univ.erase i, u j = -u i := by
    have h := Finset.sum_erase_add (Finset.univ : Finset ι) u (Finset.mem_univ i)
    rw [hu] at h
    linarith
  have hsumsq : ∑ j ∈ Finset.univ.erase i, u j ^ 2 = (∑ j, u j ^ 2) - u i ^ 2 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun j => u j ^ 2) (Finset.mem_univ i)
    linarith
  have hc : ((Finset.univ.erase i : Finset ι).card : ℝ) =
      (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.mpr inferInstance)]
    norm_num
  have hcauchy := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i) (f := u)
  rw [hsum, hsumsq, hc] at hcauchy
  rw [hi]
  nlinarith [hsq]

/-- The usual Euclidean length of a finite coordinate vector. -/
noncomputable def euclideanLength (u : ι → ℝ) : ℝ := Real.sqrt (∑ i, u i ^ 2)

omit [Nonempty ι] in
theorem euclideanLength_nonneg (u : ι → ℝ) : 0 ≤ euclideanLength u :=
  Real.sqrt_nonneg _

omit [Nonempty ι] in
theorem euclideanLength_sq (u : ι → ℝ) : euclideanLength u ^ 2 = ∑ i, u i ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (u i)))

omit [Nonempty ι] in
theorem euclideanLength_neg (u : ι → ℝ) :
    euclideanLength (fun i => -u i) = euclideanLength u := by
  simp [euclideanLength]

omit [Nonempty ι] in
/-- The coordinate formula is exactly Mathlib's ordinary Euclidean-space norm. -/
theorem euclideanLength_eq_norm (u : ι → ℝ) :
    euclideanLength u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ := by
  simpa [euclideanLength, Real.norm_eq_abs, sq_abs] using
    (PiLp.norm_eq_of_L2 (WithLp.toLp 2 u : EuclideanSpace ℝ ι)).symm

/-- The two unsquared sharp Euclidean norm inequalities in (3.2). -/
theorem heightGauge_norm_bounds (hd : 2 ≤ Fintype.card ι) (u : ι → ℝ)
    (hu : ∑ i, u i = 0) :
    euclideanLength u / Real.sqrt ((Fintype.card ι : ℝ) - 1) ≤
      heightGauge (Real.sqrt (Fintype.card ι : ℝ)) u ∧
    heightGauge (Real.sqrt (Fintype.card ι : ℝ)) u ≤
      Real.sqrt ((Fintype.card ι : ℝ) - 1) * euclideanLength u := by
  have hm : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hd
  have hs : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = (Fintype.card ι : ℝ) :=
    Real.sq_sqrt (by linarith)
  have hroot : 0 < Real.sqrt ((Fintype.card ι : ℝ) - 1) :=
    Real.sqrt_pos.mpr (by linarith)
  have hrootsq : (Real.sqrt ((Fintype.card ι : ℝ) - 1)) ^ 2 =
      (Fintype.card ι : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hnorm := euclideanLength_nonneg u
  have hnormsq := euclideanLength_sq u
  have hL := heightGauge_nonneg (Real.sqrt (Fintype.card ι : ℝ)) u hu
  have hlo := sum_sq_le_card_sub_one_mul_heightGauge_sq _ hs u hu
  have hhi := heightGauge_sq_le_card_sub_one_mul_sum_sq _ hs u hu
  constructor
  · apply (div_le_iff₀ hroot).mpr
    have hp : 0 ≤ Real.sqrt ((Fintype.card ι : ℝ) - 1) *
        heightGauge (Real.sqrt (Fintype.card ι : ℝ)) u :=
      mul_nonneg hroot.le hL
    nlinarith [sq_nonneg (euclideanLength u +
      Real.sqrt ((Fintype.card ι : ℝ) - 1) * heightGauge (Real.sqrt (Fintype.card ι : ℝ)) u)]
  · have hp : 0 ≤ Real.sqrt ((Fintype.card ι : ℝ) - 1) * euclideanLength u :=
      mul_nonneg hroot.le hnorm
    nlinarith [sq_nonneg (heightGauge (Real.sqrt (Fintype.card ι : ℝ)) u +
      Real.sqrt ((Fintype.card ι : ℝ) - 1) * euclideanLength u)]

/-- The sharp bounds with the native Euclidean norm, as printed in Lemma 3.2. -/
theorem heightGauge_norm_bounds_euclidean (hd : 2 ≤ Fintype.card ι) (u : ι → ℝ)
    (hu : ∑ i, u i = 0) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ / Real.sqrt ((Fintype.card ι : ℝ) - 1) ≤
      heightGauge (Real.sqrt (Fintype.card ι : ℝ)) u ∧
    heightGauge (Real.sqrt (Fintype.card ι : ℝ)) u ≤
      Real.sqrt ((Fintype.card ι : ℝ) - 1) * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ := by
  simpa only [euclideanLength_eq_norm] using heightGauge_norm_bounds hd u hu

/-- The floor hyperplane `E`, represented by its zero coordinate sum. -/
def ZeroSumFloor (ι : Type*) [Fintype ι] := {u : ι → ℝ // ∑ i, u i = 0}

/-- The directed distance on the floor used in the extension formula. -/
noncomputable def floorDistance (s : ℝ) (u v : ZeroSumFloor ι) : ℝ :=
  heightGauge s (fun i => u.val i - v.val i)

@[simp] theorem floorDistance_self (s : ℝ) (u : ZeroSumFloor ι) :
    floorDistance s u u = 0 := by
  simp [floorDistance]

theorem floorDistance_nonneg (s : ℝ) (u v : ZeroSumFloor ι) :
    0 ≤ floorDistance s u v := by
  apply heightGauge_nonneg
  rw [Finset.sum_sub_distrib, u.property, v.property, sub_self]

theorem floorDistance_triangle (s : ℝ) (u v w : ZeroSumFloor ι) :
    floorDistance s u w ≤ floorDistance s u v + floorDistance s v w := by
  have heq : (fun i => u.val i - v.val i + (v.val i - w.val i)) =
      (fun i => u.val i - w.val i) := by
    funext i
    exact sub_add_sub_cancel _ _ _
  simpa only [floorDistance, heq] using
    heightGauge_add_le s (fun i => u.val i - v.val i) (fun i => v.val i - w.val i)

section Extension

variable {X : Type*}

/-- Infimal extension, with no finite-set restriction. -/
noncomputable def heightExtension (D : X → X → ℝ) (B : Set X)
    (h : X → ℝ) (x : X) : ℝ :=
  sInf (Set.range (fun w : B => h w.val + D x w.val))

theorem extension_values_bddBelow (D : X → X → ℝ)
    (hD : ∀ x y, 0 ≤ D x y) (B : Set X) (h : X → ℝ)
    (hb : BddBelow (h '' B)) (x : X) :
    BddBelow (Set.range (fun w : B => h w.val + D x w.val)) := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  rintro t ⟨w, rfl⟩
  have ha' : a ≤ h w.val := ha (Set.mem_image_of_mem h w.property)
  have hd := hD x w.val
  linarith

/-- The real-valued infimum is a genuine greatest lower bound, hence finite. -/
theorem heightExtension_isGLB (D : X → X → ℝ)
    (hD : ∀ x y, 0 ≤ D x y) (B : Set X) (hB : B.Nonempty) (h : X → ℝ)
    (hb : BddBelow (h '' B)) (x : X) :
    IsGLB (Set.range (fun w : B => h w.val + D x w.val)) (heightExtension D B h x) := by
  apply isGLB_csInf
  · obtain ⟨w, hw⟩ := hB
    exact ⟨_, Set.mem_range_self (⟨w, hw⟩ : B)⟩
  · exact extension_values_bddBelow D hD B h hb x

/-- The infimal extension agrees exactly with compatible height data.
Only a lower bound on the data is needed, weaker than the paper's boundedness. -/
theorem heightExtension_agrees (D : X → X → ℝ)
    (hD : ∀ x y, 0 ≤ D x y) (hzero : ∀ x, D x x = 0)
    (B : Set X) (h : X → ℝ) (hb : BddBelow (h '' B))
    (hcompat : ∀ u ∈ B, ∀ v ∈ B, h u - h v ≤ D u v)
    (u : X) (hu : u ∈ B) : heightExtension D B h u = h u := by
  apply le_antisymm
  · have hx := csInf_le (extension_values_bddBelow D hD B h hb u)
      (Set.mem_range_self (⟨u, hu⟩ : B))
    simpa only [heightExtension, hzero, add_zero] using hx
  · apply le_csInf
    · exact ⟨_, Set.mem_range_self (⟨u, hu⟩ : B)⟩
    · rintro t ⟨v, rfl⟩
      have hv := hcompat u hu v.val v.property
      linarith

/-- The directed Lipschitz inequality survives taking the actual infimum. -/
theorem heightExtension_directed (D : X → X → ℝ)
    (hD : ∀ x y, 0 ≤ D x y)
    (htri : ∀ x y z, D x z ≤ D x y + D y z)
    (B : Set X) (hB : B.Nonempty) (h : X → ℝ)
    (hb : BddBelow (h '' B)) (u v : X) :
    heightExtension D B h u - heightExtension D B h v ≤ D u v := by
  have haux : heightExtension D B h u - D u v ≤ heightExtension D B h v := by
    apply le_csInf
    · obtain ⟨w, hw⟩ := hB
      exact ⟨_, Set.mem_range_self (⟨w, hw⟩ : B)⟩
    · rintro t ⟨w, rfl⟩
      have hx : heightExtension D B h u ≤ h w.val + D u w.val :=
        csInf_le (extension_values_bddBelow D hD B h hb u) (Set.mem_range_self w)
      have ht := htri u v w.val
      linarith
  linarith

end Extension

/-- The agreement assertion of Proposition 5.1 for the paper's actual floor gauge. -/
theorem floor_heightExtension_agrees (s : ℝ) (B : Set (ZeroSumFloor ι))
    (h : ZeroSumFloor ι → ℝ) (hb : BddBelow (h '' B))
    (hcompat : ∀ u ∈ B, ∀ v ∈ B, h u - h v ≤ floorDistance s u v)
    (u : ZeroSumFloor ι) (hu : u ∈ B) :
    heightExtension (floorDistance s) B h u = h u := by
  exact heightExtension_agrees (floorDistance s) (floorDistance_nonneg s)
    (floorDistance_self s) B h hb hcompat u hu

/-- The directed inequality in Proposition 5.1 for arbitrary nonempty data sets. -/
theorem floor_heightExtension_directed (s : ℝ) (B : Set (ZeroSumFloor ι))
    (hB : B.Nonempty) (h : ZeroSumFloor ι → ℝ)
    (hb : BddBelow (h '' B)) (u v : ZeroSumFloor ι) :
    heightExtension (floorDistance s) B h u -
      heightExtension (floorDistance s) B h v ≤ floorDistance s u v := by
  exact heightExtension_directed (floorDistance s) (floorDistance_nonneg s)
    (floorDistance_triangle s) B hB h hb u v

/-- Proposition 3.1 using the manuscript's distinct-pair antichain definition. -/
theorem isAntichain_iff_height_constraints {κ : Type*} (s : ℝ) (hs : 0 < s)
    (f : κ → ι → ℝ) (h : κ → ℝ) :
    IsAntichain (fun j i => f j i + h j / s) ↔
      ∀ j k, h j - h k ≤ heightGauge s (fun i => f j i - f k i) := by
  rw [← antichain_iff_height_constraints s hs f h]
  constructor
  · intro ha j k hlt
    by_cases hjk : j = k
    · subst k
      obtain ⟨i⟩ := ‹Nonempty ι›
      exact (lt_irrefl _ (hlt i))
    · exact ha k j (fun hkj => hjk hkj.symm) hlt
  · intro ha j k _ hlt
    exact ha k j hlt

/-- Proposition 3.1 with the paper's actual `√d` and zero-sum floor coordinates. -/
theorem floor_antichain_iff_height_constraints {κ : Type*}
    (f : κ → ZeroSumFloor ι) (h : κ → ℝ) :
    IsAntichain (fun j i => (f j).val i + h j / Real.sqrt (Fintype.card ι : ℝ)) ↔
      ∀ j k, h j - h k ≤ floorDistance (Real.sqrt (Fintype.card ι : ℝ)) (f j) (f k) := by
  have hm : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  exact isAntichain_iff_height_constraints _ (Real.sqrt_pos.mpr hm) (fun j => (f j).val) h

omit [Nonempty ι] in
theorem euclideanLength_sub_rev (u v : ι → ℝ) :
    euclideanLength (fun i => v i - u i) = euclideanLength (fun i => u i - v i) := by
  have heq : (fun i => v i - u i) = (fun i => -(u i - v i)) := by
    funext i
    ring
  rw [heq, euclideanLength_neg]

/-- The Lipschitz conclusion of Lemma 3.3 from its exact ordered constraints. -/
theorem height_constraints_lipschitz {κ : Type*} (hd : 2 ≤ Fintype.card ι)
    (f : κ → ZeroSumFloor ι) (h : κ → ℝ)
    (hc : ∀ j k, h j - h k ≤
      heightGauge (Real.sqrt (Fintype.card ι : ℝ)) (fun i => (f j).val i - (f k).val i))
    (j k : κ) : |h j - h k| ≤ Real.sqrt ((Fintype.card ι : ℝ) - 1) *
      euclideanLength (fun i => (f j).val i - (f k).val i) := by
  have hz : ∀ j k, ∑ i, ((f j).val i - (f k).val i) = 0 := by
    intro j k
    rw [Finset.sum_sub_distrib, (f j).property, (f k).property, sub_self]
  have hjk := (hc j k).trans (heightGauge_norm_bounds hd _ (hz j k)).2
  have hkj := (hc k j).trans (heightGauge_norm_bounds hd _ (hz k j)).2
  rw [euclideanLength_sub_rev] at hkj
  exact abs_le.mpr ⟨by linarith, hjk⟩

/-- Lemma 3.3 for an actual antichain in the paper's Gaussian floor/height coordinates. -/
theorem antichain_height_lipschitz {κ : Type*} (hd : 2 ≤ Fintype.card ι)
    (f : κ → ZeroSumFloor ι) (h : κ → ℝ)
    (ha : IsAntichain (fun j i => (f j).val i + h j / Real.sqrt (Fintype.card ι : ℝ)))
    (j k : κ) : |h j - h k| ≤ Real.sqrt ((Fintype.card ι : ℝ) - 1) *
      euclideanLength (fun i => (f j).val i - (f k).val i) := by
  have hm : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc := (isAntichain_iff_height_constraints _ (Real.sqrt_pos.mpr hm)
    (fun j => (f j).val) h).mp ha
  exact height_constraints_lipschitz hd f h hc j k

/-- The ordinary Euclidean Lipschitz conclusion of Proposition 5.1. -/
theorem floor_heightExtension_lipschitz (hd : 2 ≤ Fintype.card ι)
    (B : Set (ZeroSumFloor ι)) (hB : B.Nonempty) (h : ZeroSumFloor ι → ℝ)
    (hb : BddBelow (h '' B)) (u v : ZeroSumFloor ι) :
    |heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h u -
      heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h v| ≤
      Real.sqrt ((Fintype.card ι : ℝ) - 1) * euclideanLength (fun i => u.val i - v.val i) := by
  exact height_constraints_lipschitz hd (fun w => w)
    (heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h)
    (floor_heightExtension_directed _ B hB h hb) u v

/-- Proposition 5.1, collecting genuine finite infimum, agreement, and both
directed and ordinary Euclidean Lipschitz inequalities for the actual gauge.
Bounded-below data suffice; the manuscript assumes bounded data. -/
theorem floor_heightExtension_spec (hd : 2 ≤ Fintype.card ι)
    (B : Set (ZeroSumFloor ι)) (hB : B.Nonempty) (h : ZeroSumFloor ι → ℝ)
    (hb : BddBelow (h '' B))
    (hc : ∀ u ∈ B, ∀ v ∈ B, h u - h v ≤
      floorDistance (Real.sqrt (Fintype.card ι : ℝ)) u v) :
    (∀ x, IsGLB (Set.range (fun w : B => h w.val +
      floorDistance (Real.sqrt (Fintype.card ι : ℝ)) x w.val))
      (heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h x)) ∧
    (∀ u ∈ B, heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h u = h u) ∧
    (∀ u v, heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h u -
      heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h v ≤
      floorDistance (Real.sqrt (Fintype.card ι : ℝ)) u v) ∧
    (∀ u v, |heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h u -
      heightExtension (floorDistance (Real.sqrt (Fintype.card ι : ℝ))) B h v| ≤
      Real.sqrt ((Fintype.card ι : ℝ) - 1) * euclideanLength (fun i => u.val i - v.val i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact heightExtension_isGLB _ (floorDistance_nonneg _) B hB h hb x
  · intro u hu
    exact floor_heightExtension_agrees _ B h hb hc u hu
  · exact floor_heightExtension_directed _ B hB h hb
  · exact floor_heightExtension_lipschitz hd B hB h hb

end Antichain
