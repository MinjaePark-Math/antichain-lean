import Antichain.PinnedVolume
import Antichain.ReferenceSimplex
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Push

/-! Positive and finite actual pinned Euclidean antichain volumes. -/

noncomputable section

namespace Antichain

open Finset MeasureTheory
open scoped Topology ENNReal

theorem isClosed_pinnedAntichainSet {ι : Type*} [Fintype ι]
    {B : Set (FloorSpace ι)} (hB : IsClosed B) (r : ℕ) :
    IsClosed (pinnedAntichainSet B r) := by
  have hf : IsClosed {x : PinnedConfiguration ι r | ∀ j, x.1 j ∈ B} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j ↦ hB.preimage ((continuous_apply j).comp continuous_fst)
  have ha : IsClosed {x : PinnedConfiguration ι r | IsAntichain (pinnedPointCloud x)} := by
    simp only [IsAntichain, Set.setOf_forall]
    refine isClosed_iInter fun j ↦ isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦ ?_
    have ho : IsOpen {x : PinnedConfiguration ι r | StrictBelow (pinnedPointCloud x j) (pinnedPointCloud x k)} := by
      simp only [StrictBelow, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i ↦
        isOpen_lt (continuous_pinnedPointCloud_apply j i) (continuous_pinnedPointCloud_apply k i)
    exact ho.isClosed_compl
  exact hf.inter ha

/-- Pinning one height to zero and bounding floor coordinates bounds every free
height directly from the actual strict-antichain condition. -/
theorem pinned_height_bounds_referenceSimplex {d r : ℕ} (hd : 2 ≤ d)
    {x : PinnedConfiguration (Fin d) r} (hx : x ∈ pinnedAntichainSet (referenceSimplex d) r)
    (k : Fin r) : |x.2 k| ≤ 2 * Real.sqrt (d : ℝ) := by
  letI : NeZero d := ⟨by omega⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hz (i : Fin d) := referenceSimplex_coordinate_bounds (show 0 < d by omega) (hx.1 0) i
  have hk (i : Fin d) := referenceSimplex_coordinate_bounds (show 0 < d by omega) (hx.1 k.succ) i
  apply abs_le.mpr
  constructor
  · by_contra hlow
    have hq : x.2 k / Real.sqrt (d : ℝ) < -2 :=
      (div_lt_iff₀ hs).mpr (by linarith)
    apply hx.2 k.succ 0 (by simp)
    intro i
    simp only [pinnedPointCloud, pinnedHeights, Fin.cons_succ, Fin.cons_zero,
      Fintype.card_fin, zero_div, add_zero]
    linarith [(hz i).1, (hk i).2]
  · by_contra hupp
    have hq : 2 < x.2 k / Real.sqrt (d : ℝ) :=
      (lt_div_iff₀ hs).mpr (by linarith)
    apply hx.2 0 k.succ (Ne.symm (Fin.succ_ne_zero k))
    intro i
    simp only [pinnedPointCloud, pinnedHeights, Fin.cons_succ, Fin.cons_zero,
      Fintype.card_fin, zero_div, add_zero]
    linarith [(hz i).2, (hk i).1]

theorem isBounded_pinnedAntichainSet_referenceSimplex {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    Bornology.IsBounded (pinnedAntichainSet (referenceSimplex d) r) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (d : ℝ) (2 * Real.sqrt (d : ℝ)), fun x hx ↦ ?_⟩
  have hf : ‖x.1‖ ≤ (d : ℝ) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      (fun j ↦ norm_le_dimension_of_mem_referenceSimplex hd (hx.1 j))
  have hh : ‖x.2‖ ≤ 2 * Real.sqrt (d : ℝ) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      (fun k ↦ by simpa only [Real.norm_eq_abs] using pinned_height_bounds_referenceSimplex hd hx k)
  exact max_le_max hf hh

theorem isCompact_pinnedAntichainSet_referenceSimplex {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    IsCompact (pinnedAntichainSet (referenceSimplex d) r) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_pinnedAntichainSet (isClosed_referenceSimplex d) r,
      isBounded_pinnedAntichainSet_referenceSimplex hd r⟩

/-- The actual pinned mass is finite, including the one-point case r=0. -/
theorem pinnedMass_referenceSimplex_lt_top {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    pinnedMass (referenceSimplex d) r < ⊤ :=
  (isCompact_pinnedAntichainSet_referenceSimplex hd r).measure_lt_top

/-- Distinct zero-sum floor points differ strictly in both coordinate directions.
This strict witness makes an antichain robust under small perturbations. -/
theorem distinct_floor_exists_coordinate_gt {ι : Type*} [Fintype ι]
    {u v : FloorSpace ι} (hne : u ≠ v) : ∃ i : ι, v.val i < u.val i := by
  classical
  have hu : ∑ i : ι, u.val i = 0 := u.property
  have hv : ∑ i : ι, v.val i = 0 := v.property
  have hsum : (∑ i : ι, (u.val i - v.val i)) = 0 := by
    rw [Finset.sum_sub_distrib, hu, hv, sub_self]
  have hn : ∃ i ∈ (Finset.univ : Finset ι), u.val i - v.val i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    apply Subtype.ext
    ext i
    exact sub_eq_zero.mp (h i (Finset.mem_univ i))
  obtain ⟨i, _, hi⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
    (fun i : ι ↦ u.val i - v.val i) hsum hn
  exact ⟨i, sub_pos.mp hi⟩

/-- An explicitly open robust subset of the pinned antichain event. -/
def pinnedRobustSet {ι : Type*} [Fintype ι] (U : Set (FloorSpace ι)) (r : ℕ) :
    Set (PinnedConfiguration ι r) :=
  {x | (∀ j, x.1 j ∈ U) ∧ ∀ j k, j ≠ k → ∃ i,
    pinnedPointCloud x k i < pinnedPointCloud x j i}

theorem isOpen_pinnedRobustSet {ι : Type*} [Fintype ι]
    {U : Set (FloorSpace ι)} (hU : IsOpen U) (r : ℕ) : IsOpen (pinnedRobustSet U r) := by
  classical
  have hf : IsOpen {x : PinnedConfiguration ι r | ∀ j, x.1 j ∈ U} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun j ↦ hU.preimage ((continuous_apply j).comp continuous_fst)
  have ha : IsOpen {x : PinnedConfiguration ι r | ∀ j k, j ≠ k → ∃ i,
      pinnedPointCloud x k i < pinnedPointCloud x j i} := by
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun k ↦
      isOpen_iInter_of_finite fun _ ↦ isOpen_iUnion fun i ↦
        isOpen_lt (continuous_pinnedPointCloud_apply k i) (continuous_pinnedPointCloud_apply j i)
  exact hf.inter ha

theorem pinnedRobustSet_subset {ι : Type*} [Fintype ι]
    {U B : Set (FloorSpace ι)} (hUB : U ⊆ B) (r : ℕ) :
    pinnedRobustSet U r ⊆ pinnedAntichainSet B r := by
  rintro x ⟨hf, ha⟩
  refine ⟨fun j ↦ hUB (hf j), fun j k hne hlt ↦ ?_⟩
  obtain ⟨i, hi⟩ := ha j k hne
  exact (not_lt_of_gt hi) (hlt i)

/-- Any distinct finite family of floor points gives a robust pinned antichain
at zero heights. -/
theorem pinnedRobustSet_nonempty_of_injective {ι : Type*} [Fintype ι]
    {U : Set (FloorSpace ι)} {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (hf : ∀ j, f j ∈ U) (hinj : Function.Injective f) : (pinnedRobustSet U r).Nonempty := by
  let x : PinnedConfiguration ι r := (f, 0)
  have hz (j : Fin (r + 1)) : pinnedHeights x j = 0 := by
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [pinnedHeights, x]
  refine ⟨x, hf, fun j k hne ↦ ?_⟩
  obtain ⟨i, hi⟩ := distinct_floor_exists_coordinate_gt (fun heq ↦ hne (hinj heq))
  refine ⟨i, ?_⟩
  simpa only [pinnedPointCloud, hz, zero_div, add_zero] using hi

theorem referenceSimplexCore_smul {d : ℕ} {w : FloorSpace (Fin d)}
    (hw : w ∈ referenceSimplexCore d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s • w ∈ referenceSimplexCore d := by
  constructor
  · intro i j hij
    change s * w.val j < s * w.val i
    exact mul_lt_mul_of_pos_left (hw.1 i j hij) hs
  · intro i j
    change s * w.val i - s * w.val j < 1
    calc
      _ = s * (w.val i - w.val j) := by ring
      _ < s * 1 := mul_lt_mul_of_pos_left (hw.2 i j) hs
      _ ≤ 1 := by simpa only [mul_one] using hs1

/-- Every number of distinct points can be placed in the actual open simplex
core, by positive rescalings of its explicit arithmetic-progression point. -/
theorem exists_injective_family_referenceSimplexCore {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    ∃ f : Fin (r + 1) → FloorSpace (Fin d),
      (∀ j, f j ∈ referenceSimplexCore d) ∧ Function.Injective f := by
  letI : NeZero d := ⟨by omega⟩
  let w : FloorSpace (Fin d) := referenceSimplexInteriorPoint d
  have hw : w ∈ referenceSimplexCore d := referenceSimplexInteriorPoint_mem_core d
  have hwne : w ≠ 0 := by
    intro hz
    have hlt := hw.1 ⟨0, by omega⟩ ⟨1, by omega⟩ (by change (0 : ℕ) < 1; decide)
    simp [hz] at hlt
  have hcoord : ∃ i : Fin d, w.val i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hwne
    apply Subtype.ext
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  let s : Fin (r + 1) → ℝ := fun j ↦ ((j.val : ℝ) + 1) / ((r : ℝ) + 2)
  have hden : (0 : ℝ) < (r : ℝ) + 2 := by positivity
  have hs (j : Fin (r + 1)) : 0 < s j ∧ s j ≤ 1 := by
    have hj : (j.val : ℝ) < (r : ℝ) + 1 := by exact_mod_cast j.isLt
    constructor
    · exact div_pos (by positivity) hden
    · exact (div_le_one hden).mpr (by linarith)
  refine ⟨fun j ↦ s j • w, fun j ↦ referenceSimplexCore_smul hw (hs j).1 (hs j).2, ?_⟩
  intro j k h
  have hmul : s j * w.val i = s k * w.val i := by
    exact congrArg (fun z : FloorSpace (Fin d) ↦ z.val i) h
  have hscale : s j = s k := mul_right_cancel₀ hi hmul
  have hn := congrArg (fun z : ℝ ↦ z * ((r : ℝ) + 2)) hscale
  dsimp [s] at hn
  simp only [div_mul_cancel₀ _ hden.ne'] at hn
  apply Fin.ext
  exact_mod_cast (show (j.val : ℝ) = (k.val : ℝ) by linarith)

theorem pinnedRobustSet_referenceSimplexCore_nonempty {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    (pinnedRobustSet (referenceSimplexCore d) r).Nonempty := by
  obtain ⟨f, hf, hinj⟩ := exists_injective_family_referenceSimplexCore hd r
  exact pinnedRobustSet_nonempty_of_injective f hf hinj

/-- A nonempty open subset lies in the actual pinned antichain event, so its
actual product Haar measure is strictly positive for every number of points. -/
theorem pinnedMass_referenceSimplex_pos {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    0 < pinnedMass (referenceSimplex d) r := by
  have ho := isOpen_pinnedRobustSet (isOpen_referenceSimplexCore d) r
  have hp := ho.measure_pos (volume : Measure (PinnedConfiguration (Fin d) r))
    (pinnedRobustSet_referenceSimplexCore_nonempty hd r)
  exact hp.trans_le (measure_mono (pinnedRobustSet_subset (referenceSimplexCore_subset d) r))

theorem pinnedVolume_referenceSimplex_pos {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    0 < pinnedVolume (referenceSimplex d) r :=
  ENNReal.toReal_pos (pinnedMass_referenceSimplex_pos hd r).ne'
    (pinnedMass_referenceSimplex_lt_top hd r).ne

end Antichain
