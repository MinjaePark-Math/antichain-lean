import Antichain.FloorSpace
import Antichain.ReferenceSimplex
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Greedy farthest insertion of finite metric configurations. -/

noncomputable section

namespace Antichain

open Finset

section FiniteTraversal

variable {α X : Type*} [PseudoMetricSpace X]

/-- Distance to the nearest selected label. The empty-set value is irrelevant to
the traversal, whose initial selected set contains its starting label. -/
def nearestSelectedDistance (p : α → X) (A : Finset α) (x : α) : ℝ :=
  if h : A.Nonempty then A.inf' h (fun a ↦ dist (p x) (p a)) else 0

theorem nearestSelectedDistance_le (p : α → X) {A : Finset α} {a : α} (ha : a ∈ A) (x : α) :
    nearestSelectedDistance p A x ≤ dist (p x) (p a) := by
  rw [nearestSelectedDistance, dif_pos ⟨a, ha⟩]
  exact Finset.inf'_le _ ha

theorem nearestSelectedDistance_attained (p : α → X) {A : Finset α} (hA : A.Nonempty) (x : α) :
    ∃ a ∈ A, nearestSelectedDistance p A x = dist (p x) (p a) := by
  rw [nearestSelectedDistance, dif_pos hA]
  exact Finset.exists_mem_eq_inf' hA _

theorem nearestSelectedDistance_nonneg (p : α → X) (A : Finset α) (x : α) :
    0 ≤ nearestSelectedDistance p A x := by
  by_cases hA : A.Nonempty
  · obtain ⟨a, _, ha⟩ := nearestSelectedDistance_attained p hA x
    rw [ha]
    exact dist_nonneg
  · simp [nearestSelectedDistance, hA]

theorem nearestSelectedDistance_antitone (p : α → X) {A B : Finset α}
    (hA : A.Nonempty) (hAB : A ⊆ B) (x : α) :
    nearestSelectedDistance p B x ≤ nearestSelectedDistance p A x := by
  obtain ⟨a, ha, heq⟩ := nearestSelectedDistance_attained p hA x
  rw [heq]
  exact nearestSelectedDistance_le p (hAB ha) x

variable [Fintype α] [DecidableEq α]

/-- Choose a farthest unselected label; the fallback is only used after the
finite configuration has been exhausted. -/
def greedyPick (p : α → X) (start : α) (A : Finset α) : α :=
  if h : (Finset.univ \ A).Nonempty then
    (Finset.exists_max_image (Finset.univ \ A) (nearestSelectedDistance p A) h).choose
  else start

theorem greedyPick_spec (p : α → X) (start : α) {A : Finset α}
    (hA : (Finset.univ \ A).Nonempty) :
    greedyPick p start A ∉ A ∧ ∀ y ∉ A,
      nearestSelectedDistance p A y ≤ nearestSelectedDistance p A (greedyPick p start A) := by
  unfold greedyPick
  rw [dif_pos hA]
  have h := (Finset.exists_max_image (Finset.univ \ A) (nearestSelectedDistance p A) hA).choose_spec
  exact ⟨(Finset.mem_sdiff.mp h.1).2, fun y hy ↦ h.2 y (by simp [hy])⟩

/-- The actual traversal, beginning at the prescribed label. -/
def greedyPrefix (p : α → X) (start : α) : ℕ → List α
  | 0 => [start]
  | n + 1 => (greedyPrefix p start n).concat (greedyPick p start (greedyPrefix p start n).toFinset)

theorem greedyPrefix_length (p : α → X) (start : α) (n : ℕ) :
    (greedyPrefix p start n).length = n + 1 := by
  induction n with
  | zero => simp [greedyPrefix]
  | succ n ih => simp [greedyPrefix, ih]

theorem start_mem_greedyPrefix (p : α → X) (start : α) (n : ℕ) :
    start ∈ greedyPrefix p start n := by
  induction n with
  | zero => simp [greedyPrefix]
  | succ n ih => simp [greedyPrefix, List.concat_eq_append, ih]

theorem greedyPrefix_set_nonempty (p : α → X) (start : α) (n : ℕ) :
    (greedyPrefix p start n).toFinset.Nonempty :=
  ⟨start, List.mem_toFinset.mpr (start_mem_greedyPrefix p start n)⟩

theorem greedyPrefix_set_succ (p : α → X) (start : α) (n : ℕ) :
    (greedyPrefix p start (n + 1)).toFinset =
      insert (greedyPick p start (greedyPrefix p start n).toFinset) (greedyPrefix p start n).toFinset := by
  ext a
  simp [greedyPrefix, List.concat_eq_append]

theorem greedyPrefix_set_subset_succ (p : α → X) (start : α) (n : ℕ) :
    (greedyPrefix p start n).toFinset ⊆ (greedyPrefix p start (n + 1)).toFinset := by
  rw [greedyPrefix_set_succ]
  exact Finset.subset_insert _ _

theorem greedyPrefix_nodup (p : α → X) (start : α) (n : ℕ)
    (hn : n + 1 ≤ Fintype.card α) : (greedyPrefix p start n).Nodup := by
  induction n with
  | zero => simp [greedyPrefix]
  | succ n ih =>
    have hnd := ih (by omega)
    have hrem : (Finset.univ \ (greedyPrefix p start n).toFinset).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have hle := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp he)
      rw [Finset.card_univ, List.toFinset_card_of_nodup hnd, greedyPrefix_length] at hle
      omega
    rw [greedyPrefix, List.nodup_concat]
    exact ⟨by simpa only [List.mem_toFinset] using (greedyPick_spec p start hrem).1, hnd⟩

theorem greedyPrefix_remaining_nonempty (p : α → X) (start : α) (n : ℕ)
    (hn : n + 2 ≤ Fintype.card α) :
    (Finset.univ \ (greedyPrefix p start n).toFinset).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  have hle := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp he)
  rw [Finset.card_univ, List.toFinset_card_of_nodup (greedyPrefix_nodup p start n (by omega)),
    greedyPrefix_length] at hle
  omega

/-- The insertion distance of the next selected point to the current prefix. -/
def greedyRadius (p : α → X) (start : α) (n : ℕ) : ℝ :=
  nearestSelectedDistance p (greedyPrefix p start n).toFinset
    (greedyPick p start (greedyPrefix p start n).toFinset)

theorem greedyRadius_nonneg (p : α → X) (start : α) (n : ℕ) :
    0 ≤ greedyRadius p start n := nearestSelectedDistance_nonneg p _ _

theorem greedyRadius_parent (p : α → X) (start : α) (n : ℕ) :
    ∃ a ∈ greedyPrefix p start n,
      greedyRadius p start n = dist
        (p (greedyPick p start (greedyPrefix p start n).toFinset)) (p a) := by
  obtain ⟨a, ha, heq⟩ := nearestSelectedDistance_attained p (greedyPrefix_set_nonempty p start n) _
  exact ⟨a, List.mem_toFinset.mp ha, heq⟩

theorem greedyRadius_farthest (p : α → X) (start : α) (n : ℕ)
    (hn : n + 2 ≤ Fintype.card α) (y : α) (hy : y ∉ greedyPrefix p start n) :
    nearestSelectedDistance p (greedyPrefix p start n).toFinset y ≤ greedyRadius p start n :=
  (greedyPick_spec p start (greedyPrefix_remaining_nonempty p start n hn)).2 y
    (by simpa only [List.mem_toFinset] using hy)

theorem greedyRadius_succ_le (p : α → X) (start : α) (n : ℕ)
    (hn : n + 3 ≤ Fintype.card α) : greedyRadius p start (n + 1) ≤ greedyRadius p start n := by
  let y := greedyPick p start (greedyPrefix p start (n + 1)).toFinset
  have hy := (greedyPick_spec p start (greedyPrefix_remaining_nonempty p start (n + 1) (by omega))).1
  have hyold : y ∉ (greedyPrefix p start n).toFinset :=
    fun h ↦ hy (greedyPrefix_set_subset_succ p start n h)
  exact (nearestSelectedDistance_antitone p (greedyPrefix_set_nonempty p start n)
    (greedyPrefix_set_subset_succ p start n) y).trans
      ((greedyPick_spec p start (greedyPrefix_remaining_nonempty p start n (by omega))).2 y hyold)

theorem greedyPrefix_separated_insert (p : α → X) (start : α) (n : ℕ)
    (hold : ((greedyPrefix p start n).toFinset : Set α).Pairwise
      (fun a b ↦ greedyRadius p start n ≤ dist (p a) (p b))) :
    ((greedyPrefix p start (n + 1)).toFinset : Set α).Pairwise
      (fun a b ↦ greedyRadius p start n ≤ dist (p a) (p b)) := by
  rw [greedyPrefix_set_succ]
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact False.elim (hab rfl)
    · exact nearestSelectedDistance_le p hb _
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · rw [dist_comm]
      exact nearestSelectedDistance_le p ha _
    · exact hold ha hb hab

/-- At insertion n+1, every pair among the first n+2 selected labels is at least
the insertion distance apart. This is derived from the actual traversal. -/
theorem greedyPrefix_pairwise_separated (p : α → X) (start : α) (n : ℕ)
    (hn : n + 2 ≤ Fintype.card α) :
    ((greedyPrefix p start (n + 1)).toFinset : Set α).Pairwise
      (fun a b ↦ greedyRadius p start n ≤ dist (p a) (p b)) := by
  induction n with
  | zero =>
    apply greedyPrefix_separated_insert
    simp [greedyPrefix]
  | succ n ih =>
    have hold := ih (by omega)
    apply greedyPrefix_separated_insert
    intro a ha b hb hab
    exact (greedyRadius_succ_le p start n (by omega)).trans (hold ha hb hab)

theorem greedyPrefix_card (p : α → X) (start : α) (n : ℕ)
    (hn : n + 1 ≤ Fintype.card α) : (greedyPrefix p start n).toFinset.card = n + 1 := by
  rw [List.toFinset_card_of_nodup (greedyPrefix_nodup p start n hn), greedyPrefix_length]

/-- The traversal exhausts the finite configuration, without duplicates. -/
theorem greedyPrefix_exhausts (p : α → X) (start : α) :
    ∀ a : α, a ∈ greedyPrefix p start (Fintype.card α - 1) := by
  letI : Nonempty α := ⟨start⟩
  have hcard : (greedyPrefix p start (Fintype.card α - 1)).toFinset.card = Fintype.card α := by
    rw [greedyPrefix_card p start _ (by have := Fintype.card_pos (α := α); omega)]
    exact Nat.sub_add_cancel Fintype.card_pos
  have heq : (greedyPrefix p start (Fintype.card α - 1)).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  intro a
  exact List.mem_toFinset.mp (by rw [heq]; exact Finset.mem_univ a)

/-- The constructed traversal gives an actual permutation of n+1 labels. -/
def greedyOrdering {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1)) :
    Fin (n + 1) ≃ Fin (n + 1) :=
  (finCongr (greedyPrefix_length p start n).symm).trans
    ((greedyPrefix_nodup p start n (by simp)).getEquivOfForallMemList _
      (by simpa only [Fintype.card_fin, Nat.add_sub_cancel] using greedyPrefix_exhausts p start))

@[simp] theorem greedyOrdering_apply {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1))
    (j : Fin (n + 1)) :
    greedyOrdering p start j = (greedyPrefix p start n).get
      (Fin.cast (greedyPrefix_length p start n).symm j) := rfl

theorem greedyPrefix_isPrefix_of_le (p : α → X) (start : α) {m n : ℕ} (hmn : m ≤ n) :
    greedyPrefix p start m <+: greedyPrefix p start n := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact List.prefix_refl _
  | succ n ih =>
    by_cases hm : m ≤ n
    · apply (ih hm).trans
      rw [greedyPrefix, List.concat_eq_append]
      exact List.prefix_append _ _
    · have hm' : m = n + 1 := by omega
      subst m
      exact List.prefix_refl _

/-- The final permutation agrees with every earlier greedy prefix. -/
theorem greedyOrdering_get_prefix {n m : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1))
    (hmn : m ≤ n) (i : Fin (m + 1)) :
    greedyOrdering p start ⟨i.val, by omega⟩ = (greedyPrefix p start m).get
      (Fin.cast (greedyPrefix_length p start m).symm i) := by
  rw [greedyOrdering_apply]
  have h := (greedyPrefix_isPrefix_of_le p start hmn).getElem
    (show i.val < (greedyPrefix p start m).length by rw [greedyPrefix_length]; exact i.isLt)
  simpa only [List.get_eq_getElem, Fin.coe_cast] using h.symm

@[simp] theorem greedyOrdering_zero {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1)) :
    greedyOrdering p start 0 = start := by
  simpa only [greedyPrefix, List.get_eq_getElem, Fin.coe_cast, List.getElem_cons_zero]
    using greedyOrdering_get_prefix p start (Nat.zero_le n) (0 : Fin 1)

/-- At position j+1 the actual final permutation selects the point picked by
the j-th greedy insertion. -/
theorem greedyOrdering_insertion {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1))
    (j : Fin n) :
    greedyOrdering p start ⟨j.val + 1, by omega⟩ =
      greedyPick p start (greedyPrefix p start j.val).toFinset := by
  have h := greedyOrdering_get_prefix p start (Nat.succ_le_of_lt j.isLt)
    (⟨j.val + 1, by omega⟩ : Fin (j.val + 1 + 1))
  have h' : greedyOrdering p start ⟨j.val + 1, by omega⟩ =
      ((greedyPrefix p start j.val).concat
        (greedyPick p start (greedyPrefix p start j.val).toFinset))[j.val + 1]'(by
          simp only [List.length_concat, greedyPrefix_length]; omega) := by
    simpa only [greedyPrefix, List.get_eq_getElem, Fin.coe_cast] using h
  apply h'.trans
  simpa only [List.concat_eq_append] using
    (List.getElem_concat_length (l := greedyPrefix p start j.val)
      (a := greedyPick p start (greedyPrefix p start j.val).toFinset)
      (greedyPrefix_length p start j.val).symm (by simp [greedyPrefix_length]))

/-- Each insertion has an actual earlier parent in the constructed permutation,
and its edge length is exactly the nearest insertion radius. -/
theorem greedyOrdering_parent {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1))
    (j : Fin n) :
    ∃ k : Fin (j.val + 1), greedyRadius p start j.val =
      dist (p (greedyOrdering p start ⟨j.val + 1, by omega⟩))
        (p (greedyOrdering p start ⟨k.val, by omega⟩)) := by
  obtain ⟨a, ha, hdist⟩ := greedyRadius_parent p start j.val
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  let k : Fin (j.val + 1) := Fin.cast (greedyPrefix_length p start j.val) i
  have hk : greedyOrdering p start ⟨k.val, by omega⟩ = a := by
    rw [greedyOrdering_get_prefix p start (Nat.le_of_lt j.isLt) k]
    simpa only [k, Fin.cast_cast, Fin.cast_refl] using hi
  refine ⟨k, ?_⟩
  rw [greedyOrdering_insertion, hk]
  exact hdist

/-- Choose the earlier parent index certified by the constructed traversal. -/
def greedyParent {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1)) (j : Fin n) :
    Fin (j.val + 1) := (greedyOrdering_parent p start j).choose

theorem greedyParent_dist {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1)) (j : Fin n) :
    greedyRadius p start j.val =
      dist (p (greedyOrdering p start ⟨j.val + 1, by omega⟩))
        (p (greedyOrdering p start ⟨(greedyParent p start j).val, by
          have := (greedyParent p start j).isLt; omega⟩)) :=
  (greedyOrdering_parent p start j).choose_spec

theorem greedyOrdering_nearest_previous {n : ℕ} (p : Fin (n + 1) → X) (start : Fin (n + 1))
    (j : Fin n) (k : Fin (j.val + 1)) :
    greedyRadius p start j.val ≤
      dist (p (greedyOrdering p start ⟨j.val + 1, by omega⟩))
        (p (greedyOrdering p start ⟨k.val, by omega⟩)) := by
  rw [greedyOrdering_insertion,
    greedyOrdering_get_prefix p start (Nat.le_of_lt j.isLt) k]
  exact nearestSelectedDistance_le p (List.mem_toFinset.mpr (List.get_mem _ _)) _

end FiniteTraversal

section NativePacking

open MeasureTheory
open scoped ENNReal

/-- Packing in the actual induced (d-1)-dimensional Euclidean floor. Disjoint
balls of radius L/2 are contained in the ball of radius 2d. Their canonical
Haar volumes yield the dimension-dependent power bound. -/
theorem floor_packing_power_bound {α : Type*} [DecidableEq α] {d : ℕ}
    (hd : 2 ≤ d) (s : Finset α) (p : α → FloorSpace (Fin d)) {L : ℝ}
    (hL : 0 ≤ L) (hLmax : L ≤ 2 * (d : ℝ))
    (hp : ∀ a ∈ s, ‖p a‖ ≤ (d : ℝ))
    (hsep : (s : Set α).Pairwise (fun a b ↦ L ≤ dist (p a) (p b))) :
    (s.card : ℝ) * (L / 2) ^ (d - 1) ≤ (2 * (d : ℝ)) ^ (d - 1) := by
  letI : NeZero d := ⟨by omega⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  by_cases hLpos : 0 < L
  · have hdisj : Set.PairwiseDisjoint (s : Set α) (fun a ↦ Metric.ball (p a) (L / 2)) := by
      intro a ha b hb hab
      exact Metric.ball_disjoint_ball (by linarith [hsep ha hb hab])
    have hsubset : (⋃ a ∈ s, Metric.ball (p a) (L / 2)) ⊆
        Metric.ball (0 : FloorSpace (Fin d)) (2 * (d : ℝ)) := by
      intro x hx
      obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ha, hx⟩ := Set.mem_iUnion.mp hx
      exact Metric.ball_subset_ball' (by simpa only [dist_zero_right] using
        (show L / 2 + ‖p a‖ ≤ 2 * (d : ℝ) by linarith [hp a ha])) hx
    have hm : (∑ a ∈ s, (volume : Measure (FloorSpace (Fin d))) (Metric.ball (p a) (L / 2))) ≤
        volume (Metric.ball (0 : FloorSpace (Fin d)) (2 * (d : ℝ))) := by
      rw [← measure_biUnion_finset hdisj (fun _ _ ↦ measurableSet_ball)]
      exact measure_mono hsubset
    have hdim : Module.finrank ℝ (FloorSpace (Fin d)) = d - 1 := by
      simpa only [Fintype.card_fin] using (finrank_floorSpace (ι := Fin d))
    let U : ℝ≥0∞ := (volume : Measure (FloorSpace (Fin d))) (Metric.ball 0 1)
    have hball (a : α) : (volume : Measure (FloorSpace (Fin d))) (Metric.ball (p a) (L / 2)) =
        ENNReal.ofReal ((L / 2) ^ (d - 1)) * U := by
      rw [Measure.addHaar_ball_of_pos volume _ (half_pos hLpos), hdim]
    simp_rw [hball] at hm
    rw [Measure.addHaar_ball_of_pos volume _ (by positivity), hdim] at hm
    change (∑ _a ∈ s, ENNReal.ofReal ((L / 2) ^ (d - 1)) * U) ≤
      ENNReal.ofReal ((2 * (d : ℝ)) ^ (d - 1)) * U at hm
    simp only [Finset.sum_const, nsmul_eq_mul] at hm
    have hUpos : 0 < U := Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self zero_lt_one⟩
    have hUtop : U ≠ ⊤ := ne_of_lt
      ((measure_mono Metric.ball_subset_closedBall).trans_lt
        (isCompact_closedBall (0 : FloorSpace (Fin d)) 1).measure_lt_top)
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUtop) hm
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hL (by norm_num : (0 : ℝ) ≤ 2)) _),
      ENNReal.toReal_ofReal (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)) _)] at hr
    exact (mul_le_mul_iff_left₀ (ENNReal.toReal_pos hUpos.ne' hUtop)).mp
      (by simpa only [mul_assoc, mul_comm U.toReal] using hr)
  · have hzero : L = 0 := le_antisymm (le_of_not_gt hLpos) hL
    simp only [hzero, zero_div, zero_pow (by omega : d - 1 ≠ 0), mul_zero]
    positivity

/-- Every actual reference-simplex configuration has insertion radii at most
its elementary diameter bound, independently of how many labels it has. -/
theorem greedyRadius_le_two_dimension {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} (hd : 2 ≤ d) (p : α → FloorSpace (Fin d))
    (hp : ∀ a, p a ∈ referenceSimplex d) (start : α) (n : ℕ) :
    greedyRadius p start n ≤ 2 * (d : ℝ) := by
  calc
    _ ≤ dist (p (greedyPick p start (greedyPrefix p start n).toFinset)) (p start) :=
      nearestSelectedDistance_le p (List.mem_toFinset.mpr (start_mem_greedyPrefix p start n)) _
    _ = ‖p (greedyPick p start (greedyPrefix p start n).toFinset) - p start‖ := dist_eq_norm _ _
    _ ≤ ‖p (greedyPick p start (greedyPrefix p start n).toFinset)‖ + ‖p start‖ := norm_sub_le _ _
    _ ≤ _ := by
      linarith [norm_le_dimension_of_mem_referenceSimplex hd (hp start),
        norm_le_dimension_of_mem_referenceSimplex hd (hp (greedyPick p start (greedyPrefix p start n).toFinset))]

/-- Applying the actual (d-1)-dimensional packing measure argument to the first
n+2 points produced by the greedy algorithm. -/
theorem greedyRadius_floor_power_bound {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} (hd : 2 ≤ d) (p : α → FloorSpace (Fin d))
    (hp : ∀ a, p a ∈ referenceSimplex d) (start : α) (n : ℕ)
    (hn : n + 2 ≤ Fintype.card α) :
    ((n + 2 : ℕ) : ℝ) * (greedyRadius p start n / 2) ^ (d - 1) ≤
      (2 * (d : ℝ)) ^ (d - 1) := by
  have h := floor_packing_power_bound hd (greedyPrefix p start (n + 1)).toFinset p
    (greedyRadius_nonneg p start n) (greedyRadius_le_two_dimension hd p hp start n)
    (fun a _ ↦ norm_le_dimension_of_mem_referenceSimplex hd (hp a))
    (greedyPrefix_pairwise_separated p start n hn)
  simpa only [greedyPrefix_card p start (n + 1) (by omega)] using h

/-- Extract the inverse-dimensional power from a finite packing inequality. -/
theorem radius_bound_of_packing_power {N a B : ℝ} {m : ℕ}
    (hN : 0 < N) (ha : 0 ≤ a) (hB : 0 ≤ B) (hm : m ≠ 0)
    (hpack : N * a ^ m ≤ B ^ m) : a ≤ B * N ^ (-(m : ℝ)⁻¹) := by
  have hdiv : a ^ m ≤ B ^ m / N := (le_div_iff₀ hN).mpr (by simpa only [mul_comm] using hpack)
  have hr := Real.rpow_le_rpow (pow_nonneg ha m) hdiv
    (inv_nonneg.mpr (Nat.cast_nonneg m))
  rw [Real.pow_rpow_inv_natCast ha hm,
    Real.div_rpow (pow_nonneg hB m) hN.le, Real.pow_rpow_inv_natCast hB hm] at hr
  simpa only [Real.rpow_neg hN.le, div_eq_mul_inv] using hr

/-- The requested greedy packing rate for the actual reference simplex. -/
theorem greedyRadius_floor_bound {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} (hd : 2 ≤ d) (p : α → FloorSpace (Fin d))
    (hp : ∀ a, p a ∈ referenceSimplex d) (start : α) (n : ℕ)
    (hn : n + 2 ≤ Fintype.card α) :
    greedyRadius p start n ≤ 4 * (d : ℝ) *
      (((n + 2 : ℕ) : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) := by
  have h := radius_bound_of_packing_power (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))
    (div_nonneg (greedyRadius_nonneg p start n) (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ)) (by omega : d - 1 ≠ 0)
    (greedyRadius_floor_power_bound hd p hp start n hn)
  nlinarith

/-- The full factorial product estimate for the actual greedy insertion radii.
The extra initial factor makes `(r+1)!` a valid denominator. -/
theorem greedyRadii_product_floor_bound {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} (hd : 2 ≤ d) (p : α → FloorSpace (Fin d))
    (hp : ∀ a, p a ∈ referenceSimplex d) (start : α) (r : ℕ)
    (hr : r + 1 ≤ Fintype.card α) :
    (∏ j ∈ Finset.range r, greedyRadius p start j) ≤
      (4 * (d : ℝ)) ^ r * ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprev := ih (by omega)
    have hnext := greedyRadius_floor_bound hd p hp start r (by omega)
    rw [Finset.prod_range_succ]
    calc
      _ ≤ ((4 * (d : ℝ)) ^ r * ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹)) *
          (4 * (d : ℝ) * (((r + 2 : ℕ) : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹))) :=
        mul_le_mul hprev hnext (greedyRadius_nonneg p start r) (by positivity)
      _ = (4 * (d : ℝ)) ^ (r + 1) * ((r + 1 + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) := by
        have hfac : ((r + 1 + 1).factorial : ℝ) =
            ((r + 2 : ℕ) : ℝ) * ((r + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
        rw [hfac, Real.mul_rpow (by positivity) (by positivity), pow_succ]
        ring

/-- A ready-to-use parent family for the triangular height-coordinate argument:
its order fixes the pinned root, and its edge product satisfies the actual
factorial packing bound. -/
theorem greedy_parent_edges_floor_product_bound {d r : ℕ} (hd : 2 ≤ d)
    (p : Fin (r + 1) → FloorSpace (Fin d)) (hp : ∀ a, p a ∈ referenceSimplex d) :
    let e := greedyOrdering p 0
    let parent := greedyParent p 0
    e 0 = 0 ∧ (∏ j : Fin r, dist (p (e j.succ))
      (p (e ⟨(parent j).val, by have := (parent j).isLt; omega⟩))) ≤
        (4 * (d : ℝ)) ^ r * ((r + 1).factorial : ℝ) ^ (-((d - 1 : ℕ) : ℝ)⁻¹) := by
  dsimp only
  refine ⟨greedyOrdering_zero p 0, ?_⟩
  have heq (j : Fin r) : dist (p (greedyOrdering p 0 j.succ))
      (p (greedyOrdering p 0 ⟨(greedyParent p 0 j).val, by
        have := (greedyParent p 0 j).isLt; omega⟩)) = greedyRadius p 0 j.val := by
    exact (greedyParent_dist p 0 j).symm
  simp_rw [heq]
  rw [Fin.prod_univ_eq_prod_range]
  exact greedyRadii_product_floor_bound hd p hp 0 r (by simp)

end NativePacking

end Antichain
