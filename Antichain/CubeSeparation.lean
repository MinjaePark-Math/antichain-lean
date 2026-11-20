import Antichain.FloorIntegralApproximation
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Positive separation and the touching-cube limiting passage in Lemma 5.4. -/

noncomputable section

namespace Antichain

open Set MeasureTheory Metric Finset
open scoped Topology BoundedContinuousFunction

theorem finite_compact_disjoint_separation {E : Type*} [MetricSpace E]
    (J : ℕ) (K : Fin J → Set E) (hK : ∀ j, IsCompact (K j))
    (hne : ∀ j, (K j).Nonempty) (hdis : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ a : ℝ, 0 < a ∧ ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, a ≤ dist x y := by
  classical
  have hp : ∀ p : Fin J × Fin J, ∃ a : ℝ, 0 < a ∧
      (p.1 ≠ p.2 → ∀ x ∈ K p.1, ∀ y ∈ K p.2, a ≤ dist x y) := by
    intro p
    by_cases hij : p.1 = p.2
    · exact ⟨1, zero_lt_one, fun hn => False.elim (hn hij)⟩
    obtain ⟨z, hz, hmin⟩ := ((hK p.1).prod (hK p.2)).exists_isMinOn
      ((hne p.1).prod (hne p.2)) continuous_dist.continuousOn
    have hzpos : 0 < dist z.1 z.2 := by
      apply dist_pos.mpr
      intro heq
      exact Set.disjoint_left.mp (hdis hij) hz.1 (heq ▸ hz.2)
    exact ⟨dist z.1 z.2, hzpos, fun _ x hx y hy =>
      (isMinOn_iff.mp hmin) (x, y) ⟨hx, hy⟩⟩
  choose a ha hbound using hp
  let D : ℝ := 1 + ∑ p, 1 / a p
  have hD : 0 < D := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun p _ => (one_div_pos.mpr (ha p)).le))
  refine ⟨1 / D, one_div_pos.mpr hD, fun i j hij x hx y hy => ?_⟩
  have hsingle : 1 / a (i, j) ≤ D :=
    (Finset.single_le_sum (fun p _ => (one_div_pos.mpr (ha p)).le)
      (Finset.mem_univ (i, j))).trans (le_add_of_nonneg_left zero_le_one)
  have hle : 1 / D ≤ a (i, j) := by
    simpa only [one_div_one_div] using
      one_div_le_one_div_of_le (one_div_pos.mpr (ha (i, j))) hsingle
  exact hle.trans (hbound (i, j) hij x hx y hy)

variable {d : ℕ} [NeZero d]

def shrunkenCubeOrigin (a : Fin (d - 1) → ℝ) (L t : ℝ) : Fin (d - 1) → ℝ :=
  fun i => a i + t * L / 2

def openOrthonormalFloorCube
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) : Set (FloorSpace (Fin d)) :=
  {x | ∀ i, a i < b.repr x i ∧ b.repr x i < a i + L}

omit [NeZero d] in
theorem isOpen_openOrthonormalFloorCube
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) : IsOpen (openOrthonormalFloorCube b a L) := by
  unfold openOrthonormalFloorCube
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ i).comp b.repr.continuous)).inter
    (isOpen_lt ((PiLp.continuous_apply 2 _ i).comp b.repr.continuous) continuous_const)

omit [NeZero d] in
theorem openOrthonormalFloorCube_subset
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) :
    openOrthonormalFloorCube b a L ⊆ orthonormalFloorCube b a L :=
  fun _ hx i => ⟨(hx i).1.le, (hx i).2.le⟩

omit [NeZero d] in
theorem shrunkenCube_subset_interior
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    orthonormalFloorCube b (shrunkenCubeOrigin a L t) ((1 - t) * L) ⊆
      interior (orthonormalFloorCube b a L) := by
  intro x hx
  have hopen : x ∈ openOrthonormalFloorCube b a L := by
    intro i
    have hi := hx i
    dsimp only [shrunkenCubeOrigin] at hi
    constructor <;> nlinarith [mul_pos ht hL]
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset ((isOpen_openOrthonormalFloorCube b a L).mem_nhds hopen)
      (openOrthonormalFloorCube_subset b a L))

omit [NeZero d] in
theorem shrunkenCubes_pairwise_disjoint
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j => Disjoint (interior (orthonormalFloorCube b (a i) (L i)))
      (interior (orthonormalFloorCube b (a j) (L j)))))
    {t : ℝ} (ht : 0 < t) :
    Pairwise (fun i j =>
      Disjoint (orthonormalFloorCube b (shrunkenCubeOrigin (a i) (L i) t) ((1 - t) * L i))
        (orthonormalFloorCube b (shrunkenCubeOrigin (a j) (L j) t) ((1 - t) * L j))) := by
  intro i j hij
  exact (hdis hij).mono (shrunkenCube_subset_interior b (a i) (hL i) ht)
    (shrunkenCube_subset_interior b (a j) (hL j) ht)

omit [NeZero d] in
theorem shrunkenCubes_positive_separation
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (hdis : Pairwise (fun i j => Disjoint (interior (orthonormalFloorCube b (a i) (L i)))
      (interior (orthonormalFloorCube b (a j) (L j)))))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ∃ sep : ℝ, 0 < sep ∧ ∀ i j, i ≠ j →
      ∀ x ∈ orthonormalFloorCube b (shrunkenCubeOrigin (a i) (L i) t) ((1 - t) * L i),
      ∀ y ∈ orthonormalFloorCube b (shrunkenCubeOrigin (a j) (L j) t) ((1 - t) * L j), sep ≤ dist x y := by
  exact finite_compact_disjoint_separation J _
    (fun j => isCompact_orthonormalFloorCube b _ _)
    (fun j => orthonormalFloorCube_nonempty b _ (mul_pos (sub_pos.mpr ht.2) (hL j)).le)
    (shrunkenCubes_pairwise_disjoint b J a L hL hdis ht.1)

omit [NeZero d] in
theorem floorCubeWeightInf_mono_subcube (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a a' : Fin (d - 1) → ℝ) {L L' : ℝ} (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hsub : orthonormalFloorCube b a' L' ⊆ orthonormalFloorCube b a L) :
    floorCubeWeightInf sigma b a L ≤ floorCubeWeightInf sigma b a' L' := by
  obtain ⟨x, hx, heq, _⟩ := floorCubeWeightInf_attained sigma b a' hL'
  rw [heq]
  exact (floorCubeWeightInf_attained sigma b a hL).choose_spec.2.2 x (hsub hx)

omit [NeZero d] in
/-- Shrinking touching cubes loses at most the explicit volume factor;
their true infimum weights can only increase. No regularity of a minimizer
or unproved convergence of optimized weights is assumed. -/
theorem shrunkenCube_lower_weight_sum
    (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    {p t : ℝ} (hp : 0 ≤ p) (ht : t ∈ Set.Ioo 0 1) :
    (1 - t) ^ (d - 1) *
      (∑ j, L j ^ (d - 1) * floorCubeWeightInf sigma b (a j) (L j) ^ p) ≤
    ∑ j, ((1 - t) * L j) ^ (d - 1) *
      floorCubeWeightInf sigma b (shrunkenCubeOrigin (a j) (L j) t) ((1 - t) * L j) ^ p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hL' : 0 ≤ (1 - t) * L j := (mul_pos (sub_pos.mpr ht.2) (hL j)).le
  have hweight := floorCubeWeightInf_mono_subcube sigma b (a j)
    (shrunkenCubeOrigin (a j) (L j) t) (hL j).le hL'
    ((shrunkenCube_subset_interior b (a j) (hL j) ht.1).trans interior_subset)
  have hpow := Real.rpow_le_rpow (floorCubeWeightInf_pos sigma b (a j) (hL j).le).le hweight hp
  rw [mul_pow]
  calc
    _ = ((1 - t) ^ (d - 1) * L j ^ (d - 1)) *
        floorCubeWeightInf sigma b (a j) (L j) ^ p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (pow_nonneg (sub_pos.mpr ht.2).le _) (pow_nonneg (hL j).le _))

end Antichain
