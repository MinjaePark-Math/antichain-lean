import Antichain.ConfigurationContraction
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Order.Interval.Finset.Fin

/-! The printed vertices of the actual native-floor reference simplex. -/

noncomputable section

namespace Antichain

open Finset Set
open scoped Topology

def referenceSimplexVertex (d : ℕ) [NeZero d] (j : Fin d) : FloorSpace (Fin d) :=
  centeredFloor (WithLp.toLp 2 (fun i : Fin d ↦ if i < j then (1 : ℝ) else 0))

theorem referenceSimplexVertex_coordinate {d : ℕ} [NeZero d] (j i : Fin d) :
    (referenceSimplexVertex d j).val i =
      if i < j then ((d : ℝ) - j.val) / d else -(j.val : ℝ) / d := by
  have hsum : (∑ k : Fin d, if k < j then (1 : ℝ) else 0) = j.val := by
    have hset : Finset.univ.filter (fun k : Fin d ↦ k < j) = Finset.Iio j := by
      ext k
      simp
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, hset, Fin.card_Iio, nsmul_eq_mul, mul_one]
  change (if i < j then (1 : ℝ) else 0) -
    (∑ k : Fin d, if k < j then (1 : ℝ) else 0) / (Fintype.card (Fin d) : ℝ) = _
  rw [hsum, Fintype.card_fin]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  split_ifs
  · field_simp
  · field_simp
    ring

@[simp] theorem referenceSimplexVertex_zero {d : ℕ} [NeZero d] :
    referenceSimplexVertex d 0 = 0 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  simp [referenceSimplexVertex_coordinate]

theorem referenceSimplexVertex_mem {d : ℕ} [NeZero d] (j : Fin d) :
    referenceSimplexVertex d j ∈ referenceSimplex d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hcoord (i : Fin d) : (referenceSimplexVertex d j).val i =
      (if i < j then (1 : ℝ) else 0) - j.val / (d : ℝ) := by
    rw [referenceSimplexVertex_coordinate]
    split_ifs
    · field_simp
    · field_simp
      ring
  constructor
  · intro a b hab
    change (referenceSimplexVertex d j).val b ≤ (referenceSimplexVertex d j).val a
    rw [hcoord, hcoord]
    split_ifs <;> try linarith
    exact False.elim (by omega)
  · intro a b
    rw [hcoord, hcoord]
    split_ifs <;> linarith

theorem floor_eq_of_adjacent_differences {k : ℕ} (u v : FloorSpace (Fin (k + 1)))
    (h : ∀ i : Fin k, u.val i.castSucc - u.val i.succ = v.val i.castSucc - v.val i.succ) :
    u = v := by
  have hconst : ∀ i : Fin (k + 1), u.val i - v.val i = u.val 0 - v.val 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i hi => linarith [h i]
  have hu : ∑ i : Fin (k + 1), u.val i = 0 := u.property
  have hv : ∑ i : Fin (k + 1), v.val i = 0 := v.property
  have hsum : (k + 1 : ℝ) * (u.val 0 - v.val 0) = 0 := by
    have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ hconst i)
    simp only [Finset.sum_sub_distrib, hu, hv, sub_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hs
    nlinarith
  have hzero : u.val 0 - v.val 0 = 0 := (mul_eq_zero.mp hsum).resolve_left (by positivity)
  apply Subtype.ext
  apply PiLp.ext
  intro i
  linarith [hconst i]

theorem referenceSimplexVertex_adjacent {k : ℕ} (j : Fin (k + 1)) (i : Fin k) :
    (referenceSimplexVertex (k + 1) j).val i.castSucc -
      (referenceSimplexVertex (k + 1) j).val i.succ = if j = i.succ then 1 else 0 := by
  change ((if i.castSucc < j then (1 : ℝ) else 0) - _) -
    ((if i.succ < j then (1 : ℝ) else 0) - _) = _
  by_cases hj : j = i.succ
  · subst j
    simp
  · have hiff : i.castSucc < j ↔ i.succ < j := by
      change i.val < j.val ↔ i.val + 1 < j.val
      constructor <;> intro h
      · have hne : j.val ≠ i.val + 1 := by intro heq; apply hj; exact Fin.ext heq
        omega
      · omega
    simp [hiff, hj]

def referenceSimplexWeight {k : ℕ} (x : FloorSpace (Fin (k + 1))) : Fin (k + 1) → ℝ :=
  Fin.cons (1 - (x.val 0 - x.val (Fin.last k)))
    (fun i : Fin k ↦ x.val i.castSucc - x.val i.succ)

theorem referenceSimplexWeight_nonneg {k : ℕ} {x : FloorSpace (Fin (k + 1))}
    (hx : x ∈ referenceSimplex (k + 1)) (j : Fin (k + 1)) :
    0 ≤ referenceSimplexWeight x j := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · change 0 ≤ 1 - (x.val 0 - x.val (Fin.last k))
    linarith [hx.2 0 (Fin.last k)]
  · change 0 ≤ x.val i.castSucc - x.val i.succ
    exact sub_nonneg.mpr (hx.1 (by change i.val ≤ i.val + 1; omega))

theorem referenceSimplexWeight_sum {k : ℕ} (x : FloorSpace (Fin (k + 1))) :
    ∑ j, referenceSimplexWeight x j = 1 := by
  rw [referenceSimplexWeight, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ (fun i : Fin (k + 1) ↦ x.val i)
  have hlast := Fin.sum_univ_castSucc (fun i : Fin (k + 1) ↦ x.val i)
  linarith

theorem referenceSimplex_barycentric_identity {k : ℕ} (x : FloorSpace (Fin (k + 1))) :
    ∑ j, referenceSimplexWeight x j • referenceSimplexVertex (k + 1) j = x := by
  apply floor_eq_of_adjacent_differences
  intro i
  have hsum (a : Fin (k + 1)) :
      (∑ j, referenceSimplexWeight x j • referenceSimplexVertex (k + 1) j).val a =
        ∑ j, referenceSimplexWeight x j * (referenceSimplexVertex (k + 1) j).val a := by
    let l : FloorSpace (Fin (k + 1)) →ₗ[ℝ] ℝ :=
      (PiLp.projₗ 2 (fun _ : Fin (k + 1) ↦ ℝ) a).comp (FloorSpace (Fin (k + 1))).subtype
    simpa only [map_smul, smul_eq_mul] using
      (map_sum l (fun j ↦ referenceSimplexWeight x j • referenceSimplexVertex (k + 1) j) Finset.univ)
  rw [hsum, hsum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, referenceSimplexVertex_adjacent]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem referenceSimplex_eq_convexHull_vertices {k : ℕ} :
    referenceSimplex (k + 1) = convexHull ℝ (Set.range (referenceSimplexVertex (k + 1))) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_convexHull_of_exists_fintype (referenceSimplexWeight x)
      (referenceSimplexVertex (k + 1)) (referenceSimplexWeight_nonneg hx)
      (referenceSimplexWeight_sum x) (fun j ↦ Set.mem_range_self j)
      (referenceSimplex_barycentric_identity x)
  · exact convexHull_min (Set.range_subset_iff.mpr referenceSimplexVertex_mem)
      (convex_referenceSimplex (k + 1))

theorem referenceSimplexWeight_vertex {k : ℕ} (j r : Fin (k + 1)) :
    referenceSimplexWeight (referenceSimplexVertex (k + 1) j) r =
      if r = j then 1 else 0 := by
  refine Fin.cases ?_ (fun i ↦ ?_) r
  · refine Fin.cases ?_ (fun l ↦ ?_) j
    · simp [referenceSimplexWeight]
    · have h0 : (0 : Fin (k + 1)) < l.succ := by change 0 < l.val + 1; omega
      have hlast : ¬ Fin.last k < l.succ := not_lt_of_ge (Fin.le_last _)
      change 1 - ((referenceSimplexVertex (k + 1) l.succ).val 0 -
        (referenceSimplexVertex (k + 1) l.succ).val (Fin.last k)) = _
      rw [referenceSimplexVertex_coordinate, referenceSimplexVertex_coordinate]
      have hneq : (0 : Fin (k + 1)) ≠ l.succ := ne_of_lt h0
      simp only [h0, if_true, hlast, if_false, hneq]
      field_simp
      ring
  · change (referenceSimplexVertex (k + 1) j).val i.castSucc -
      (referenceSimplexVertex (k + 1) j).val i.succ = _
    rw [referenceSimplexVertex_adjacent]
    simp only [eq_comm]

theorem referenceSimplexWeight_affine {k : ℕ} (u v : FloorSpace (Fin (k + 1)))
    (a b : ℝ) (hab : a + b = 1) (j : Fin (k + 1)) :
    referenceSimplexWeight (a • u + b • v) j =
      a * referenceSimplexWeight u j + b * referenceSimplexWeight v j := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · change 1 - ((a * u.val 0 + b * v.val 0) -
      (a * u.val (Fin.last k) + b * v.val (Fin.last k))) =
      a * (1 - (u.val 0 - u.val (Fin.last k))) + b * (1 - (v.val 0 - v.val (Fin.last k)))
    nlinarith
  · change (a * u.val i.castSucc + b * v.val i.castSucc) -
      (a * u.val i.succ + b * v.val i.succ) =
      a * (u.val i.castSucc - u.val i.succ) + b * (v.val i.castSucc - v.val i.succ)
    ring

theorem referenceSimplexVertex_extreme {k : ℕ} (j : Fin (k + 1)) :
    referenceSimplexVertex (k + 1) j ∈ (referenceSimplex (k + 1)).extremePoints ℝ := by
  classical
  apply mem_extremePoints_iff_left.mpr
  refine ⟨referenceSimplexVertex_mem j, ?_⟩
  intro u hu v hv hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hw (r : Fin (k + 1)) :
      a * referenceSimplexWeight u r + b * referenceSimplexWeight v r =
        if r = j then 1 else 0 := by
    rw [← referenceSimplexWeight_affine u v a b hab r, heq,
      referenceSimplexWeight_vertex]
  have hzero (r : Fin (k + 1)) (hr : r ≠ j) : referenceSimplexWeight u r = 0 := by
    have h := hw r
    rw [if_neg hr] at h
    have hnonu := referenceSimplexWeight_nonneg hu r
    have hnonv := referenceSimplexWeight_nonneg hv r
    have hmul : a * referenceSimplexWeight u r = 0 := by nlinarith
    exact (mul_eq_zero.mp hmul).resolve_left ha.ne'
  have hone : referenceSimplexWeight u j = 1 := by
    have hs : ∑ r, referenceSimplexWeight u r = referenceSimplexWeight u j :=
      Finset.sum_eq_single j (fun r _ hr ↦ hzero r hr) (by simp)
    rw [referenceSimplexWeight_sum] at hs
    exact hs.symm
  have huweights (r : Fin (k + 1)) : referenceSimplexWeight u r = if r = j then 1 else 0 := by
    split_ifs with hr
    · exact hr ▸ hone
    · exact hzero r hr
  calc
    u = ∑ r, referenceSimplexWeight u r • referenceSimplexVertex (k + 1) r :=
      (referenceSimplex_barycentric_identity u).symm
    _ = referenceSimplexVertex (k + 1) j := by simp_rw [huweights]; simp

theorem referenceSimplex_extremePoints {k : ℕ} :
    (referenceSimplex (k + 1)).extremePoints ℝ = Set.range (referenceSimplexVertex (k + 1)) := by
  apply Set.Subset.antisymm
  · rw [referenceSimplex_eq_convexHull_vertices]
    exact extremePoints_convexHull_subset
  · rintro _ ⟨j, rfl⟩
    exact referenceSimplexVertex_extreme j

theorem referenceSimplexVertex_injective {k : ℕ} :
    Function.Injective (referenceSimplexVertex (k + 1)) := by
  intro i j hij
  have h := congrArg (fun v ↦ referenceSimplexWeight v i) hij
  change referenceSimplexWeight (referenceSimplexVertex (k + 1) i) i =
    referenceSimplexWeight (referenceSimplexVertex (k + 1) j) i at h
  rw [referenceSimplexWeight_vertex, referenceSimplexWeight_vertex, if_pos rfl] at h
  by_contra hne
  rw [if_neg hne] at h
  norm_num at h

theorem referenceSimplex_three_edge_sq (i j : Fin 3) (hij : i ≠ j) :
    dist (referenceSimplexVertex 3 i) (referenceSimplexVertex 3 j) ^ 2 = (2 : ℝ) / 3 := by
  rw [dist_eq_norm]
  change ‖(referenceSimplexVertex 3 i).val - (referenceSimplexVertex 3 j).val‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
  simp_rw [referenceSimplexVertex_coordinate]
  fin_cases i <;> fin_cases j <;> first | exact False.elim (hij rfl) | norm_num [Fin.lt_def, Fin.ext_iff]

theorem referenceSimplex_three_equilateral :
    referenceSimplex 3 = convexHull ℝ (Set.range (referenceSimplexVertex 3)) ∧
      Function.Injective (referenceSimplexVertex 3) ∧
      0 < Real.sqrt ((2 : ℝ) / 3) ∧
      ∀ i j : Fin 3, i ≠ j →
        dist (referenceSimplexVertex 3 i) (referenceSimplexVertex 3 j) = Real.sqrt ((2 : ℝ) / 3) := by
  refine ⟨referenceSimplex_eq_convexHull_vertices, referenceSimplexVertex_injective,
    Real.sqrt_pos.mpr (by norm_num), ?_⟩
  intro i j hij
  have hs := referenceSimplex_three_edge_sq i j hij
  have hroot := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ) / 3)
  nlinarith [(dist_nonneg : 0 ≤ dist (referenceSimplexVertex 3 i) (referenceSimplexVertex 3 j)),
    Real.sqrt_nonneg ((2 : ℝ) / 3)]

/-- All printed vertex assertions in the native Euclidean floor, for positive dimension. -/
theorem referenceSimplex_vertices_source (d : ℕ) [NeZero d] :
    (referenceSimplex d).extremePoints ℝ = Set.range (referenceSimplexVertex d) ∧
      referenceSimplex d = convexHull ℝ (Set.range (referenceSimplexVertex d)) ∧
      referenceSimplexVertex d 0 = 0 ∧
      ∀ j i : Fin d, (referenceSimplexVertex d j).val i =
        if i < j then ((d : ℝ) - j.val) / d else -(j.val : ℝ) / d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  exact ⟨referenceSimplex_extremePoints, referenceSimplex_eq_convexHull_vertices,
    referenceSimplexVertex_zero, referenceSimplexVertex_coordinate⟩

end Antichain
