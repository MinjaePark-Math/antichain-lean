import Antichain.AffineAlcoveGroup
import Antichain.AlcoveTiling
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Int.Interval

/-! Discreteness of actual reflection-word orbits and local finiteness of tiles.
No covering, disjointness, or cited alcove input is assumed. -/

noncomputable section

namespace Antichain

open Set Finset
open scoped Topology

variable (d : ℕ) [NeZero d]

def integerFloorBall (R : ℝ) : Set (FloorSpace (Fin d)) :=
  {z | ‖z‖ ≤ R ∧ ∀ i, ∃ k : ℤ, z.val i = (k : ℝ)}

omit [NeZero d] in
theorem integerFloorBall_finite (R : ℝ) : (integerFloorBall d R).Finite := by
  classical
  let encode : integerFloorBall d R → (Fin d → Set.Icc (-⌈R⌉ : ℤ) ⌈R⌉) := fun z i =>
    ⟨Classical.choose (z.property.2 i), by
      have heq := Classical.choose_spec (z.property.2 i)
      have hb : |((Classical.choose (z.property.2 i) : ℤ) : ℝ)| ≤ R := by
        rw [← heq]
        exact (PiLp.norm_apply_le z.val.val i).trans z.property.1
      have hceil : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
      have hbounds := (abs_le.mp (hb.trans hceil))
      constructor
      · exact_mod_cast hbounds.1
      · exact_mod_cast hbounds.2⟩
  have hinj : Function.Injective encode := by
    intro z w h
    apply Subtype.ext
    apply Subtype.ext
    ext i
    have hi := congrArg (fun f => (f i).val) h
    change Classical.choose (z.property.2 i) = Classical.choose (w.property.2 i) at hi
    rw [Classical.choose_spec (z.property.2 i), Classical.choose_spec (w.property.2 i), hi]
  letI : Finite (integerFloorBall d R) := Finite.of_injective encode hinj
  exact Set.toFinite _

def reflectionWordOrbit (x : FloorSpace (Fin d)) : Set (FloorSpace (Fin d)) :=
  Set.range (fun word : List (Fin d) => reflectionWordMap d word x)

theorem wordTranslation_norm_le_of_norm_image_le (word : List (Fin d))
    (x : FloorSpace (Fin d)) {R : ℝ} (h : ‖reflectionWordMap d word x‖ ≤ R) :
    ‖wordTranslation d word‖ ≤ R + ‖x‖ := by
  have heq : wordTranslation d word =
      reflectionWordMap d word x - floorPermutation (wordPermutation d word) x := by
    rw [reflectionWordMap_eq_affine]
    simp
  rw [heq]
  exact (norm_sub_le _ _).trans (by simpa using add_le_add_right h ‖x‖)

theorem reflectionWordOrbit_bounded_finite (x : FloorSpace (Fin d)) (R : ℝ) :
    {y | y ∈ reflectionWordOrbit d x ∧ ‖y‖ ≤ R}.Finite := by
  classical
  let parameters : Set (FloorSpace (Fin d) × Equiv.Perm (Fin d)) :=
    integerFloorBall d (R + ‖x‖) ×ˢ Set.univ
  have hp : parameters.Finite := (integerFloorBall_finite d _).prod (Set.finite_univ)
  have hf := hp.image (fun p => p.1 + floorPermutation p.2 x)
  apply hf.subset
  rintro y ⟨⟨word, rfl⟩, hy⟩
  refine ⟨(wordTranslation d word, wordPermutation d word), ?_, ?_⟩
  · exact ⟨⟨wordTranslation_norm_le_of_norm_image_le d word x hy,
      wordTranslation_integer d word⟩, Set.mem_univ _⟩
  · exact (reflectionWordMap_eq_affine d word x).symm

theorem reflectionWordOrbit_dist_sublevel_finite (x c : FloorSpace (Fin d)) (R : ℝ) :
    {y | y ∈ reflectionWordOrbit d x ∧ dist y c ≤ R}.Finite := by
  apply (reflectionWordOrbit_bounded_finite d x (R + ‖c‖)).subset
  rintro y ⟨hy, hdist⟩
  refine ⟨hy, ?_⟩
  calc
    ‖y‖ = dist y 0 := (dist_zero_right y).symm
    _ ≤ dist y c + dist c 0 := dist_triangle y c 0
    _ ≤ R + ‖c‖ := by simpa using add_le_add_right hdist ‖c‖

/-- Every actual reflection-word orbit has a closest point to any prescribed center. -/
theorem reflectionWordOrbit_has_dist_minimizer (x c : FloorSpace (Fin d)) :
    ∃ word : List (Fin d), ∀ v : List (Fin d),
      dist (reflectionWordMap d word x) c ≤ dist (reflectionWordMap d v x) c := by
  let s : Set (FloorSpace (Fin d)) :=
    {y | y ∈ reflectionWordOrbit d x ∧ dist y c ≤ dist x c}
  have hx : x ∈ s := ⟨⟨[], rfl⟩, le_rfl⟩
  obtain ⟨y, hy, hmin⟩ := Set.exists_min_image s (fun y => dist y c)
    (reflectionWordOrbit_dist_sublevel_finite d x c (dist x c)) ⟨x, hx⟩
  obtain ⟨word, rfl⟩ := hy.1
  refine ⟨word, fun v => ?_⟩
  by_cases hv : dist (reflectionWordMap d v x) c ≤ dist x c
  · exact hmin _ ⟨⟨v, rfl⟩, hv⟩
  · exact (hmin x hx).trans (le_of_not_ge hv)

theorem wordTranslation_norm_le_of_tile_meets_ball (hd : 2 ≤ d)
    (word : List (Fin d)) (c : FloorSpace (Fin d))
    (h : (reflectionTile d word ∩ Metric.ball c 1).Nonempty) :
    ‖wordTranslation d word‖ ≤ ‖c‖ + 1 + (d : ℝ) := by
  obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ := h
  have heq : wordTranslation d word =
      reflectionWordMap d word u - floorPermutation (wordPermutation d word) u := by
    rw [reflectionWordMap_eq_affine]
    simp
  have hybound : ‖reflectionWordMap d word u‖ ≤ ‖c‖ + 1 := by
    calc
      ‖reflectionWordMap d word u‖ = dist (reflectionWordMap d word u) 0 :=
        (dist_zero_right _).symm
      _ ≤ dist (reflectionWordMap d word u) c + dist c 0 := dist_triangle _ c 0
      _ ≤ ‖c‖ + 1 := by simpa only [dist_zero_right] using
        (add_le_add_right (Metric.mem_ball.mp hy).le ‖c‖ |>.trans_eq (add_comm 1 ‖c‖))
  rw [heq]
  calc
    ‖reflectionWordMap d word u - floorPermutation (wordPermutation d word) u‖ ≤
        ‖reflectionWordMap d word u‖ + ‖floorPermutation (wordPermutation d word) u‖ := norm_sub_le _ _
    _ ≤ ‖c‖ + 1 + (d : ℝ) := by
      simpa using add_le_add hybound (norm_le_dimension_of_mem_referenceSimplex hd hu)

/-- Local finiteness is a direct consequence of integer translations and finite coordinate permutations. -/
theorem alcoveTile_locallyFinite_direct (hd : 2 ≤ d) :
    LocallyFinite (fun t : AlcoveTile d => (t : Set (FloorSpace (Fin d)))) := by
  classical
  intro c
  refine ⟨Metric.ball c 1, Metric.ball_mem_nhds c zero_lt_one, ?_⟩
  let parameters : Set (FloorSpace (Fin d) × Equiv.Perm (Fin d)) :=
    integerFloorBall d (‖c‖ + 1 + (d : ℝ)) ×ˢ Set.univ
  let shape : (FloorSpace (Fin d) × Equiv.Perm (Fin d)) → Set (FloorSpace (Fin d)) :=
    fun p => (fun u => p.1 + floorPermutation p.2 u) '' referenceSimplex d
  have hp : parameters.Finite := (integerFloorBall_finite d _).prod (Set.finite_univ)
  have hshape : (shape '' parameters).Finite := hp.image shape
  apply Set.Finite.of_injOn (f := fun t : AlcoveTile d => t.val) ?_
    Subtype.val_injective.injOn hshape
  rintro t ht
  obtain ⟨word, hword⟩ := t.property
  refine ⟨(wordTranslation d word, wordPermutation d word), ?_, ?_⟩
  · refine ⟨⟨?_, wordTranslation_integer d word⟩, Set.mem_univ _⟩
    apply wordTranslation_norm_le_of_tile_meets_ball d hd word c
    simpa only [hword] using ht
  · exact (reflectionTile_eq_affine d word).symm.trans hword

end Antichain
