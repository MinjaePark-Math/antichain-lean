import Antichain.CubeModel
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

/-! Explicit finite-grid simplicial interpolation on a cube.
Common scalar rounding gives the partition of unity of the Kuhn hats.
The ordered-simplex formulas identify the same hats as barycentric coordinates.
-/

noncomputable section

namespace Antichain

open Set Finset MeasureTheory
open scoped ENNReal NNReal Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]

local instance : DecidableEq ι := Classical.decEq ι

abbrev SimplicialGridVertex (ι : Type*) (N : ℕ) := ι → Fin (N + 1)

def simplicialRoundingLower {N : ℕ} (z : ι → ℝ) (v : SimplicialGridVertex ι N) : ℝ :=
  max 0 (univ.sup' univ_nonempty (fun i => (v i : ℝ) - z i))

def simplicialRoundingUpper {N : ℕ} (z : ι → ℝ) (v : SimplicialGridVertex ι N) : ℝ :=
  min 1 (univ.inf' univ_nonempty (fun i => (v i : ℝ) + 1 - z i))

def simplicialGridHat {N : ℕ} (z : ι → ℝ) (v : SimplicialGridVertex ι N) : ℝ :=
  max 0 (simplicialRoundingUpper z v - simplicialRoundingLower z v)

def simplicialRoundingFiber {N : ℕ} (z : ι → ℝ) (v : SimplicialGridVertex ι N) : Set ℝ :=
  {t | t ∈ Ico (0 : ℝ) 1 ∧ ∀ i, (v i : ℝ) ≤ z i + t ∧ z i + t < (v i : ℝ) + 1}

theorem simplicialRoundingFiber_eq_Ico {N : ℕ} (z : ι → ℝ)
    (v : SimplicialGridVertex ι N) :
    simplicialRoundingFiber z v =
      Ico (simplicialRoundingLower z v) (simplicialRoundingUpper z v) := by
  ext t
  constructor
  · rintro ⟨ht, hv⟩
    constructor
    · apply max_le ht.1
      exact Finset.sup'_le _ _ (fun i _ => by linarith [(hv i).1])
    · apply lt_min ht.2
      apply (Finset.lt_inf'_iff univ_nonempty).mpr
      intro i _
      linarith [(hv i).2]
  · intro ht
    have hlo : 0 ≤ t := (le_max_left _ _).trans ht.1
    have hhi : t < 1 := ht.2.trans_le (min_le_left _ _)
    refine ⟨⟨hlo, hhi⟩, fun i => ?_⟩
    have hi0 : (v i : ℝ) - z i ≤ t :=
      (Finset.le_sup' (fun i => (v i : ℝ) - z i) (mem_univ i)).trans
        ((le_max_right _ _).trans ht.1)
    have hi1 : t < (v i : ℝ) + 1 - z i :=
      ht.2.trans_le ((min_le_right _ _).trans
        (Finset.inf'_le (fun i => (v i : ℝ) + 1 - z i) (mem_univ i)))
    constructor <;> linarith

theorem measurableSet_simplicialRoundingFiber {N : ℕ} (z : ι → ℝ)
    (v : SimplicialGridVertex ι N) : MeasurableSet (simplicialRoundingFiber z v) := by
  rw [simplicialRoundingFiber_eq_Ico]
  exact measurableSet_Ico

theorem simplicialGridHat_nonneg {N : ℕ} (z : ι → ℝ) (v : SimplicialGridVertex ι N) :
    0 ≤ simplicialGridHat z v := le_max_left _ _

theorem simplicialGridHat_le_one {N : ℕ} (z : ι → ℝ) (v : SimplicialGridVertex ι N) :
    simplicialGridHat z v ≤ 1 := by
  apply max_le zero_le_one
  have hlo : 0 ≤ simplicialRoundingLower z v := le_max_left _ _
  have hhi : simplicialRoundingUpper z v ≤ 1 := min_le_left _ _
  linarith

theorem volume_simplicialRoundingFiber {N : ℕ} (z : ι → ℝ)
    (v : SimplicialGridVertex ι N) :
    volume (simplicialRoundingFiber z v) = ENNReal.ofReal (simplicialGridHat z v) := by
  rw [simplicialRoundingFiber_eq_Ico, Real.volume_Ico]
  unfold simplicialGridHat
  simp

omit [Fintype ι] [Nonempty ι] in
theorem simplicialRoundingFiber_pairwise_disjoint {N : ℕ} (z : ι → ℝ) :
    Pairwise (fun v w : SimplicialGridVertex ι N =>
      Disjoint (simplicialRoundingFiber z v) (simplicialRoundingFiber z w)) := by
  intro v w hvw
  apply Set.disjoint_left.mpr
  intro t hv hw
  apply hvw
  funext i
  apply Fin.ext
  have hvi : ((v i).val : ℝ) < (w i).val + 1 := lt_of_le_of_lt (hv.2 i).1 (hw.2 i).2
  have hwi : ((w i).val : ℝ) < (v i).val + 1 := lt_of_le_of_lt (hw.2 i).1 (hv.2 i).2
  have hvn : (v i).val < (w i).val + 1 := by exact_mod_cast hvi
  have hwn : (w i).val < (v i).val + 1 := by exact_mod_cast hwi
  omega

omit [Fintype ι] [Nonempty ι] in
theorem simplicialRoundingFiber_covers {N : ℕ} (z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) N) :
    (⋃ v : SimplicialGridVertex ι N, simplicialRoundingFiber z v) = Ico (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp ht
    exact hv.1
  · intro t ht
    have hbound (i : ι) : Nat.floor (z i + t) < N + 1 := by
      apply (Nat.floor_lt' (Nat.succ_ne_zero N)).mpr
      push_cast
      linarith [(hz i).2, ht.2]
    let v : SimplicialGridVertex ι N := fun i => ⟨Nat.floor (z i + t), hbound i⟩
    refine Set.mem_iUnion.mpr ⟨v, ht, fun i => ?_⟩
    exact ⟨Nat.floor_le (by linarith [(hz i).1, ht.1]), Nat.lt_floor_add_one _⟩

/-- The explicit Kuhn hat functions are a genuine finite partition of unity.
The proof identifies them with lengths of disjoint common-rounding fibers. -/
theorem sum_simplicialGridHat {N : ℕ} (z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) N) :
    ∑ v : SimplicialGridVertex ι N, simplicialGridHat z v = 1 := by
  classical
  have hmeasure := measure_iUnion (μ := (volume : Measure ℝ))
    (simplicialRoundingFiber_pairwise_disjoint (N := N) z)
    (measurableSet_simplicialRoundingFiber (N := N) z)
  rw [simplicialRoundingFiber_covers z hz, Real.volume_Ico] at hmeasure
  simp only [sub_zero, ENNReal.ofReal_one, tsum_fintype, volume_simplicialRoundingFiber] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_sum (fun v _ => ENNReal.ofReal_ne_top)] at hreal
  simpa only [ENNReal.toReal_one,
    ENNReal.toReal_ofReal (simplicialGridHat_nonneg _ _)] using hreal.symm

def simplicialGridPoint {N : ℕ} (v : SimplicialGridVertex ι N) : ι → ℝ :=
  fun i => (v i : ℝ) / (N : ℝ)

def scaledSimplicialGridHat (N : ℕ) (x : ι → ℝ) (v : SimplicialGridVertex ι N) : ℝ :=
  simplicialGridHat (fun i => (N : ℝ) * x i) v

theorem simplicialGridHat_support_near {N : ℕ} (z : ι → ℝ)
    (v : SimplicialGridVertex ι N) (hv : 0 < simplicialGridHat z v) (i : ι) :
    |z i - (v i : ℝ)| < 1 := by
  have hLU : simplicialRoundingLower z v < simplicialRoundingUpper z v := by
    have h := (lt_max_iff.mp hv).resolve_left (lt_irrefl 0)
    linarith
  have hmem : simplicialRoundingLower z v ∈ simplicialRoundingFiber z v := by
    rw [simplicialRoundingFiber_eq_Ico]
    exact ⟨le_rfl, hLU⟩
  apply abs_lt.mpr
  constructor <;> linarith [(hmem.2 i).1, (hmem.2 i).2, hmem.1.1, hmem.1.2]

theorem sum_scaledSimplicialGridHat (N : ℕ) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    ∑ v : SimplicialGridVertex ι N, scaledSimplicialGridHat N x v = 1 := by
  apply sum_simplicialGridHat
  intro i
  exact ⟨mul_nonneg (Nat.cast_nonneg N) (hx i).1,
    by simpa using mul_le_mul_of_nonneg_left (hx i).2 (Nat.cast_nonneg N)⟩

omit [Fintype ι] [Nonempty ι] in
theorem simplicialGridPoint_mem_cube {N : ℕ} (hN : 0 < N)
    (v : SimplicialGridVertex ι N) (i : ι) :
    simplicialGridPoint v i ∈ Icc (0 : ℝ) 1 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨div_nonneg (by positivity) hNR.le, ?_⟩
  apply (div_le_one hNR).mpr
  exact_mod_cast Nat.lt_succ_iff.mp (v i).isLt

theorem scaledSimplicialGridHat_support_dist {N : ℕ} (hN : 0 < N)
    (x : ι → ℝ) (v : SimplicialGridVertex ι N)
    (hv : 0 < scaledSimplicialGridHat N x v) :
    dist x (simplicialGridPoint v) ≤ 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (dist_pi_le_iff (one_div_nonneg.mpr hNR.le)).mpr
  intro i
  rw [Real.dist_eq]
  have hnear := simplicialGridHat_support_near (fun i => (N : ℝ) * x i) v hv i
  change |x i - (v i : ℝ) / (N : ℝ)| ≤ 1 / (N : ℝ)
  have heq : x i - (v i : ℝ) / (N : ℝ) = ((N : ℝ) * x i - (v i : ℝ)) / (N : ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hNR]
  exact div_le_div_of_nonneg_right hnear.le hNR.le

end Antichain
