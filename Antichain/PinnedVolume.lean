import Antichain.FloorSpace
import Antichain.CubeModel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FunProp

/-! Pinned antichains with their actual dr-1 dimensional Euclidean product measure.
There are r+1 floor points and r free heights; the zeroth height is fixed to zero. -/

noncomputable section

namespace Antichain

open Finset Module MeasureTheory
open scoped Pointwise ENNReal

variable {ι : Type*} [Fintype ι]

/-- Exactly the free coordinates in the pinned section of the paper. -/
abbrev PinnedConfiguration (ι : Type*) [Fintype ι] (r : ℕ) :=
  (Fin (r + 1) → FloorSpace ι) × (Fin r → ℝ)

instance pinnedConfiguration_isAddHaar (r : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (PinnedConfiguration ι r)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Reinsert the height fixed at zero, without introducing a redundant coordinate. -/
def pinnedHeights {r : ℕ} (x : PinnedConfiguration ι r) : Fin (r + 1) → ℝ :=
  Fin.cons 0 x.2

/-- The actual floor/height points of a pinned configuration. -/
def pinnedPointCloud {r : ℕ} (x : PinnedConfiguration ι r) : Fin (r + 1) → ι → ℝ :=
  fun j i => (x.1 j).val i + pinnedHeights x j / Real.sqrt (Fintype.card ι : ℝ)

/-- Pinned antichains whose floor points belong to B. -/
def pinnedAntichainSet (B : Set (FloorSpace ι)) (r : ℕ) : Set (PinnedConfiguration ι r) :=
  {x | (∀ j, x.1 j ∈ B) ∧ IsAntichain (pinnedPointCloud x)}

/-- Pinned volume S_(r+1)(B), first as a nonnegative extended real measure. -/
def pinnedMass (B : Set (FloorSpace ι)) (r : ℕ) : ℝ≥0∞ :=
  volume (pinnedAntichainSet B r)

/-- Its real-valued form; positivity and finiteness must be established before logs. -/
def pinnedVolume (B : Set (FloorSpace ι)) (r : ℕ) : ℝ := (pinnedMass B r).toReal

theorem continuous_pinnedHeights_apply {r : ℕ} (j : Fin (r + 1)) :
    Continuous (fun x : PinnedConfiguration ι r => pinnedHeights x j) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [pinnedHeights, Fin.cons_zero]
    exact continuous_const
  · simp only [pinnedHeights, Fin.cons_succ]
    exact (continuous_apply k).comp continuous_snd

theorem continuous_pinnedPointCloud_apply {r : ℕ} (j : Fin (r + 1)) (i : ι) :
    Continuous (fun x : PinnedConfiguration ι r => pinnedPointCloud x j i) := by
  unfold pinnedPointCloud
  have hf : Continuous (fun x : PinnedConfiguration ι r => (x.1 j).val i) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst))
  exact hf.add ((continuous_pinnedHeights_apply j).div_const _)

theorem measurableSet_pinnedAntichainSet {B : Set (FloorSpace ι)}
    (hB : MeasurableSet B) (r : ℕ) : MeasurableSet (pinnedAntichainSet B r) := by
  have hfloors : MeasurableSet {x : PinnedConfiguration ι r | ∀ j, x.1 j ∈ B} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => hB.preimage
      ((measurable_pi_apply j).comp measurable_fst))
  have hanti : MeasurableSet {x : PinnedConfiguration ι r | IsAntichain (pinnedPointCloud x)} :=
    measurableSet_isAntichain pinnedPointCloud
      (fun j i => (continuous_pinnedPointCloud_apply j i).measurable)
  exact hfloors.inter hanti

/-- Apply the same coordinate permutation and floor translation to all floor points. -/
def pinnedAffinePermutation (e : ι ≃ ι) (a : FloorSpace ι) {r : ℕ}
    (x : PinnedConfiguration ι r) : PinnedConfiguration ι r :=
  (fun j => a + floorPermutation e (x.1 j), x.2)

theorem floorAffinePermutation_injective (e : ι ≃ ι) (a : FloorSpace ι) :
    Function.Injective (fun x : FloorSpace ι => a + floorPermutation e x) := by
  intro x y h
  exact (floorPermutation e).injective (add_left_cancel h)

theorem pinnedAffinePermutation_measurePreserving (e : ι ≃ ι) (a : FloorSpace ι) (r : ℕ) :
    MeasurePreserving (pinnedAffinePermutation e a (r := r)) volume volume := by
  have hf : MeasurePreserving (fun x : FloorSpace ι => a + floorPermutation e x)
      volume volume :=
    (measurePreserving_add_left volume a).comp (floorPermutation e).measurePreserving
  exact (volume_preserving_pi (fun _ : Fin (r + 1) => hf)).prod
    (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))

theorem pinnedPointCloud_affinePermutation (e : ι ≃ ι) (a : FloorSpace ι)
    {r : ℕ} (x : PinnedConfiguration ι r) :
    pinnedPointCloud (pinnedAffinePermutation e a x) =
      fun j i => a.val i + pinnedPointCloud x j (e i) := by
  funext j i
  simp only [pinnedPointCloud, pinnedAffinePermutation, pinnedHeights,
    floorPermutation_apply, Submodule.coe_add, PiLp.add_apply]
  ring

omit [Fintype ι] in
theorem isAntichain_coordinatePermutation_iff {κ : Type*} (e : ι ≃ ι)
    (x : κ → ι → ℝ) : IsAntichain (fun j i => x j (e i)) ↔ IsAntichain x := by
  have hp (j k : κ) : StrictBelow (fun i => x j (e i)) (fun i => x k (e i)) ↔
      StrictBelow (x j) (x k) := by
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      exact h (e i)
  simp only [IsAntichain, hp]

theorem pinnedAntichainSet_affinePermutation_iff (e : ι ≃ ι) (a : FloorSpace ι)
    (B : Set (FloorSpace ι)) {r : ℕ} (x : PinnedConfiguration ι r) :
    pinnedAffinePermutation e a x ∈
      pinnedAntichainSet ((fun f => a + floorPermutation e f) '' B) r ↔
      x ∈ pinnedAntichainSet B r := by
  have hm (j : Fin (r + 1)) :
      a + floorPermutation e (x.1 j) ∈ (fun f => a + floorPermutation e f) '' B ↔
        x.1 j ∈ B := (floorAffinePermutation_injective e a).mem_set_image
  change (∀ j, a + floorPermutation e (x.1 j) ∈ (fun f => a + floorPermutation e f) '' B) ∧
    IsAntichain (pinnedPointCloud (pinnedAffinePermutation e a x)) ↔
      (∀ j, x.1 j ∈ B) ∧ IsAntichain (pinnedPointCloud x)
  simp only [hm, pinnedPointCloud_affinePermutation, isAntichain_translate_iff,
    isAntichain_coordinatePermutation_iff]

theorem pinnedMass_affinePermutation (e : ι ≃ ι) (a : FloorSpace ι)
    {B : Set (FloorSpace ι)} (hB : MeasurableSet B) (r : ℕ) :
    pinnedMass ((fun f => a + floorPermutation e f) '' B) r = pinnedMass B r := by
  have hb' : MeasurableSet ((fun f => a + floorPermutation e f) '' B) :=
    ((floorPermutation e).toMeasurableEquiv.trans (MeasurableEquiv.addLeft a)).measurableSet_image.mpr hB
  have h := (pinnedAffinePermutation_measurePreserving e a r).measure_preimage
    (measurableSet_pinnedAntichainSet hb' r).nullMeasurableSet
  have heq : pinnedAffinePermutation e a ⁻¹'
      pinnedAntichainSet ((fun f => a + floorPermutation e f) '' B) r =
      pinnedAntichainSet B r := Set.ext (pinnedAntichainSet_affinePermutation_iff e a B)
  rw [heq] at h
  exact h.symm

/-- All d-1 Euclidean floor coordinates per point plus the r free heights. -/
theorem finrank_pinnedConfiguration [Nonempty ι] (r : ℕ) :
    finrank ℝ (PinnedConfiguration ι r) = Fintype.card ι * (r + 1) - 1 := by
  have hc : Fintype.card ι - 1 + 1 = Fintype.card ι :=
    Nat.sub_add_cancel Fintype.card_pos
  have hdim : finrank ℝ (PinnedConfiguration ι r) + 1 = Fintype.card ι * (r + 1) := by
    simp only [PinnedConfiguration, finrank_prod, finrank_pi_fintype, finrank_floorSpace,
      finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    calc
      (r + 1) * (Fintype.card ι - 1) + r * 1 + 1 =
          (r + 1) * (Fintype.card ι - 1 + 1) := by ring
      _ = _ := by rw [hc]; ring
  omega

theorem pinnedHeights_smul {r : ℕ} (s : ℝ) (x : PinnedConfiguration ι r) :
    pinnedHeights (s • x) = fun j => s * pinnedHeights x j := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [pinnedHeights]
  · simp [pinnedHeights, smul_eq_mul]

theorem pinnedPointCloud_smul {r : ℕ} (s : ℝ) (x : PinnedConfiguration ι r) :
    pinnedPointCloud (s • x) = fun j i => s * pinnedPointCloud x j i := by
  funext j i
  simp [pinnedPointCloud, pinnedHeights_smul, smul_eq_mul]
  ring

theorem pinnedAntichainSet_smul_iff {r : ℕ} (s : ℝ) (hs : 0 < s)
    (B : Set (FloorSpace ι)) (x : PinnedConfiguration ι r) :
    s • x ∈ pinnedAntichainSet (s • B) r ↔ x ∈ pinnedAntichainSet B r := by
  have hQ : StrictMono (fun t : ℝ => s * t) := strictMono_mul_left_of_pos hs
  simp only [pinnedAntichainSet, Set.mem_setOf_eq, Prod.smul_fst, Pi.smul_apply,
    Set.smul_mem_smul_set_iff₀ hs.ne', pinnedPointCloud_smul,
    isAntichain_coordinatewise_iff hQ]

/-- The actual pinned section scales bijectively, including its fixed zero height. -/
theorem pinnedAntichainSet_smul (s : ℝ) (hs : 0 < s)
    (B : Set (FloorSpace ι)) (r : ℕ) :
    pinnedAntichainSet (s • B) r = s • pinnedAntichainSet B r := by
  ext x
  constructor
  · intro hx
    refine ⟨s⁻¹ • x, ?_, by simp [hs.ne']⟩
    apply (pinnedAntichainSet_smul_iff s hs B (s⁻¹ • x)).mp
    simpa [hs.ne'] using hx
  · rintro ⟨y, hy, rfl⟩
    exact (pinnedAntichainSet_smul_iff s hs B y).mpr hy

/-- The full scaling exponent dr-1 of Lemma 3.5, for every actual floor set. -/
theorem pinnedMass_smul [Nonempty ι] (s : ℝ) (hs : 0 < s)
    (B : Set (FloorSpace ι)) (r : ℕ) :
    pinnedMass (s • B) r = ENNReal.ofReal s ^ (Fintype.card ι * (r + 1) - 1) *
      pinnedMass B r := by
  rw [pinnedMass, pinnedAntichainSet_smul s hs B r,
    Measure.addHaar_smul_of_nonneg volume hs.le, finrank_pinnedConfiguration]
  rw [ENNReal.ofReal_pow hs.le]
  rfl

theorem pinnedVolume_smul [Nonempty ι] (s : ℝ) (hs : 0 < s)
    (B : Set (FloorSpace ι)) (r : ℕ) :
    pinnedVolume (s • B) r = s ^ (Fintype.card ι * (r + 1) - 1) * pinnedVolume B r := by
  simp [pinnedVolume, pinnedMass_smul s hs, ENNReal.toReal_mul, ENNReal.toReal_pow, hs.le]

end Antichain
