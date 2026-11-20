import Antichain.PinnedVolume
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.FunProp

/-!
The actual common-height and pinned-height coordinate change. Its measure law
is proved from translation invariance and the finite-product splitting map,
without assuming a Jacobian or determinant formula.
-/

noncomputable section

namespace Antichain

open MeasureTheory Set
open scoped ENNReal

def heightCoordinates (r : ℕ) (p : ℝ × (Fin r → ℝ)) : Fin (r + 1) → ℝ :=
  Fin.cons p.1 (fun j => p.1 + p.2 j)

def heightDifferences (r : ℕ) (h : Fin (r + 1) → ℝ) : ℝ × (Fin r → ℝ) :=
  (h 0, fun j => h j.succ - h 0)

@[simp] theorem heightCoordinates_zero (r : ℕ) (p : ℝ × (Fin r → ℝ)) :
    heightCoordinates r p 0 = p.1 := rfl

@[simp] theorem heightCoordinates_succ (r : ℕ) (p : ℝ × (Fin r → ℝ)) (j : Fin r) :
    heightCoordinates r p j.succ = p.1 + p.2 j := rfl

theorem heightDifferences_heightCoordinates (r : ℕ) (p : ℝ × (Fin r → ℝ)) :
    heightDifferences r (heightCoordinates r p) = p := by
  apply Prod.ext
  · rfl
  · funext j
    simp [heightDifferences]

theorem heightCoordinates_heightDifferences (r : ℕ) (h : Fin (r + 1) → ℝ) :
    heightCoordinates r (heightDifferences r h) = h := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · simp [heightDifferences]

@[fun_prop] theorem heightCoordinates_continuous (r : ℕ) : Continuous (heightCoordinates r) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact continuous_fst
  · exact continuous_fst.add ((continuous_apply k).comp continuous_snd)

@[fun_prop] theorem heightDifferences_continuous (r : ℕ) : Continuous (heightDifferences r) :=
  (continuous_apply 0).prodMk (continuous_pi (fun j =>
    (continuous_apply j.succ).sub (continuous_apply 0)))

/-- The explicit measurable equivalence and its source free-coordinate inverse. -/
def heightCoordinatesEquiv (r : ℕ) : (ℝ × (Fin r → ℝ)) ≃ᵐ (Fin (r + 1) → ℝ) where
  toFun := heightCoordinates r
  invFun := heightDifferences r
  left_inv := heightDifferences_heightCoordinates r
  right_inv := heightCoordinates_heightDifferences r
  measurable_toFun := (heightCoordinates_continuous r).measurable
  measurable_invFun := (heightDifferences_continuous r).measurable

/-- The common-height coordinate change preserves ordinary product Lebesgue
measure exactly. This proves the paper's free-coordinate Jacobian-one claim. -/
theorem heightCoordinates_measurePreserving (r : ℕ) :
    MeasurePreserving (heightCoordinates r)
      ((volume : Measure ℝ).prod (volume : Measure (Fin r → ℝ)))
      (volume : Measure (Fin (r + 1) → ℝ)) := by
  have hshear : MeasurePreserving
      (fun p : ℝ × (Fin r → ℝ) => (p.1, fun j => p.1 + p.2 j))
      ((volume : Measure ℝ).prod (volume : Measure (Fin r → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin r → ℝ))) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun (s : ℝ) (h : Fin r → ℝ) j => s + h j)
    · exact (continuous_pi (fun j =>
        continuous_fst.add ((continuous_apply j).comp continuous_snd))).measurable
    · exact Filter.Eventually.of_forall (fun s =>
        (measurePreserving_add_left (volume : Measure (Fin r → ℝ)) (fun _ => s)).map_eq)
  have hsplit := volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) 0
  have hcons := MeasurePreserving.symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) 0) hsplit
  convert hcons.comp hshear using 1
  ext p j
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero, heightCoordinates, Equiv.coe_fn_mk, cast_eq]

theorem heightDifferences_measurePreserving (r : ℕ) :
    MeasurePreserving (heightDifferences r) (volume : Measure (Fin (r + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin r → ℝ))) :=
  MeasurePreserving.symm (heightCoordinatesEquiv r) (heightCoordinates_measurePreserving r)

/-- Tonelli disintegration, with the common shift integrated first. -/
theorem heightCoordinates_lintegral (r : ℕ) (F : (Fin (r + 1) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ h, F h ∂(volume : Measure (Fin (r + 1) → ℝ))) =
      ∫⁻ delta : Fin r → ℝ, ∫⁻ s : ℝ, F (heightCoordinates r (s, delta)) := by
  rw [← (heightCoordinates_measurePreserving r).lintegral_comp hF]
  exact lintegral_prod_symm _
    (hF.comp (heightCoordinates_continuous r).measurable).aemeasurable

/-- Antichains are unchanged by a common shift of all heights. The scale
parameter is explicit and need not be assumed positive for this identity. -/
theorem commonHeightShift_antichain_iff {κ ι : Type*} (f : κ → ι → ℝ)
    (h : κ → ℝ) (s q : ℝ) :
    IsAntichain (fun j i => f j i + (s + h j) / q) ↔
      IsAntichain (fun j i => f j i + h j / q) := by
  have heq : (fun j i => f j i + (s + h j) / q) =
      (fun j i => s / q + (f j i + h j / q)) := by
    funext j i
    ring
  rw [heq]
  exact isAntichain_translate_iff _ (fun _ => s / q)

theorem heightCoordinates_eq_shift_cons_zero (r : ℕ) (s : ℝ) (delta : Fin r → ℝ) :
    heightCoordinates r (s, delta) =
      fun j => s + (Fin.cons (0 : ℝ) delta : Fin (r + 1) → ℝ) j := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · rfl

variable {ι : Type*} [Fintype ι]

/-- The actual unpinned point cloud above prescribed native Euclidean floors. -/
def fullHeightPointCloud {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (h : Fin (r + 1) → ℝ) : Fin (r + 1) → ι → ℝ :=
  fun j i => (f j).val i + h j / Real.sqrt (Fintype.card ι : ℝ)

theorem heightCoordinates_antichain_iff {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (s : ℝ) (delta : Fin r → ℝ) :
    IsAntichain (fullHeightPointCloud f (heightCoordinates r (s, delta))) ↔
      IsAntichain (pinnedPointCloud (f, delta)) := by
  rw [heightCoordinates_eq_shift_cons_zero]
  exact commonHeightShift_antichain_iff (fun j i => (f j).val i)
    (Fin.cons 0 delta) s (Real.sqrt (Fintype.card ι : ℝ))

def antichainHeightFiber {r : ℕ} (f : Fin (r + 1) → FloorSpace ι) :
    Set (Fin (r + 1) → ℝ) := {h | IsAntichain (fullHeightPointCloud f h)}

def pinnedHeightFiber {r : ℕ} (f : Fin (r + 1) → FloorSpace ι) :
    Set (Fin r → ℝ) := {delta | IsAntichain (pinnedPointCloud (f, delta))}

theorem measurableSet_antichainHeightFiber {r : ℕ}
    (f : Fin (r + 1) → FloorSpace ι) : MeasurableSet (antichainHeightFiber f) := by
  apply measurableSet_isAntichain (fun h => fullHeightPointCloud f h)
  intro j i
  exact (continuous_const.add ((continuous_apply j).div_const _)).measurable

theorem measurableSet_pinnedHeightFiber {r : ℕ}
    (f : Fin (r + 1) → FloorSpace ι) : MeasurableSet (pinnedHeightFiber f) := by
  apply measurableSet_isAntichain (fun delta => pinnedPointCloud (f, delta))
  intro j i
  exact ((continuous_pinnedPointCloud_apply j i).comp
    (continuous_const.prodMk continuous_id)).measurable

theorem heightCoordinates_mem_antichainHeightFiber_iff {r : ℕ}
    (f : Fin (r + 1) → FloorSpace ι) (s : ℝ) (delta : Fin r → ℝ) :
    heightCoordinates r (s, delta) ∈ antichainHeightFiber f ↔ delta ∈ pinnedHeightFiber f :=
  heightCoordinates_antichain_iff f s delta

/-- Exact disintegration of an arbitrary measurable nonnegative weight over
the actual height fiber into free pinned differences and common translation. -/
theorem antichainHeightFiber_lintegral {r : ℕ} (f : Fin (r + 1) → FloorSpace ι)
    (W : (Fin (r + 1) → ℝ) → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ h in antichainHeightFiber f, W h) =
      ∫⁻ delta in pinnedHeightFiber f, ∫⁻ s : ℝ, W (heightCoordinates r (s, delta)) := by
  calc
    (∫⁻ h in antichainHeightFiber f, W h) =
        ∫⁻ delta : Fin r → ℝ, ∫⁻ s : ℝ,
          (antichainHeightFiber f).indicator W (heightCoordinates r (s, delta)) := by
      rw [← lintegral_indicator (measurableSet_antichainHeightFiber f)]
      exact heightCoordinates_lintegral r _ (hW.indicator (measurableSet_antichainHeightFiber f))
    _ = _ := by
      rw [← lintegral_indicator (measurableSet_pinnedHeightFiber f)]
      apply lintegral_congr
      intro delta
      by_cases hdelta : delta ∈ pinnedHeightFiber f
      · rw [Set.indicator_of_mem hdelta]
        apply lintegral_congr
        intro s
        exact Set.indicator_of_mem
          ((heightCoordinates_mem_antichainHeightFiber_iff f s delta).mpr hdelta) W
      · rw [Set.indicator_of_notMem hdelta]
        calc
          (∫⁻ s : ℝ, (antichainHeightFiber f).indicator W (heightCoordinates r (s, delta))) =
              ∫⁻ _ : ℝ, (0 : ℝ≥0∞) := by
            apply lintegral_congr
            intro s
            exact Set.indicator_of_notMem
              (fun hmem => hdelta ((heightCoordinates_mem_antichainHeightFiber_iff f s delta).mp hmem)) W
          _ = 0 := by simp

/-- The actual pinned mass equals the integral of the free-height fiber
volumes, with the induced Euclidean floor product measure used in the paper. -/
theorem pinnedMass_eq_lintegral_pinnedHeightFiber {B : Set (FloorSpace ι)}
    (hB : MeasurableSet B) (r : ℕ) :
    pinnedMass B r =
      ∫⁻ f in Set.univ.pi (fun _ : Fin (r + 1) => B),
        (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) := by
  change ((volume : Measure (Fin (r + 1) → FloorSpace ι)).prod
    (volume : Measure (Fin r → ℝ))) (pinnedAntichainSet B r) = _
  rw [Measure.prod_apply (measurableSet_pinnedAntichainSet hB r),
    ← lintegral_indicator (MeasurableSet.univ_pi (fun _ : Fin (r + 1) => hB))]
  apply lintegral_congr
  intro f
  by_cases hf : ∀ j, f j ∈ B
  · have hmem : f ∈ Set.univ.pi (fun _ : Fin (r + 1) => B) := by simpa using hf
    rw [Set.indicator_of_mem hmem]
    congr 1
    ext delta
    simp [pinnedAntichainSet, hf, pinnedHeightFiber]
  · have hmem : f ∉ Set.univ.pi (fun _ : Fin (r + 1) => B) := by simpa using hf
    rw [Set.indicator_of_notMem hmem]
    have hempty : Prod.mk f ⁻¹' pinnedAntichainSet B r = ∅ := by
      ext delta
      simp only [Set.mem_preimage, pinnedAntichainSet, Set.mem_setOf_eq, hf,
        false_and, Set.notMem_empty]
    rw [hempty, measure_empty]

end Antichain
