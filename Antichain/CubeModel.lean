import Antichain.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
The actual finite independent uniform cube sample and strict-antichain event.
The probability is defined from product restricted Lebesgue measure; positivity
is proved from a nonempty open family of oppositely ordered configurations.
-/

namespace Antichain

open MeasureTheory Set
open scoped ENNReal

abbrev CubePoint (d : ℕ) := Fin d → ℝ
abbrev CubeSample (n d : ℕ) := Fin n → CubePoint d

/-- The actual uniform probability measure on the closed unit interval. -/
noncomputable def cubeCoordinateLaw : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

instance cubeCoordinateLaw_isProbabilityMeasure : IsProbabilityMeasure cubeCoordinateLaw where
  measure_univ := by
    simp [cubeCoordinateLaw, Real.volume_Icc]

/-- Independent uniform coordinates in a cube point. -/
noncomputable def cubePointLaw (d : ℕ) : Measure (CubePoint d) :=
  Measure.pi (fun _ : Fin d => cubeCoordinateLaw)

instance cubePointLaw_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (cubePointLaw d) := by
  unfold cubePointLaw
  infer_instance

/-- Independent labelled cube points, with independent coordinates. -/
noncomputable def cubeSampleLaw (n d : ℕ) : Measure (CubeSample n d) :=
  Measure.pi (fun _ : Fin n => cubePointLaw d)

instance cubeSampleLaw_isProbabilityMeasure (n d : ℕ) :
    IsProbabilityMeasure (cubeSampleLaw n d) := by
  unfold cubeSampleLaw
  infer_instance

def cubePointSet (d : ℕ) : Set (CubePoint d) :=
  Set.univ.pi (fun _ : Fin d => Icc (0 : ℝ) 1)

def cubeSampleSet (n d : ℕ) : Set (CubeSample n d) :=
  Set.univ.pi (fun _ : Fin n => cubePointSet d)

theorem measurableSet_cubePointSet (d : ℕ) : MeasurableSet (cubePointSet d) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem measurableSet_cubeSampleSet (n d : ℕ) : MeasurableSet (cubeSampleSet n d) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_cubePointSet d)

/-- Each labelled point has the actual independent-coordinate uniform law. -/
theorem measurePreserving_cubePoint (n d : ℕ) (j : Fin n) :
    MeasurePreserving (fun x : CubeSample n d => x j)
      (cubeSampleLaw n d) (cubePointLaw d) :=
  measurePreserving_eval (fun _ : Fin n => cubePointLaw d) j

/-- Each sample coordinate has the actual uniform interval law. -/
theorem measurePreserving_cubeCoordinate (n d : ℕ) (j : Fin n) (i : Fin d) :
    MeasurePreserving (fun x : CubeSample n d => x j i)
      (cubeSampleLaw n d) cubeCoordinateLaw :=
  (measurePreserving_eval (fun _ : Fin d => cubeCoordinateLaw) i).comp
    (measurePreserving_cubePoint n d j)

/-- The cube product law is precisely restricted Euclidean product volume. -/
theorem cubePointLaw_eq_volume_restrict (d : ℕ) :
    cubePointLaw d = (volume : Measure (CubePoint d)).restrict (cubePointSet d) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin d => (volume : Measure ℝ))
    (fun _ : Fin d => Icc (0 : ℝ) 1)).symm

theorem cubeSampleLaw_eq_volume_restrict (n d : ℕ) :
    cubeSampleLaw n d =
      (volume : Measure (CubeSample n d)).restrict (cubeSampleSet n d) := by
  unfold cubeSampleLaw
  simp_rw [cubePointLaw_eq_volume_restrict]
  exact (Measure.restrict_pi_pi (fun _ : Fin n => (volume : Measure (CubePoint d)))
    (fun _ : Fin n => cubePointSet d)).symm

theorem ae_cubeSample_mem_cube (n d : ℕ) :
    ∀ᵐ x ∂cubeSampleLaw n d, x ∈ cubeSampleSet n d := by
  rw [cubeSampleLaw_eq_volume_restrict]
  exact ae_restrict_mem (measurableSet_cubeSampleSet n d)

/-- The paper's antichain event: comparisons are strict in every coordinate. -/
def strictAntichainEvent (n d : ℕ) : Set (CubeSample n d) :=
  {x | IsAntichain x}

theorem isClosed_strictAntichainEvent (n d : ℕ) :
    IsClosed (strictAntichainEvent n d) := by
  have hcoord (j : Fin n) (i : Fin d) :
      Continuous (fun x : CubeSample n d => x j i) :=
    (continuous_apply i).comp (continuous_apply j)
  have hpair (j k : Fin n) :
      IsClosed {x : CubeSample n d | ¬ StrictBelow (x j) (x k)} := by
    apply IsOpen.isClosed_compl
    change IsOpen {x : CubeSample n d | ∀ i, x j i < x k i}
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (hcoord j i) (hcoord k i))
  unfold strictAntichainEvent IsAntichain
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun j => isClosed_iInter
    (fun k => isClosed_iInter (fun _ => hpair j k)))

theorem measurableSet_strictAntichainEvent (n d : ℕ) :
    MeasurableSet (strictAntichainEvent n d) :=
  (isClosed_strictAntichainEvent n d).measurableSet

/-- Measurability of the same strict-antichain predicate for any countable
labelled measurable real-coordinate family, independent of the cube law. -/
theorem measurableSet_isAntichain {Ω κ ι : Type*} [MeasurableSpace Ω]
    [Countable κ] [Countable ι] (x : Ω → κ → ι → ℝ)
    (hx : ∀ j i, Measurable (fun ω => x ω j i)) :
    MeasurableSet {ω | IsAntichain (x ω)} := by
  unfold IsAntichain StrictBelow
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun k =>
    MeasurableSet.iInter (fun _ => ?_)))
  have h : MeasurableSet {ω | ∀ i, x ω j i < x ω k i} := by
    simpa only [Set.setOf_forall] using
      MeasurableSet.iInter (fun i => measurableSet_lt (hx j i) (hx k i))
  exact h.compl

/-- Extended-real mass, kept separate from its real-valued version. -/
noncomputable def antichainMass (n d : ℕ) : ℝ≥0∞ :=
  cubeSampleLaw n d (strictAntichainEvent n d)

/-- The real probability `a_n` used in the paper's logarithms. -/
noncomputable def antichainProbability (n d : ℕ) : ℝ :=
  (antichainMass n d).toReal

theorem antichainMass_eq_event_measure (n d : ℕ) :
    antichainMass n d = cubeSampleLaw n d (strictAntichainEvent n d) := rfl

theorem antichainProbability_eq_event_measure_toReal (n d : ℕ) :
    antichainProbability n d =
      (cubeSampleLaw n d (strictAntichainEvent n d)).toReal := rfl

theorem antichainMass_le_one (n d : ℕ) : antichainMass n d ≤ 1 :=
  prob_le_one

theorem antichainMass_ne_top (n d : ℕ) : antichainMass n d ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (antichainMass_le_one n d)

theorem antichainProbability_nonneg (n d : ℕ) : 0 ≤ antichainProbability n d :=
  ENNReal.toReal_nonneg

theorem antichainProbability_le_one (n d : ℕ) : antichainProbability n d ≤ 1 := by
  have h := (ENNReal.toReal_le_toReal (antichainMass_ne_top n d) ENNReal.one_ne_top).mpr
    (antichainMass_le_one n d)
  simpa [antichainProbability] using h

theorem strictAntichainEvent_zero (d : ℕ) : strictAntichainEvent 0 d = Set.univ := by
  ext x
  simp only [strictAntichainEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro j
  exact Fin.elim0 j

theorem strictAntichainEvent_one (d : ℕ) : strictAntichainEvent 1 d = Set.univ := by
  ext x
  simp only [strictAntichainEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro j k hjk
  exact (hjk (Subsingleton.elim j k)).elim

theorem antichainMass_zero (d : ℕ) : antichainMass 0 d = 1 := by
  rw [antichainMass, strictAntichainEvent_zero]
  exact measure_univ

theorem antichainMass_one (d : ℕ) : antichainMass 1 d = 1 := by
  rw [antichainMass, strictAntichainEvent_one]
  exact measure_univ

section Positivity

variable (n d : ℕ) (hd : 2 ≤ d)

private def firstCoordinate : Fin d := ⟨0, by omega⟩
private def secondCoordinate : Fin d := ⟨1, by omega⟩

/-- An explicit open family of interior cube configurations: the first
coordinate increases with the label, and the second decreases. -/
def oppositelyOrderedOpen : Set (CubeSample n d) :=
  {x | (∀ j i, 0 < x j i ∧ x j i < 1) ∧
    ∀ j k, j < k →
      x j (firstCoordinate d hd) < x k (firstCoordinate d hd) ∧
      x k (secondCoordinate d hd) < x j (secondCoordinate d hd)}

theorem isOpen_oppositelyOrderedOpen : IsOpen (oppositelyOrderedOpen n d hd) := by
  have hcoord (j : Fin n) (i : Fin d) :
      Continuous (fun x : CubeSample n d => x j i) :=
    (continuous_apply i).comp (continuous_apply j)
  unfold oppositelyOrderedOpen
  simp only [Set.setOf_and, Set.setOf_forall]
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite (fun j => isOpen_iInter_of_finite (fun i =>
      (isOpen_lt continuous_const (hcoord j i)).inter
        (isOpen_lt (hcoord j i) continuous_const)))
  · exact isOpen_iInter_of_finite (fun j => isOpen_iInter_of_finite (fun k =>
      isOpen_iInter_of_finite (fun _ =>
        (isOpen_lt (hcoord j _) (hcoord k _)).inter
          (isOpen_lt (hcoord k _) (hcoord j _)))))

theorem oppositelyOrderedOpen_subset_cube :
    oppositelyOrderedOpen n d hd ⊆ cubeSampleSet n d := by
  intro x hx j _ i _
  exact ⟨(hx.1 j i).1.le, (hx.1 j i).2.le⟩

theorem oppositelyOrderedOpen_subset_antichain :
    oppositelyOrderedOpen n d hd ⊆ strictAntichainEvent n d := by
  intro x hx j k hjk hbelow
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · exact (not_lt_of_gt (hx.2 j k hlt).2) (hbelow (secondCoordinate d hd))
  · exact (not_lt_of_gt (hx.2 k j hgt).1) (hbelow (firstCoordinate d hd))

/-- Nonemptiness is witnessed by strictly interior, oppositely ordered
coordinates, including the empty sample without a special assumption on n. -/
theorem oppositelyOrderedOpen_nonempty : (oppositelyOrderedOpen n d hd).Nonempty := by
  let p : Fin n → ℝ := fun j => ((j.val : ℝ) + 1) / ((n : ℝ) + 1)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp (j : Fin n) : 0 < p j ∧ p j < 1 := by
    have hj : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    constructor
    · exact div_pos (by positivity) hn
    · apply (div_lt_one hn).mpr
      dsimp [p]
      linarith
  have hmono (j k : Fin n) (hjk : j < k) : p j < p k := by
    have hv : (j.val : ℝ) < k.val := by exact_mod_cast hjk
    apply (div_lt_div_iff_of_pos_right hn).mpr
    linarith
  let x : CubeSample n d := fun j i =>
    if i = firstCoordinate d hd then p j
    else if i = secondCoordinate d hd then 1 - p j else 1 / 2
  have hne : secondCoordinate d hd ≠ firstCoordinate d hd := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [firstCoordinate, secondCoordinate] at hv
  refine ⟨x, ?_, ?_⟩
  · intro j i
    dsimp [x]
    split_ifs
    · exact hp j
    · constructor <;> linarith [(hp j).1, (hp j).2]
    · constructor <;> norm_num
  · intro j k hjk
    have hm := hmono j k hjk
    simp only [x, if_pos rfl, if_neg hne, ite_true]
    constructor
    · exact hm
    · linarith

/-- The exhibited open antichain family has strictly positive actual
uniform-cube probability, not only positive ambient Lebesgue measure. -/
theorem cubeSampleLaw_oppositelyOrderedOpen_pos :
    0 < cubeSampleLaw n d (oppositelyOrderedOpen n d hd) := by
  rw [cubeSampleLaw_eq_volume_restrict,
    Measure.restrict_apply (isOpen_oppositelyOrderedOpen n d hd).measurableSet]
  rw [Set.inter_eq_left.mpr (oppositelyOrderedOpen_subset_cube n d hd)]
  exact (isOpen_oppositelyOrderedOpen n d hd).measure_pos volume
    (oppositelyOrderedOpen_nonempty n d hd)

include hd in
/-- Every finite independent uniform sample has positive antichain
probability in every dimension at least two. -/
theorem antichainMass_pos : 0 < antichainMass n d := by
  exact (cubeSampleLaw_oppositelyOrderedOpen_pos n d hd).trans_le
    (measure_mono (oppositelyOrderedOpen_subset_antichain n d hd))

include hd in
theorem antichainProbability_pos : 0 < antichainProbability n d :=
  ENNReal.toReal_pos (antichainMass_pos n d hd).ne' (antichainMass_ne_top n d)

end Positivity

end Antichain
