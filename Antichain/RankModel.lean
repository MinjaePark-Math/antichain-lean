import Antichain.CubeModel
import Antichain.ProductTranspose
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.WellFounded
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
The literal rank permutations of uniform real-coordinate samples. Ties are
assigned a measurable fallback; all probability conclusions remove that null
set using the actual independent restricted-volume sample law.
-/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

instance rankPermutationMeasurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance rankPermutationMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem exists_strictly_sorted_permutation {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (fun j => x (e j)) := by
  classical
  let e : Fin n ≃ Set.range x := Equiv.ofInjective x hx
  letI : Fintype (Set.range x) := Fintype.ofEquiv (Fin n) e
  have hc : Fintype.card (Set.range x) = n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  let o : Fin n ≃o Set.range x := Fintype.orderIsoFinOfCardEq _ hc
  refine ⟨o.toEquiv.trans e.symm, ?_⟩
  have hval (j : Fin n) : x ((o.toEquiv.trans e.symm) j) = (o j).val := by
    exact congrArg Subtype.val (e.apply_symm_apply (o j))
  simpa only [hval] using o.strictMono

theorem strictly_sorted_permutation_unique {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (e f : Equiv.Perm (Fin n))
    (he : StrictMono (fun j => x (e j))) (hf : StrictMono (fun j => x (f j))) : e = f := by
  have hr : Set.range (fun j => x (e j)) = Set.range (fun j => x (f j)) := by
    rw [show (fun j => x (e j)) = x ∘ e from rfl,
      show (fun j => x (f j)) = x ∘ f from rfl,
      Set.range_comp, Set.range_comp, Set.range_eq_univ.mpr e.surjective,
      Set.range_eq_univ.mpr f.surjective]
  have hfun := (he.range_inj hf).mp hr
  exact Equiv.ext (fun j => hx (congrFun hfun j))

/-- The permutation taking increasing positions to their original labels. -/
def sampleSortPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  if hx : Function.Injective x then (exists_strictly_sorted_permutation x hx).choose
  else Equiv.refl _

theorem sampleSortPermutation_strictMono {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) : StrictMono (fun j => x (sampleSortPermutation x j)) := by
  unfold sampleSortPermutation
  rw [dif_pos hx]
  exact (exists_strictly_sorted_permutation x hx).choose_spec

theorem sampleSortPermutation_eq_iff {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (e : Equiv.Perm (Fin n)) :
    sampleSortPermutation x = e ↔ StrictMono (fun j => x (e j)) := by
  constructor
  · intro h
    simpa only [← h] using sampleSortPermutation_strictMono x hx
  · exact strictly_sorted_permutation_unique x hx _ e (sampleSortPermutation_strictMono x hx)

theorem measurableSet_scalarInjective (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | Function.Injective x} := by
  classical
  unfold Function.Injective
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun k => ?_))
  by_cases h : j = k
  · simp only [h, implies_true, Set.setOf_true]
    exact MeasurableSet.univ
  · simp only [h, imp_false]
    exact (measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply k)).compl

theorem measurableSet_sortChamber {n : ℕ} (e : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | StrictMono (fun j => x (e j))} := by
  unfold StrictMono
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter
    (fun k => MeasurableSet.iInter (fun _ => measurableSet_lt
      (measurable_pi_apply (e j)) (measurable_pi_apply (e k)))))

theorem sampleSortPermutation_measurable (n : ℕ) :
    Measurable (sampleSortPermutation : (Fin n → ℝ) → Equiv.Perm (Fin n)) := by
  classical
  apply measurable_to_countable'
  intro e
  have heq : sampleSortPermutation ⁻¹' {e} =
      ({x | Function.Injective x} ∩ {x | StrictMono (fun j => x (e j))}) ∪
        ({x | ¬ Function.Injective x} ∩ {x | Equiv.refl (Fin n) = e}) := by
    ext x
    by_cases hx : Function.Injective x
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
        Set.mem_setOf_eq, hx, true_and, not_true_eq_false, false_and, or_false]
      exact sampleSortPermutation_eq_iff x hx e
    · simp [sampleSortPermutation, hx]
  rw [heq]
  exact ((measurableSet_scalarInjective n).inter (measurableSet_sortChamber e)).union
    ((measurableSet_scalarInjective n).compl.inter (by by_cases h : Equiv.refl (Fin n) = e <;> simp [h]))

/-- A label's zero-based coordinate rank. -/
def sampleRankPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  (sampleSortPermutation x).symm

theorem sampleRankPermutation_measurable (n : ℕ) :
    Measurable (sampleRankPermutation : (Fin n → ℝ) → Equiv.Perm (Fin n)) :=
  (measurable_of_finite (fun e : Equiv.Perm (Fin n) => e.symm)).comp
    (sampleSortPermutation_measurable n)

/-- Actual sorted coordinate values; on the null tie set a measurable fallback
still yields a total function. -/
def sampleSortedValues {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x (sampleSortPermutation x j)

theorem sampleSortedValues_measurable (n : ℕ) :
    Measurable (sampleSortedValues : (Fin n → ℝ) → (Fin n → ℝ)) := by
  apply measurable_pi_iff.mpr
  intro j
  have heval : Measurable (fun p : (Fin n → ℝ) × Equiv.Perm (Fin n) => p.1 (p.2 j)) :=
    measurable_from_prod_countable_left (fun e => measurable_pi_apply (e j))
  exact heval.comp (measurable_id.prodMk (sampleSortPermutation_measurable n))

theorem sampleRankPermutation_lt_iff {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (j k : Fin n) :
    sampleRankPermutation x j < sampleRankPermutation x k ↔ x j < x k := by
  have h := (sampleSortPermutation_strictMono x hx).lt_iff_lt
    (a := (sampleSortPermutation x).symm j) (b := (sampleSortPermutation x).symm k)
  simpa only [sampleRankPermutation, Equiv.apply_symm_apply] using
    h.symm

theorem sampleSortPermutation_comp_perm {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (e : Equiv.Perm (Fin n)) :
    sampleSortPermutation (fun j => x (e j)) = (sampleSortPermutation x).trans e.symm := by
  apply (sampleSortPermutation_eq_iff _ (hx.comp e.injective) _).mpr
  simpa only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] using
    sampleSortPermutation_strictMono x hx

theorem sampleRankPermutation_comp_perm {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (e : Equiv.Perm (Fin n)) :
    sampleRankPermutation (fun j => x (e j)) = e.trans (sampleRankPermutation x) := by
  unfold sampleRankPermutation
  rw [sampleSortPermutation_comp_perm x hx e]
  rfl

theorem sampleSortedValues_comp_perm {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (e : Equiv.Perm (Fin n)) :
    sampleSortedValues (fun j => x (e j)) = sampleSortedValues x := by
  funext j
  simp only [sampleSortedValues, sampleSortPermutation_comp_perm x hx e,
    Equiv.trans_apply, Equiv.apply_symm_apply]

/-- Independent draws from an atomless scalar law have no ties. -/
theorem iid_scalar_injective_ae (n : ℕ) (mu : Measure ℝ) [IsProbabilityMeasure mu]
    [NoAtoms mu] :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => mu), Function.Injective x := by
  have hind := iIndepFun_pi (fun _ : Fin n => (measurable_id (α := ℝ)).aemeasurable (μ := mu))
  have hdiagmeas : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hdiag : (mu.prod mu) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    apply Measure.measure_prod_null_of_ae_null hdiagmeas
    apply Filter.Eventually.of_forall
    intro a
    change mu {b : ℝ | a = b} = 0
    simpa only [Set.setOf_eq_eq_singleton'] using (measure_singleton a : mu {a} = 0)
  have hpair (j k : Fin n) :
      ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => mu), j ≠ k → x j ≠ x k := by
    by_cases hjk : j = k
    · exact Filter.Eventually.of_forall (fun _ h => (h hjk).elim)
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply j).aemeasurable (measurable_pi_apply k).aemeasurable).mp
        (hind.indepFun hjk)
    rw [(measurePreserving_eval (fun _ : Fin n => mu) j).map_eq,
      (measurePreserving_eval (fun _ : Fin n => mu) k).map_eq] at hmap
    have hzero : (Measure.pi (fun _ : Fin n => mu)) {x | x j = x k} = 0 := by
      have hm := Measure.map_apply (μ := Measure.pi (fun _ : Fin n => mu))
        ((measurable_pi_apply j).prodMk (measurable_pi_apply k)) hdiagmeas
      change Measure.map (fun x : Fin n → ℝ => (x j, x k)) (Measure.pi (fun _ => mu))
        {p : ℝ × ℝ | p.1 = p.2} = (Measure.pi (fun _ : Fin n => mu)) {x | x j = x k} at hm
      rw [← hm, hmap, hdiag]
    have ha : ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => mu), x j ≠ x k := by
      rw [ae_iff]
      simpa only [not_not] using hzero
    exact ha.mono (fun _ h _ => h)
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => hpair j k))] with x hx
  intro j k heq
  by_contra hjk
  exact hx j k hjk heq

instance cubeCoordinateLaw_noAtoms : NoAtoms cubeCoordinateLaw := by
  unfold cubeCoordinateLaw
  infer_instance

def CoordinateTieFree (n d : ℕ) (x : CubeSample n d) : Prop :=
  ∀ i : Fin d, Function.Injective (fun j => x j i)

theorem measurableSet_coordinateTieFree (n d : ℕ) :
    MeasurableSet {x : CubeSample n d | CoordinateTieFree n d x} := by
  unfold CoordinateTieFree
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurableSet_scalarInjective n).preimage
    (measurable_pi_iff.mpr (fun j => (measurable_pi_apply i).comp (measurable_pi_apply j))))

/-- The actual independent uniform cube sample has no coordinate ties. -/
theorem cubeSample_coordinateTieFree_ae (n d : ℕ) :
    ∀ᵐ x ∂cubeSampleLaw n d, CoordinateTieFree n d x := by
  have hcols : ∀ᵐ y : Fin d → Fin n → ℝ
      ∂Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin n => cubeCoordinateLaw)),
      ∀ i, Function.Injective (y i) := by
    apply ae_all_iff.mpr
    intro i
    have h := iid_scalar_injective_ae n cubeCoordinateLaw
    rw [← (measurePreserving_eval
      (fun _ : Fin d => Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) i).map_eq] at h
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable (measurableSet_scalarInjective n)).mp h
  have hmp := measurePreserving_iid_transpose (I := Fin n) (J := Fin d) cubeCoordinateLaw
  rw [← hmp.map_eq] at hcols
  have hpred : MeasurableSet {y : Fin d → Fin n → ℝ | ∀ i, Function.Injective (y i)} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => (measurableSet_scalarInjective n).preimage
      (measurable_pi_apply i))
  exact (ae_map_iff hmp.measurable.aemeasurable hpred).mp hcols

def coordinateRankPermutations (n d : ℕ) (x : CubeSample n d) :
    Fin d → Equiv.Perm (Fin n) := fun i => sampleRankPermutation (fun j => x j i)

def coordinateSortedValues (n d : ℕ) (x : CubeSample n d) : Fin d → Fin n → ℝ :=
  fun i => sampleSortedValues (fun j => x j i)

theorem coordinateRankPermutations_measurable (n d : ℕ) :
    Measurable (coordinateRankPermutations n d) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (sampleRankPermutation_measurable n).comp
    (measurable_pi_iff.mpr (fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)))

theorem coordinateSortedValues_measurable (n d : ℕ) :
    Measurable (coordinateSortedValues n d) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (sampleSortedValues_measurable n).comp
    (measurable_pi_iff.mpr (fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)))

end Antichain
