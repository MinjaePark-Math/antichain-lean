import Antichain.GaussianWeighted
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual sample-size deletion bounds for the weighted antichain model. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def singlePointWeight (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (g : CubePoint d) : ℝ :=
  Real.exp (sigma (actualFloor g) + c * actualHeight g ^ 2)

@[fun_prop] theorem singlePointWeight_continuous
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    Continuous (singlePointWeight sigma c) := by
  unfold singlePointWeight
  fun_prop

def unrestrictedSinglePointMass (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (singlePointWeight sigma c g) ∂gaussianPointLaw d

theorem unrestrictedSinglePointMass_eq_partition_one
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    unrestrictedSinglePointMass sigma c = weightedPartitionMass 1 sigma c := by
  have h := (measurePreserving_funUnique (gaussianPointLaw d) (Fin 1)).lintegral_comp
    (singlePointWeight_continuous sigma c).measurable.ennreal_ofReal
  rw [weightedPartitionMass, strictAntichainEvent_one, Measure.restrict_univ]
  symm
  convert h using 1
  apply lintegral_congr
  intro g
  simp [gaussianWeight, gaussianWeightExponent, singlePointWeight,
    MeasurableEquiv.funUnique]

theorem unrestrictedSinglePointMass_lt_top
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    unrestrictedSinglePointMass sigma c < ⊤ := by
  rw [unrestrictedSinglePointMass_eq_partition_one]
  exact weightedPartitionMass_lt_top 1 sigma c hc

theorem unrestrictedSinglePointMass_pos (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    0 < unrestrictedSinglePointMass sigma c := by
  rw [unrestrictedSinglePointMass_eq_partition_one]
  exact weightedPartitionMass_pos 1 sigma c hd

omit [NeZero d] in
theorem strictAntichainEvent_tail (n : ℕ) (g : CubeSample (n + 1) d)
    (hg : g ∈ strictAntichainEvent (n + 1) d) :
    (fun j : Fin n => g j.succ) ∈ strictAntichainEvent n d := by
  intro j k hjk
  exact hg j.succ k.succ (fun h => hjk (Fin.succ_inj.mp h))

theorem gaussianWeight_cons (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (x : CubePoint d) (g : CubeSample n d) :
    gaussianWeight (n + 1) sigma c (Fin.cons x g) =
      singlePointWeight sigma c x * gaussianWeight n sigma c g := by
  simp only [gaussianWeight, gaussianWeightExponent, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, singlePointWeight, Real.exp_add]

/-- Deleting one point drops genuine antichain constraints. The factor is the
actual unrestricted one-point weighted integral, not a supplied estimate. -/
theorem weightedPartitionMass_succ_le (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartitionMass (n + 1) sigma c ≤
      unrestrictedSinglePointMass sigma c * weightedPartitionMass n sigma c := by
  let F : CubeSample (n + 1) d → ℝ≥0∞ :=
    (strictAntichainEvent (n + 1) d).indicator
      (fun g => ENNReal.ofReal (gaussianWeight (n + 1) sigma c g))
  have hF : Measurable F :=
    (gaussianWeight_continuous (n + 1) sigma c).measurable.ennreal_ofReal.indicator
      (measurableSet_strictAntichainEvent (n + 1) d)
  have hsplit := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => gaussianPointLaw d) 0).symm.lintegral_comp hF
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero] at hsplit
  change (∫⁻ p : CubePoint d × CubeSample n d, F (Fin.cons p.1 p.2)
    ∂(gaussianPointLaw d).prod (gaussianSampleLaw n d)) =
      ∫⁻ g, F g ∂gaussianSampleLaw (n + 1) d at hsplit
  rw [weightedPartitionMass,
    ← lintegral_indicator (measurableSet_strictAntichainEvent (n + 1) d)]
  change (∫⁻ g, F g ∂gaussianSampleLaw (n + 1) d) ≤ _
  rw [← hsplit]
  calc
    _ ≤ ∫⁻ p : CubePoint d × CubeSample n d,
        ENNReal.ofReal (singlePointWeight sigma c p.1) *
          (strictAntichainEvent n d).indicator
            (fun g => ENNReal.ofReal (gaussianWeight n sigma c g)) p.2
          ∂(gaussianPointLaw d).prod (gaussianSampleLaw n d) := by
      apply lintegral_mono
      intro p
      change F (Fin.cons p.1 p.2) ≤ _
      by_cases hp : Fin.cons p.1 p.2 ∈ strictAntichainEvent (n + 1) d
      · have ht : p.2 ∈ strictAntichainEvent n d := by
          simpa only [Fin.cons_succ] using strictAntichainEvent_tail n _ hp
        simp only [F, Set.indicator_of_mem hp, Set.indicator_of_mem ht, gaussianWeight_cons]
        rw [ENNReal.ofReal_mul (show 0 ≤ singlePointWeight sigma c p.1 from Real.exp_nonneg _)]
      · simp only [F, Set.indicator_of_notMem hp]
        exact zero_le _
    _ = _ := by
      have hG : Measurable (fun p : CubePoint d × CubeSample n d =>
          ENNReal.ofReal (singlePointWeight sigma c p.1) *
            (strictAntichainEvent n d).indicator
              (fun g => ENNReal.ofReal (gaussianWeight n sigma c g)) p.2) := by
        exact ((singlePointWeight_continuous sigma c).measurable.ennreal_ofReal.comp
          measurable_fst).mul (((gaussianWeight_continuous n sigma c).measurable.ennreal_ofReal.indicator
          (measurableSet_strictAntichainEvent n d)).comp measurable_snd)
      rw [lintegral_prod _ hG.aemeasurable]
      rw [lintegral_lintegral_mul
        (singlePointWeight_continuous sigma c).measurable.ennreal_ofReal.aemeasurable
        (((gaussianWeight_continuous n sigma c).measurable.ennreal_ofReal.indicator
          (measurableSet_strictAntichainEvent n d)).aemeasurable),
        lintegral_indicator (measurableSet_strictAntichainEvent n d)]
      rfl

theorem weightedPartitionMass_add_le (n k : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartitionMass (n + k) sigma c ≤
      unrestrictedSinglePointMass sigma c ^ k * weightedPartitionMass n sigma c := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ ≤ unrestrictedSinglePointMass sigma c * weightedPartitionMass (n + k) sigma c :=
        weightedPartitionMass_succ_le (n + k) sigma c
      _ ≤ unrestrictedSinglePointMass sigma c *
          (unrestrictedSinglePointMass sigma c ^ k * weightedPartitionMass n sigma c) :=
        mul_le_mul_left' ih _
      _ = _ := by rw [pow_succ]; ac_rfl

/-- Ordinary-real form of the actual sample-size comparison. All involved
nonnegative integrals are proved finite before taking real values. -/
theorem weightedPartition_add_le (n k : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    weightedPartition (n + k) sigma c ≤
      (unrestrictedSinglePointMass sigma c).toReal ^ k * weightedPartition n sigma c := by
  have hfinite : unrestrictedSinglePointMass sigma c ^ k *
      weightedPartitionMass n sigma c ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (unrestrictedSinglePointMass_lt_top sigma c hc).ne)
      (weightedPartitionMass_lt_top n sigma c hc).ne
  have h := ENNReal.toReal_mono hfinite (weightedPartitionMass_add_le n k sigma c)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, weightedPartition] using h

theorem weightedPartition_deletion_lower (hd : 2 ≤ d) (n N : ℕ) (hnN : n ≤ N)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    ((unrestrictedSinglePointMass sigma c).toReal ^ (N - n))⁻¹ *
      weightedPartition N sigma c ≤ weightedPartition n sigma c := by
  have hm : 0 < (unrestrictedSinglePointMass sigma c).toReal :=
    ENNReal.toReal_pos (unrestrictedSinglePointMass_pos hd sigma c).ne'
      (unrestrictedSinglePointMass_lt_top sigma c hc).ne
  have h := weightedPartition_add_le n (N - n) sigma c hc
  rw [Nat.add_sub_of_le hnN] at h
  calc
    _ ≤ ((unrestrictedSinglePointMass sigma c).toReal ^ (N - n))⁻¹ *
        ((unrestrictedSinglePointMass sigma c).toReal ^ (N - n) * weightedPartition n sigma c) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg hm.le _))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (pow_pos hm _).ne', one_mul]

end Antichain
