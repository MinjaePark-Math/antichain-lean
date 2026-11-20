import Antichain.UniformCDFConcentration
import Antichain.TileProduct
import Antichain.RankCDF
import Antichain.DKWSaddle
import Mathlib.Probability.Martingale.OptionalStopping

/-! Research toward the sharp DKW inequality.  The likelihoods and laws in
this file are defined from the actual iid uniform cube-coordinate measure.
No DKW inequality or reverse-martingale assertion is assumed. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

def dkwCensor (b x : ℝ) : ℝ := max x b

theorem dkwCensor_measurable (b : ℝ) : Measurable (dkwCensor b) :=
  measurable_id.max measurable_const

theorem dkwCensor_comp {a b : ℝ} (hab : a ≤ b) :
    dkwCensor b ∘ dkwCensor a = dkwCensor b := by
  funext x
  simp only [Function.comp_apply, dkwCensor, max_assoc, max_eq_right hab]

def dkwScalarLikelihood (a lambda x : ℝ) : ℝ :=
  1 + lambda / a * uniformCDFIndicator a x

theorem dkwScalarLikelihood_measurable (a lambda : ℝ) :
    Measurable (dkwScalarLikelihood a lambda) :=
  measurable_const.add ((uniformCDFIndicator_measurable a).const_mul _)

theorem dkwScalarLikelihood_nonneg {a lambda : ℝ} (ha : 0 < a) (hl : 0 ≤ lambda)
    (x : ℝ) : 0 ≤ dkwScalarLikelihood a lambda x := by
  unfold dkwScalarLikelihood
  have := (uniformCDFIndicator_mem_Icc a x).1
  positivity

theorem dkwScalarLikelihood_integrable (a lambda : ℝ) :
    Integrable (dkwScalarLikelihood a lambda) cubeCoordinateLaw :=
  (integrable_const _).add
    (((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul _)

def dkwTiltLaw (a lambda : ℝ) : Measure ℝ :=
  cubeCoordinateLaw + ENNReal.ofReal (lambda / a) • cubeCoordinateLaw.restrict (Iic a)

theorem dkwTiltLaw_eq_withDensity {a lambda : ℝ} (ha : 0 < a) (hl : 0 ≤ lambda) :
    dkwTiltLaw a lambda = cubeCoordinateLaw.withDensity
      (fun x => ENNReal.ofReal (dkwScalarLikelihood a lambda x)) := by
  have hfun : (fun x => ENNReal.ofReal (dkwScalarLikelihood a lambda x)) =
      (fun x => 1 + ENNReal.ofReal (lambda / a) * (Iic a).indicator (fun _ => 1) x) := by
    funext x
    by_cases hx : x ≤ a <;>
      simp [dkwScalarLikelihood, uniformCDFIndicator, hx,
        ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) (div_nonneg hl ha.le)]
  rw [hfun]
  change dkwTiltLaw a lambda = cubeCoordinateLaw.withDensity
    ((1 : ℝ → ℝ≥0∞) + fun x => ENNReal.ofReal (lambda / a) *
      (Iic a).indicator (fun _ => 1) x)
  rw [withDensity_add_left (f := (1 : ℝ → ℝ≥0∞)) measurable_const _, withDensity_one]
  unfold dkwTiltLaw
  congr 1
  change ENNReal.ofReal (lambda / a) • cubeCoordinateLaw.restrict (Iic a) =
    cubeCoordinateLaw.withDensity
      (ENNReal.ofReal (lambda / a) • (Iic a).indicator (1 : ℝ → ℝ≥0∞))
  rw [withDensity_smul (f := (Iic a).indicator (1 : ℝ → ℝ≥0∞))
      _ (measurable_const.indicator measurableSet_Iic),
    withDensity_indicator_one measurableSet_Iic]

theorem dkwCensor_map_restrict {a b : ℝ} (hab : a ≤ b) :
    (cubeCoordinateLaw.restrict (Iic a)).map (dkwCensor b) =
      cubeCoordinateLaw (Iic a) • Measure.dirac b := by
  have hconst : dkwCensor b =ᵐ[cubeCoordinateLaw.restrict (Iic a)] fun _ => b := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact max_eq_right (hx.trans hab)
  rw [Measure.map_congr hconst, Measure.map_const, Measure.restrict_apply_univ]

theorem dkwTiltLaw_censor {a b lambda : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) (hl : 0 ≤ lambda) :
    (dkwTiltLaw a lambda).map (dkwCensor b) =
      cubeCoordinateLaw.map (dkwCensor b) + ENNReal.ofReal lambda • Measure.dirac b := by
  rw [dkwTiltLaw, Measure.map_add _ _ (dkwCensor_measurable b),
    Measure.map_smul, dkwCensor_map_restrict hab, smul_smul,
    cubeCoordinateLaw_Iic, min_eq_left (hab.trans hb),
    ← ENNReal.ofReal_mul (div_nonneg hl ha.le), div_mul_cancel₀ _ ha.ne']

theorem dkwTiltLaw_censor_eq {a b lambda : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) (hl : 0 ≤ lambda) :
    (dkwTiltLaw a lambda).map (dkwCensor b) =
      (dkwTiltLaw b lambda).map (dkwCensor b) := by
  rw [dkwTiltLaw_censor ha hab hb hl,
    dkwTiltLaw_censor (ha.trans_le hab) le_rfl hb hl]

instance dkwTiltLaw_isFiniteMeasure (a lambda : ℝ) : IsFiniteMeasure (dkwTiltLaw a lambda) := by
  unfold dkwTiltLaw
  letI := (cubeCoordinateLaw.restrict (Iic a)).smul_finite (ENNReal.ofReal_ne_top :
    ENNReal.ofReal (lambda / a) ≠ ∞)
  infer_instance

def dkwSampleCensor (n : ℕ) (b : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => dkwCensor b (x j)

theorem dkwSampleCensor_measurable (n : ℕ) (b : ℝ) :
    Measurable (dkwSampleCensor n b) := by
  exact measurable_pi_lambda _ (fun j => (dkwCensor_measurable b).comp (measurable_pi_apply j))

def dkwSampleLikelihood (n : ℕ) (a lambda : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ j, dkwScalarLikelihood a lambda (x j)

theorem dkwSampleLikelihood_measurable (n : ℕ) (a lambda : ℝ) :
    Measurable (dkwSampleLikelihood n a lambda) := by
  unfold dkwSampleLikelihood
  exact Finset.measurable_prod _ (fun j _ =>
    (dkwScalarLikelihood_measurable a lambda).comp (measurable_pi_apply j))

theorem dkwSampleLikelihood_nonneg (n : ℕ) {a lambda : ℝ} (ha : 0 < a)
    (hl : 0 ≤ lambda) (x : Fin n → ℝ) : 0 ≤ dkwSampleLikelihood n a lambda x :=
  Finset.prod_nonneg (fun _ _ => dkwScalarLikelihood_nonneg ha hl _)

theorem dkwSampleLikelihood_integrable (n : ℕ) (a lambda : ℝ) :
    Integrable (dkwSampleLikelihood n a lambda)
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) :=
  Integrable.fintype_prod (fun _ => dkwScalarLikelihood_integrable a lambda)

def dkwSampleTiltLaw (n : ℕ) (a lambda : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => dkwTiltLaw a lambda)

theorem dkwSampleTiltLaw_eq_withDensity (n : ℕ) {a lambda : ℝ}
    (ha : 0 < a) (hl : 0 ≤ lambda) :
    dkwSampleTiltLaw n a lambda =
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)).withDensity
        (fun x => ENNReal.ofReal (dkwSampleLikelihood n a lambda x)) := by
  unfold dkwSampleTiltLaw
  simp_rw [dkwTiltLaw_eq_withDensity ha hl]
  exact pi_withDensity_real cubeCoordinateLaw _ (dkwScalarLikelihood_integrable a lambda)
    (dkwScalarLikelihood_nonneg ha hl)

theorem dkwSampleTiltLaw_censor_eq (n : ℕ) {a b lambda : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1) (hl : 0 ≤ lambda) :
    (dkwSampleTiltLaw n a lambda).map (dkwSampleCensor n b) =
      (dkwSampleTiltLaw n b lambda).map (dkwSampleCensor n b) := by
  unfold dkwSampleTiltLaw dkwSampleCensor
  rw [Measure.pi_map_pi (fun _ => (dkwCensor_measurable b).aemeasurable),
    Measure.pi_map_pi (fun _ => (dkwCensor_measurable b).aemeasurable)]
  simp_rw [dkwTiltLaw_censor_eq ha hab hb hl]

theorem dkwSampleLikelihood_censor_self (n : ℕ) (b lambda : ℝ) :
    dkwSampleLikelihood n b lambda ∘ dkwSampleCensor n b =
      dkwSampleLikelihood n b lambda := by
  funext x
  simp only [Function.comp_apply]
  unfold dkwSampleLikelihood dkwSampleCensor dkwScalarLikelihood
    uniformCDFIndicator dkwCensor
  congr 1
  ext j
  by_cases hx : x j ≤ b <;> simp [hx]

theorem dkwSampleLikelihood_setIntegral_eq (n : ℕ) {a b lambda : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hl : 0 ≤ lambda)
    {s : Set (Fin n → ℝ)}
    (hs : MeasurableSet[(inferInstance : MeasurableSpace (Fin n → ℝ)).comap
      (dkwSampleCensor n b)] s) :
    ∫ x in s, dkwSampleLikelihood n a lambda x
        ∂Measure.pi (fun _ : Fin n => cubeCoordinateLaw) =
      ∫ x in s, dkwSampleLikelihood n b lambda x
        ∂Measure.pi (fun _ : Fin n => cubeCoordinateLaw) := by
  obtain ⟨t, ht, rfl⟩ := hs
  have hs := (dkwSampleCensor_measurable n b) ht
  have hmass (u : ℝ) (hu : 0 < u) :
      dkwSampleTiltLaw n u lambda ((dkwSampleCensor n b) ⁻¹' t) =
        ENNReal.ofReal (∫ x in (dkwSampleCensor n b) ⁻¹' t,
          dkwSampleLikelihood n u lambda x
            ∂Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) := by
    rw [dkwSampleTiltLaw_eq_withDensity n hu hl, withDensity_apply _ hs]
    exact (ofReal_integral_eq_lintegral_ofReal
      ((dkwSampleLikelihood_integrable n u lambda).restrict)
      (Eventually.of_forall (dkwSampleLikelihood_nonneg n hu hl))).symm
  have h := congrArg (fun mu : Measure (Fin n → ℝ) => mu t)
    (dkwSampleTiltLaw_censor_eq n ha hab hb hl)
  dsimp only at h
  rw [Measure.map_apply (dkwSampleCensor_measurable n b) ht,
    Measure.map_apply (dkwSampleCensor_measurable n b) ht,
    hmass a ha, hmass b (ha.trans_le hab)] at h
  have hreal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (dkwSampleLikelihood_nonneg n ha hl)),
    ENNReal.toReal_ofReal (integral_nonneg (dkwSampleLikelihood_nonneg n (ha.trans_le hab) hl))]
    using hreal

def dkwCensorSigma (n : ℕ) (b : ℝ) : MeasurableSpace (Fin n → ℝ) :=
  (inferInstance : MeasurableSpace (Fin n → ℝ)).comap (dkwSampleCensor n b)

theorem dkwCensorSigma_le (n : ℕ) (b : ℝ) :
    dkwCensorSigma n b ≤ (inferInstance : MeasurableSpace (Fin n → ℝ)) :=
  (dkwSampleCensor_measurable n b).comap_le

theorem dkwSampleCensor_comp (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    dkwSampleCensor n b ∘ dkwSampleCensor n a = dkwSampleCensor n b := by
  funext x j
  simp only [Function.comp_apply, dkwSampleCensor, dkwCensor, max_assoc,
    max_eq_right hab]

theorem dkwCensorSigma_antitone (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    dkwCensorSigma n b ≤ dkwCensorSigma n a := by
  have hm : Measurable[dkwCensorSigma n a] (dkwSampleCensor n a) :=
    measurable_iff_comap_le.mpr le_rfl
  have hc := (dkwSampleCensor_measurable n b).comp hm
  rw [dkwSampleCensor_comp n hab] at hc
  exact hc.comap_le

theorem dkwSampleLikelihood_censor_measurable (n : ℕ) (b lambda : ℝ) :
    Measurable[dkwCensorSigma n b] (dkwSampleLikelihood n b lambda) := by
  have hm : Measurable[dkwCensorSigma n b] (dkwSampleCensor n b) :=
    measurable_iff_comap_le.mpr le_rfl
  have hc := (dkwSampleLikelihood_measurable n b lambda).comp hm
  rw [dkwSampleLikelihood_censor_self] at hc
  exact hc

def dkwCensorFiltration (n : ℕ) (b : ℕ → ℝ) (hb : Antitone b) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) where
  seq i := dkwCensorSigma n (b i)
  mono' _ _ hij := dkwCensorSigma_antitone n (hb hij)
  le' i := dkwCensorSigma_le n (b i)

/-- The actual iid-uniform likelihood product is a martingale as the censor
threshold decreases.  Its conditional laws are proved by the tilted pushforward
identity above, rather than assumed binomial or martingale inputs. -/
theorem dkwSampleLikelihood_martingale (n : ℕ) (b : ℕ → ℝ) (hb : Antitone b)
    (hbpos : ∀ i, 0 < b i) (hbone : ∀ i, b i ≤ 1) {lambda : ℝ} (hl : 0 ≤ lambda) :
    Martingale (fun i => dkwSampleLikelihood n (b i) lambda)
      (dkwCensorFiltration n b hb) (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) := by
  apply martingale_of_setIntegral_eq_succ
  · intro i
    exact (dkwSampleLikelihood_censor_measurable n (b i) lambda).stronglyMeasurable
  · intro i
    exact dkwSampleLikelihood_integrable n (b i) lambda
  · intro i s hs
    exact (dkwSampleLikelihood_setIntegral_eq n (hbpos (i + 1))
      (hb (Nat.le_succ i)) (hbone i) hl hs).symm

theorem dkwScalarLikelihood_integral {a lambda : ℝ} (ha : 0 < a) (haone : a ≤ 1) :
    ∫ x, dkwScalarLikelihood a lambda x ∂cubeCoordinateLaw = 1 + lambda := by
  have hi : Integrable (uniformCDFIndicator a) cubeCoordinateLaw :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  unfold dkwScalarLikelihood
  rw [integral_add (integrable_const _) (hi.const_mul _),
    integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul,
    uniformCDFIndicator_integral ⟨ha.le, haone⟩, div_mul_cancel₀ _ ha.ne']

theorem dkwSampleLikelihood_integral (n : ℕ) {a lambda : ℝ}
    (ha : 0 < a) (haone : a ≤ 1) :
    ∫ x, dkwSampleLikelihood n a lambda x
      ∂Measure.pi (fun _ : Fin n => cubeCoordinateLaw) = (1 + lambda) ^ n := by
  unfold dkwSampleLikelihood
  rw [integral_fintype_prod_eq_prod]
  simp_rw [dkwScalarLikelihood_integral ha haone]
  simp

/-- Finite maximal likelihood inequality for the actual iid uniform law.
The threshold and time horizon are arbitrary; the sharp DKW analytic barrier
is a separate deterministic calculation. -/
theorem dkwSampleLikelihood_maximal (n m : ℕ) (b : ℕ → ℝ) (hb : Antitone b)
    (hbpos : ∀ i, 0 < b i) (hbone : ∀ i, b i ≤ 1) {lambda : ℝ} (hl : 0 ≤ lambda)
    (c : ℝ≥0) :
    (c : ℝ≥0∞) * (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      {x | ∃ i ≤ m, (c : ℝ) ≤ dkwSampleLikelihood n (b i) lambda x} ≤
        ENNReal.ofReal ((1 + lambda) ^ n) := by
  have hm := maximal_ineq (dkwSampleLikelihood_martingale n b hb hbpos hbone hl).submartingale
    (show 0 ≤ (fun i => dkwSampleLikelihood n (b i) lambda) from
      fun i x => dkwSampleLikelihood_nonneg n (hbpos i) hl x) (ε := c) m
  have hset : {x | ∃ i ≤ m, (c : ℝ) ≤ dkwSampleLikelihood n (b i) lambda x} ⊆
      {x | (c : ℝ) ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        (fun i => dkwSampleLikelihood n (b i) lambda x)} := by
    rintro x ⟨i, hi, hx⟩
    exact hx.trans (Finset.le_sup' (fun i => dkwSampleLikelihood n (b i) lambda x)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi)))
  have hint := setIntegral_le_integral (s := {x | (c : ℝ) ≤
      (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
        (fun i => dkwSampleLikelihood n (b i) lambda x)})
    (dkwSampleLikelihood_integrable n (b m) lambda)
    (Filter.Eventually.of_forall (dkwSampleLikelihood_nonneg n (hbpos m) hl))
  rw [dkwSampleLikelihood_integral n (hbpos m) (hbone m)] at hint
  exact (mul_le_mul_left' (measure_mono hset) (c : ℝ≥0∞)).trans
    (hm.trans (ENNReal.ofReal_le_ofReal hint))

theorem dkwSampleLikelihood_eq_count_power (n : ℕ) (a lambda : ℝ) (x : Fin n → ℝ) :
    dkwSampleLikelihood n a lambda x =
      (1 + lambda / a) ^ ((Finset.univ.filter (fun j => x j ≤ a)).card) := by
  classical
  have hscalar (j : Fin n) : dkwScalarLikelihood a lambda (x j) =
      if x j ≤ a then 1 + lambda / a else 1 := by
    by_cases hx : x j ≤ a <;> simp [dkwScalarLikelihood, uniformCDFIndicator, hx]
  unfold dkwSampleLikelihood
  simp_rw [hscalar]
  rw [Finset.prod_ite]
  simp

def dkwFirstCriticalIndex (n : ℕ) (delta : ℝ) : ℕ := Nat.floor ((n : ℝ) * delta) + 1

theorem dkwFirstCriticalIndex_le (n : ℕ) (hn : 0 < n) {delta : ℝ} (hd : delta < 1) :
    dkwFirstCriticalIndex n delta ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : (n : ℝ) * delta < n := by nlinarith
  have hf : Nat.floor ((n : ℝ) * delta) < n := (Nat.floor_lt' hn.ne').mpr hh
  exact hf

theorem dkwFirstCriticalIndex_positive_threshold (n : ℕ) (hn : 0 < n) (delta : ℝ) :
    0 < (dkwFirstCriticalIndex n delta : ℝ) / n - delta := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := Nat.lt_floor_add_one ((n : ℝ) * delta)
  have hc : (n : ℝ) * delta < (dkwFirstCriticalIndex n delta : ℝ) := by
    simpa only [dkwFirstCriticalIndex, Nat.cast_add, Nat.cast_one] using hh
  have hd : delta < (dkwFirstCriticalIndex n delta : ℝ) / n :=
    (lt_div_iff₀ hnR).mpr (by nlinarith)
  linarith

theorem dkwFirstCriticalIndex_min (n k : ℕ) (hn : 0 < n) {delta : ℝ} (hd : 0 ≤ delta)
    (hk : 0 < (k : ℝ) / n - delta) : dkwFirstCriticalIndex n delta ≤ k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnk : (n : ℝ) * delta < k := by
    have hh : delta < (k : ℝ) / n := by linarith
    nlinarith [(lt_div_iff₀ hnR).mp hh]
  have hf : Nat.floor ((n : ℝ) * delta) < k := by
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le (mul_nonneg hnR.le hd)) hnk
  exact hf

def dkwCriticalSequence (n : ℕ) (delta : ℝ) (i : ℕ) : ℝ :=
  max ((n : ℝ) - i) (dkwFirstCriticalIndex n delta : ℝ) / n - delta

theorem dkwCriticalSequence_antitone (n : ℕ) (delta : ℝ) :
    Antitone (dkwCriticalSequence n delta) := by
  intro i j hij
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold dkwCriticalSequence
  gcongr

theorem dkwCriticalSequence_pos (n : ℕ) (hn : 0 < n) (delta : ℝ) (i : ℕ) :
    0 < dkwCriticalSequence n delta i := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (dkwFirstCriticalIndex_positive_threshold n hn delta).trans_le
  unfold dkwCriticalSequence
  exact sub_le_sub_right (div_le_div_of_nonneg_right (le_max_right _ _) hnR.le) delta

theorem dkwCriticalSequence_le_one (n : ℕ) (hn : 0 < n) {delta : ℝ}
    (hd : 0 ≤ delta) (hdone : delta < 1) (i : ℕ) : dkwCriticalSequence n delta i ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (dkwFirstCriticalIndex n delta : ℝ) ≤ n := by
    exact_mod_cast dkwFirstCriticalIndex_le n hn hdone
  have hm : max ((n : ℝ) - i) (dkwFirstCriticalIndex n delta : ℝ) ≤ n := by
    exact max_le (sub_le_self _ (Nat.cast_nonneg i)) hk
  have hh := (div_le_one hnR).mpr hm
  unfold dkwCriticalSequence
  linarith

theorem dkwCriticalSequence_at (n k : ℕ) (hk : k ≤ n) {delta : ℝ}
    (hklo : dkwFirstCriticalIndex n delta ≤ k) :
    dkwCriticalSequence n delta (n - k) = (k : ℝ) / n - delta := by
  have hkR : (dkwFirstCriticalIndex n delta : ℝ) ≤ k := by exact_mod_cast hklo
  simp only [dkwCriticalSequence, Nat.cast_sub hk, sub_sub_cancel,
    max_eq_left hkR]

def dkwUpperCdfBadEvent (n : ℕ) (delta : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ s ∈ Icc (0 : ℝ) 1, delta < uniformEmpiricalCDF n x s - s}

/-- A strict upper empirical-CDF crossing forces a crossing at one of the
finitely many positive critical thresholds k/n-delta.  This argument requires
neither order statistics nor a tie-null assumption. -/
theorem dkwUpperCdfBadEvent_critical (n : ℕ) (delta : ℝ) (x : Fin n → ℝ)
    (hx : x ∈ dkwUpperCdfBadEvent n delta) :
    ∃ k : ℕ, k ≤ n ∧ 0 < (k : ℝ) / n - delta ∧
      k ≤ (Finset.univ.filter (fun j => x j ≤ (k : ℝ) / n - delta)).card := by
  classical
  obtain ⟨s, hs, hbad⟩ := hx
  let k := (Finset.univ.filter (fun j => x j ≤ s)).card
  have hsu : s < (k : ℝ) / n - delta := by
    change delta < (k : ℝ) / n - s at hbad
    linarith
  refine ⟨k, ?_, hs.1.trans_lt hsu, ?_⟩
  · exact (Finset.card_filter_le _ _).trans_eq (by simp)
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.trans hsu.le

theorem dkwCriticalLikelihood_barrier (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    {delta lambda : ℝ} (hl : 0 ≤ lambda)
    (hbarrier : ∀ p : ℝ, 0 < p → p ≤ 1 - delta →
      Real.log (1 + lambda) - (p + delta) * Real.log (1 + lambda / p) ≤ -2 * delta ^ 2)
    (hapos : 0 < (k : ℝ) / n - delta) (x : Fin n → ℝ)
    (hcount : k ≤ (Finset.univ.filter (fun j => x j ≤ (k : ℝ) / n - delta)).card) :
    Real.exp ((n : ℝ) * (Real.log (1 + lambda) + 2 * delta ^ 2)) ≤
      dkwSampleLikelihood n ((k : ℝ) / n - delta) lambda x := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  let a : ℝ := (k : ℝ) / n - delta
  have ha : 0 < a := hapos
  have hau : a ≤ 1 - delta := by
    dsimp [a]
    linarith [(div_le_one hnR).mpr hkR]
  have hh := hbarrier a ha hau
  have hna : (n : ℝ) * (a + delta) = k := by
    dsimp [a]
    field_simp
    ring
  have hlog : (n : ℝ) * (Real.log (1 + lambda) + 2 * delta ^ 2) ≤
      (k : ℝ) * Real.log (1 + lambda / a) := by
    have hm := mul_le_mul_of_nonneg_left hh hnR.le
    rw [mul_sub, ← mul_assoc, hna] at hm
    nlinarith
  have hbase : 1 ≤ 1 + lambda / a := le_add_of_nonneg_right (div_nonneg hl ha.le)
  have hpow : Real.exp ((k : ℝ) * Real.log (1 + lambda / a)) =
      (1 + lambda / a) ^ k := by
    rw [← Real.log_pow, Real.exp_log (pow_pos (lt_of_lt_of_le zero_lt_one hbase) k)]
  rw [dkwSampleLikelihood_eq_count_power]
  exact ((Real.exp_le_exp.mpr hlog).trans_eq hpow).trans
    (pow_le_pow_right₀ hbase hcount)

/-- The actual finite-sample one-sided CDF inequality follows from a single
deterministic common likelihood barrier.  The Research analytic module proves
that barrier, so it is not an assumed probability inequality or DKW input. -/
theorem dkw_uniform_one_sided_of_common_barrier (n : ℕ) (hn : 0 < n)
    {delta lambda : ℝ} (hd : 0 < delta) (hdone : delta < 1) (hl : 0 ≤ lambda)
    (hbarrier : ∀ p : ℝ, 0 < p → p ≤ 1 - delta →
      Real.log (1 + lambda) - (p + delta) * Real.log (1 + lambda / p) ≤ -2 * delta ^ 2) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (dkwUpperCdfBadEvent n delta) ≤
      ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * delta ^ 2)) := by
  classical
  let b := dkwCriticalSequence n delta
  let c : ℝ≥0 := ⟨Real.exp ((n : ℝ) * (Real.log (1 + lambda) + 2 * delta ^ 2)),
    (Real.exp_pos _).le⟩
  have hsub : dkwUpperCdfBadEvent n delta ⊆
      {x | ∃ i ≤ n, (c : ℝ) ≤ dkwSampleLikelihood n (b i) lambda x} := by
    intro x hx
    obtain ⟨k, hk, ha, hcount⟩ := dkwUpperCdfBadEvent_critical n delta x hx
    refine ⟨n - k, Nat.sub_le _ _, ?_⟩
    dsimp only [b]
    rw [dkwCriticalSequence_at n k hk (dkwFirstCriticalIndex_min n k hn hd.le ha)]
    exact dkwCriticalLikelihood_barrier n k hn hk hl hbarrier ha x hcount
  have hm := dkwSampleLikelihood_maximal n n b (dkwCriticalSequence_antitone n delta)
    (dkwCriticalSequence_pos n hn delta) (dkwCriticalSequence_le_one n hn hd.le hdone) hl c
  have hbound := (mul_le_mul_left' (measure_mono hsub) (c : ℝ≥0∞)).trans hm
  have hc : (c : ℝ≥0∞) =
      ENNReal.ofReal (Real.exp ((n : ℝ) * (Real.log (1 + lambda) + 2 * delta ^ 2))) :=
    (ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le).symm
  rw [hc] at hbound
  have heq : Real.exp ((n : ℝ) * (Real.log (1 + lambda) + 2 * delta ^ 2)) *
      Real.exp (-2 * (n : ℝ) * delta ^ 2) = (1 + lambda) ^ n := by
    rw [← Real.exp_add]
    have hring : (n : ℝ) * (Real.log (1 + lambda) + 2 * delta ^ 2) +
        -2 * (n : ℝ) * delta ^ 2 = (n : ℝ) * Real.log (1 + lambda) := by ring
    rw [hring, ← Real.log_pow, Real.exp_log (by positivity : 0 < (1 + lambda) ^ n)]
  have heqE := congrArg ENNReal.ofReal heq
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at heqE
  rw [← heqE] at hbound
  exact (ENNReal.mul_le_mul_left (by positivity) (by simp)).mp hbound

def dkwSampleReflectEquiv (n : ℕ) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toFun x j := 1 - x j
  invFun x j := 1 - x j
  left_inv x := by funext j; dsimp; ring
  right_inv x := by funext j; dsimp; ring
  measurable_toFun := by
    change Measurable (fun x : Fin n → ℝ => fun j => 1 - x j)
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin n → ℝ => fun j => 1 - x j)
    fun_prop

theorem dkwScalarReflect_measurePreserving :
    MeasurePreserving (fun x : ℝ => 1 - x) cubeCoordinateLaw cubeCoordinateLaw := by
  have hpre : (fun x : ℝ => 1 - x) ⁻¹' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hh := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage
    (s := Icc (0 : ℝ) 1) measurableSet_Icc
  simpa only [hpre, cubeCoordinateLaw] using hh

theorem dkwSampleReflect_measurePreserving (n : ℕ) :
    MeasurePreserving (dkwSampleReflectEquiv n)
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) := by
  exact measurePreserving_pi _ _ (fun _ => dkwScalarReflect_measurePreserving)

theorem dkwSampleReflect_preimage_measure (n : ℕ) (A : Set (Fin n → ℝ)) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) ((dkwSampleReflectEquiv n) ⁻¹' A) =
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) A := by
  rw [← (dkwSampleReflectEquiv n).measurableEmbedding.map_apply,
    (dkwSampleReflect_measurePreserving n).map_eq]

def dkwLowerCdfBadEvent (n : ℕ) (delta : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ s ∈ Icc (0 : ℝ) 1, delta < s - uniformEmpiricalCDF n x s}

theorem dkwEmpiricalCDF_reflect_inequality (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (s : ℝ) :
    1 - uniformEmpiricalCDF n x s ≤
      uniformEmpiricalCDF n (dkwSampleReflectEquiv n x) (1 - s) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : (Finset.univ.filter (fun j => ¬ x j ≤ s)) ⊆
      (Finset.univ.filter (fun j => (dkwSampleReflectEquiv n x) j ≤ 1 - s)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    change 1 - x j ≤ 1 - s
    linarith
  have hcard := Finset.card_le_card hsub
  have hsum := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ) (fun j : Fin n => x j ≤ s)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hreal : (n : ℝ) ≤ ((Finset.univ.filter (fun j => x j ≤ s)).card : ℝ) +
      ((Finset.univ.filter (fun j => (dkwSampleReflectEquiv n x) j ≤ 1 - s)).card : ℝ) := by
    exact_mod_cast (by omega : n ≤ _)
  unfold uniformEmpiricalCDF
  apply (le_div_iff₀ hnR).mpr
  have hdiv : (((Finset.univ.filter (fun j => x j ≤ s)).card : ℝ) / n) * n =
      ((Finset.univ.filter (fun j => x j ≤ s)).card : ℝ) := div_mul_cancel₀ _ hnR.ne'
  nlinarith

theorem dkwLowerCdfBadEvent_reflect_subset (n : ℕ) (hn : 0 < n) (delta : ℝ) :
    dkwLowerCdfBadEvent n delta ⊆ (dkwSampleReflectEquiv n) ⁻¹' dkwUpperCdfBadEvent n delta := by
  rintro x ⟨s, hs, hbad⟩
  refine ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
  have hh := dkwEmpiricalCDF_reflect_inequality n hn x s
  linarith

theorem dkw_uniform_lower_from_upper (n : ℕ) (hn : 0 < n) (delta : ℝ) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (dkwLowerCdfBadEvent n delta) ≤
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (dkwUpperCdfBadEvent n delta) := by
  exact (measure_mono (dkwLowerCdfBadEvent_reflect_subset n hn delta)).trans_eq
    (dkwSampleReflect_preimage_measure n _)

theorem dkwUniformEmpiricalCDF_mem_Icc (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (s : ℝ) :
    uniformEmpiricalCDF n x s ∈ Icc (0 : ℝ) 1 := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · unfold uniformEmpiricalCDF
    positivity
  · unfold uniformEmpiricalCDF
    apply (div_le_one hnR).mpr
    exact_mod_cast (Finset.card_filter_le Finset.univ (fun j => x j ≤ s)).trans_eq (by simp)

theorem dkwUpperCdfBadEvent_eq_empty (n : ℕ) (hn : 0 < n) {delta : ℝ} (hd : 1 ≤ delta) :
    dkwUpperCdfBadEvent n delta = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨s, hs, hbad⟩
  have hh := (dkwUniformEmpiricalCDF_mem_Icc n hn x s).2
  linarith [hs.1]

/-- Sharp one-sided DKW for the actual finite iid uniform sample, with the
common analytic barrier and the martingale probability argument both proved. -/
theorem sharp_uniform_cdf_one_sided (n : ℕ) (hn : 0 < n) {delta : ℝ} (hd : 0 < delta) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (dkwUpperCdfBadEvent n delta) ≤
      ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * delta ^ 2)) := by
  by_cases hdone : delta < 1
  · obtain ⟨lambda, hlambda, hbarrier⟩ := sharpDKW_likelihood_barrier hd hdone
    exact dkw_uniform_one_sided_of_common_barrier n hn hd hdone hlambda.le
      (fun p hp _ => hbarrier p hp)
  · rw [dkwUpperCdfBadEvent_eq_empty n hn (le_of_not_gt hdone), measure_empty]
    exact zero_le _

theorem sharp_uniform_cdf_lower (n : ℕ) (hn : 0 < n) {delta : ℝ} (hd : 0 < delta) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (dkwLowerCdfBadEvent n delta) ≤
      ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * delta ^ 2)) :=
  (dkw_uniform_lower_from_upper n hn delta).trans (sharp_uniform_cdf_one_sided n hn hd)

/-- The literal sharp finite-sample two-sided bound quoted in the manuscript.
All laws are the actual product restricted-volume uniform law. -/
theorem sharp_uniform_cdf_two_sided (n : ℕ) (hn : 0 < n) {delta : ℝ} (hd : 0 < delta) :
    (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      {x | ∃ s ∈ Icc (0 : ℝ) 1, delta < |uniformEmpiricalCDF n x s - s|} ≤
        ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * delta ^ 2)) := by
  have hsub : {x : Fin n → ℝ | ∃ s ∈ Icc (0 : ℝ) 1,
      delta < |uniformEmpiricalCDF n x s - s|} ⊆
      dkwUpperCdfBadEvent n delta ∪ dkwLowerCdfBadEvent n delta := by
    rintro x ⟨s, hs, hbad⟩
    rcases lt_abs.mp hbad with h | h
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr ⟨s, hs, by linarith⟩
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
        (dkwUpperCdfBadEvent n delta ∪ dkwLowerCdfBadEvent n delta) := measure_mono hsub
    _ ≤ (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (dkwUpperCdfBadEvent n delta) +
        (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)) (dkwLowerCdfBadEvent n delta) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * delta ^ 2)) +
        ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * delta ^ 2)) :=
      add_le_add (sharp_uniform_cdf_one_sided n hn hd) (sharp_uniform_cdf_lower n hn hd)
    _ = _ := by rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; congr 1; ring

/-- The legacy interface is now inhabited by a proof, not a cited assumption. -/
theorem sharpDKWInput_proved : DKWInput where
  bound n hn delta hd := by
    simpa only [scalarEmpiricalCDF, uniformEmpiricalCDF] using
      sharp_uniform_cdf_two_sided n hn hd

end Antichain
