import Mathlib.Probability.Distributions.Poisson
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
A finite Poisson configuration constructed from its count and independent marks.
This construction does not postulate independence between spatial restrictions.
-/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

abbrev FiniteConfiguration (X : Type*) := Σ n : ℕ, Fin n → X

variable {X : Type*} [MeasurableSpace X]

def configurationMk (n : ℕ) (x : Fin n → X) : FiniteConfiguration X := ⟨n, x⟩

theorem measurable_configurationMk (n : ℕ) :
    Measurable (configurationMk (X := X) n) := by
  exact Measurable.of_le_map (iInf_le _ n)

def configurationEvent (A : ∀ n : ℕ, Set (Fin n → X)) : Set (FiniteConfiguration X) :=
  {z | z.2 ∈ A z.1}

theorem configurationEvent_measurable (A : ∀ n : ℕ, Set (Fin n → X))
    (hA : ∀ n, MeasurableSet (A n)) : MeasurableSet (configurationEvent A) := by
  change MeasurableSet[⨅ n, (inferInstance : MeasurableSpace (Fin n → X)).map
    (configurationMk n)] (configurationEvent A)
  rw [MeasurableSpace.measurableSet_iInf]
  exact hA

omit [MeasurableSpace X] in
@[simp] theorem configurationMk_preimage_event (A : ∀ n : ℕ, Set (Fin n → X))
    (n : ℕ) : configurationMk n ⁻¹' configurationEvent A = A n := rfl

/-- Actual sampling: a Poisson count of rate `r`, followed by independent marks
with law `mu`. The finite ordered list is an explicit configuration carrier. -/
def poissonConfigurationLaw (r : ℝ≥0) (mu : Measure X) : Measure (FiniteConfiguration X) :=
  Measure.sum (fun n : ℕ => (poissonPMF r n) •
    (Measure.pi (fun _ : Fin n => mu)).map (configurationMk n))

instance poissonConfigurationLaw_isProbabilityMeasure (r : ℝ≥0) (mu : Measure X)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (poissonConfigurationLaw r mu) := by
  constructor
  rw [poissonConfigurationLaw, Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_configurationMk _ ) MeasurableSet.univ,
    preimage_univ, measure_univ, mul_one]
  exact (poissonPMF r).tsum_coe

/-- Integrating a configuration functional is exactly the Poisson mixture of
its independent-mark integrals. -/
theorem poissonConfigurationLaw_lintegral (r : ℝ≥0) (mu : Measure X)
    (F : FiniteConfiguration X → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂poissonConfigurationLaw r mu) =
      ∑' n : ℕ, poissonPMF r n *
        ∫⁻ x : Fin n → X, F ⟨n, x⟩ ∂Measure.pi (fun _ => mu) := by
  rw [poissonConfigurationLaw, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_map hF (measurable_configurationMk n)]
  rfl

/-- The exact event expansion. Its coefficients are genuine probabilities for
independent marks, and the law on the left is a constructed probability law. -/
theorem poissonConfigurationLaw_event (r : ℝ≥0) (mu : Measure X)
    (A : Set (FiniteConfiguration X)) (hA : MeasurableSet A) :
    poissonConfigurationLaw r mu A =
      ∑' n : ℕ, poissonPMF r n *
        Measure.pi (fun _ : Fin n => mu) ((configurationMk n) ⁻¹' A) := by
  rw [poissonConfigurationLaw, Measure.sum_apply_of_countable]
  apply tsum_congr
  intro n
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_configurationMk n) hA]

/-- Removing the Poisson normalizing factor yields the exponential generating
series, including the zero-rate case. -/
theorem poissonConfigurationLaw_event_expansion (r : ℝ≥0) (mu : Measure X)
    (A : Set (FiniteConfiguration X)) (hA : MeasurableSet A) :
    ENNReal.ofReal (Real.exp (r : ℝ)) * poissonConfigurationLaw r mu A =
      ∑' n : ℕ, (r : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) *
        Measure.pi (fun _ : Fin n => mu) ((configurationMk n) ⁻¹' A) := by
  rw [poissonConfigurationLaw_event r mu A hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hcancel : ENNReal.ofReal (Real.exp (r : ℝ)) * poissonPMF r n =
      (r : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) := by
    change ENNReal.ofReal (Real.exp (r : ℝ)) *
      ENNReal.ofReal (poissonPMFReal r n) = _
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), poissonPMFReal]
    have hreal : Real.exp (r : ℝ) *
        (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) =
        (r : ℝ) ^ n / (n.factorial : ℝ) := by
      rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add]
      simp
    rw [hreal, ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_pow r.coe_nonneg]
    simp
  rw [← mul_assoc, hcancel]

/-- Scaling every independent mark measure scales its `n`-fold product by the
literal `n`th power. -/
theorem pi_nnreal_smul (mu : Measure X) [IsFiniteMeasure mu] (a : ℝ≥0) (n : ℕ) :
    Measure.pi (fun _ : Fin n => a • mu) =
      (a : ℝ≥0∞) ^ n • Measure.pi (fun _ : Fin n => mu) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Measure.pi_pi]
  rw [Finset.prod_mul_distrib]
  simp

/-- The normalized independent mark law associated with a finite intensity. -/
def normalizedMarkLaw (mu : Measure X) : Measure X :=
  ((mu univ).toNNReal)⁻¹ • mu

theorem intensity_eq_mass_smul_normalized (mu : Measure X) [IsFiniteMeasure mu]
    [NeZero mu] : mu = (mu univ).toNNReal • normalizedMarkLaw mu := by
  have hm : (mu univ).toNNReal ≠ 0 := by
    exact ENNReal.toNNReal_ne_zero.mpr ⟨NeZero.ne _, measure_ne_top _ _⟩
  rw [normalizedMarkLaw, smul_smul, mul_inv_cancel₀ hm, one_smul]

instance normalizedMarkLaw_isProbabilityMeasure (mu : Measure X) [IsFiniteMeasure mu]
    [NeZero mu] : IsProbabilityMeasure (normalizedMarkLaw mu) := by
  constructor
  have hm : mu univ ≠ 0 := NeZero.ne _
  have hmNN : (mu univ).toNNReal ≠ 0 :=
    ENNReal.toNNReal_ne_zero.mpr ⟨hm, measure_ne_top _ _⟩
  simp only [normalizedMarkLaw, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hmNN,
    ENNReal.coe_toNNReal (measure_ne_top _ _)]
  exact ENNReal.inv_mul_cancel hm (measure_ne_top _ _)

/-- A finite-intensity Poisson process on an explicit finite-list carrier:
the Poisson mean is `t * mu(univ)` and the marks have the normalized intensity. -/
def finiteIntensityPoissonLaw (t : ℝ≥0) (mu : Measure X) :
    Measure (FiniteConfiguration X) :=
  poissonConfigurationLaw (t * (mu univ).toNNReal) (normalizedMarkLaw mu)

instance finiteIntensityPoissonLaw_isProbabilityMeasure (t : ℝ≥0)
    (mu : Measure X) [IsFiniteMeasure mu] [NeZero mu] :
    IsProbabilityMeasure (finiteIntensityPoissonLaw t mu) := by
  unfold finiteIntensityPoissonLaw
  infer_instance

/-- Exact exponential formula for an actual finite-intensity Poisson/iid law.
No independence assertion about different cells enters this proof. -/
theorem finiteIntensityPoissonLaw_event_expansion (t : ℝ≥0) (mu : Measure X)
    [IsFiniteMeasure mu] [NeZero mu]
    (A : ∀ n : ℕ, Set (Fin n → X)) (hA : ∀ n, MeasurableSet (A n)) :
    ENNReal.ofReal (Real.exp ((t : ℝ) * (mu univ).toReal)) *
        finiteIntensityPoissonLaw t mu (configurationEvent A) =
      ∑' n : ℕ, (t : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) *
        Measure.pi (fun _ : Fin n => mu) (A n) := by
  have h := poissonConfigurationLaw_event_expansion (t * (mu univ).toNNReal)
    (normalizedMarkLaw mu) (configurationEvent A) (configurationEvent_measurable A hA)
  change _ = _ at h
  rw [show ((t * (mu univ).toNNReal : ℝ≥0) : ℝ) =
      (t : ℝ) * (mu univ).toReal by simp [ENNReal.toReal]] at h
  unfold finiteIntensityPoissonLaw
  rw [h]
  apply tsum_congr
  intro n
  have hpi : Measure.pi (fun _ : Fin n => mu) =
      ((mu univ).toNNReal : ℝ≥0∞) ^ n •
        Measure.pi (fun _ : Fin n => normalizedMarkLaw mu) := by
    conv_lhs => rw [intensity_eq_mass_smul_normalized mu]
    exact pi_nnreal_smul _ _ _
  rw [hpi, Measure.smul_apply, smul_eq_mul]
  simp only [ENNReal.coe_mul, mul_pow, configurationMk_preimage_event]
  simp only [div_eq_mul_inv]
  ac_rfl

/-- The nonnegative unnormalized configuration measure. Its measurable-event
masses are exponential generating series without any convergence convention. -/
def configurationSeriesMeasure (t : ℝ≥0∞) (mu : Measure X) : Measure (FiniteConfiguration X) :=
  Measure.sum (fun n : ℕ => (t ^ n / (n.factorial : ℝ≥0∞)) •
    (Measure.pi (fun _ : Fin n => mu)).map (configurationMk n))

theorem configurationSeriesMeasure_event (t : ℝ≥0∞) (mu : Measure X)
    (A : ∀ n : ℕ, Set (Fin n → X)) (hA : ∀ n, MeasurableSet (A n)) :
    configurationSeriesMeasure t mu (configurationEvent A) =
      ∑' n : ℕ, t ^ n / (n.factorial : ℝ≥0∞) * Measure.pi (fun _ : Fin n => mu) (A n) := by
  rw [configurationSeriesMeasure, Measure.sum_apply_of_countable]
  apply tsum_congr
  intro n
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_configurationMk n) (configurationEvent_measurable A hA),
    configurationMk_preimage_event]

def configurationCarrier (U : Set X) : Set (FiniteConfiguration X) :=
  configurationEvent (fun n => Set.univ.pi (fun _ : Fin n => U))

theorem configurationCarrier_measurable {U : Set X} (hU : MeasurableSet U) :
    MeasurableSet (configurationCarrier U) :=
  configurationEvent_measurable _ (fun _ => MeasurableSet.univ_pi (fun _ => hU))

theorem configurationSeriesMeasure_restrict (t : ℝ≥0∞) (mu : Measure X)
    [IsFiniteMeasure mu] {U : Set X} (hU : MeasurableSet U)
    (A : ∀ n : ℕ, Set (Fin n → X)) (hA : ∀ n, MeasurableSet (A n)) :
    configurationSeriesMeasure t (mu.restrict U) (configurationEvent A) =
      configurationSeriesMeasure t mu (configurationEvent A ∩ configurationCarrier U) := by
  rw [configurationSeriesMeasure_event t (mu.restrict U) A hA,
    configurationSeriesMeasure, Measure.sum_apply_of_countable]
  apply tsum_congr
  intro n
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_configurationMk n)
      ((configurationEvent_measurable A hA).inter (configurationCarrier_measurable hU)),
    ← Measure.restrict_pi_pi (fun _ : Fin n => mu) (fun _ => U),
    Measure.restrict_apply (hA n)]
  rfl

omit [MeasurableSpace X] in
theorem configurationCarrier_monotone : Monotone (configurationCarrier (X := X)) := by
  intro U V hUV z hz j hj
  exact hUV (hz j hj)

omit [MeasurableSpace X] in
/-- Every finite configuration is eventually contained in an increasing
exhaustion. This uses actual finiteness of its marks, not a probabilistic input. -/
theorem configurationCarrier_iUnion (U : ℕ → Set X) (hmono : Monotone U)
    (hcover : (⋃ m, U m) = Set.univ) :
    (⋃ m, configurationCarrier (U m)) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  rintro ⟨n, x⟩
  have hx (j : Fin n) : ∃ m : ℕ, x j ∈ U m := by
    have hh : x j ∈ ⋃ m, U m := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hh
  choose k hk using hx
  refine Set.mem_iUnion.mpr ⟨Finset.univ.sup k, ?_⟩
  intro j hj
  exact hmono (Finset.le_sup (f := k) (Finset.mem_univ j)) (hk j)

/-- Full generating-series exhaustion, obtained by continuity from below of an
actual measure on the finite-configuration carrier. -/
theorem configurationSeriesMeasure_exhaustion (t : ℝ≥0∞) (mu : Measure X)
    [IsFiniteMeasure mu] (U : ℕ → Set X) (hU : ∀ m, MeasurableSet (U m))
    (hmono : Monotone U) (hcover : (⋃ m, U m) = Set.univ)
    (A : ∀ n : ℕ, Set (Fin n → X)) (hA : ∀ n, MeasurableSet (A n)) :
    configurationSeriesMeasure t mu (configurationEvent A) =
      ⨆ m : ℕ, configurationSeriesMeasure t (mu.restrict (U m)) (configurationEvent A) := by
  have hm : Monotone (fun m => configurationEvent A ∩ configurationCarrier (U m)) :=
    fun i j hij z hz => ⟨hz.1, configurationCarrier_monotone (hmono hij) hz.2⟩
  have heq : (⋃ m, configurationEvent A ∩ configurationCarrier (U m)) = configurationEvent A := by
    rw [← Set.inter_iUnion, configurationCarrier_iUnion U hmono hcover, Set.inter_univ]
  calc
    _ = configurationSeriesMeasure t mu
        (⋃ m, configurationEvent A ∩ configurationCarrier (U m)) := congrArg _ heq.symm
    _ = ⨆ m, configurationSeriesMeasure t mu
        (configurationEvent A ∩ configurationCarrier (U m)) := hm.measure_iUnion
    _ = _ := by
      apply iSup_congr
      intro m
      exact (configurationSeriesMeasure_restrict t mu (hU m) A hA).symm

end Antichain
