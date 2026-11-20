import Antichain.TileSeriesLocal
import Antichain.OneTileReal
import Antichain.AlcoveTiling
import Antichain.PoissonConfiguration
import Antichain.PoissonConfigurationProduct
import Antichain.OnePointIntegral
import Antichain.TileLogGrowth
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Finset.Preimage
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
Measure expansions and analytic product estimates for the paper's actual tile
generating functions. Spatial restriction independence is proved from the actual Poisson law.
-/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset
open scoped ENNReal NNReal Pointwise BoundedContinuousFunction

/-- Finite products of a genuine integrable density, with arbitrary finite base
measure. The equality is proved on measurable rectangles by Fubini. -/
theorem pi_withDensity_real {J X : Type*} [Fintype J] [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (w : X → ℝ)
    (hw : Integrable w mu) (hn : ∀ x, 0 ≤ w x) :
    Measure.pi (fun _ : J => mu.withDensity (fun x => ENNReal.ofReal (w x))) =
      (Measure.pi (fun _ : J => mu)).withDensity
        (fun x => ENNReal.ofReal (∏ j, w (x j))) := by
  classical
  letI := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ENNReal.ofReal (∏ j, w (x j))
    ∂((Measure.pi (fun _ : J => mu)).restrict (Set.univ.pi s))) = _
  rw [Measure.restrict_pi_pi]
  have hprod := Integrable.fintype_prod (fun j => hw.restrict (s := s j))
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun j _ => hn (x j)))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => integral_nonneg hn)]
  apply Finset.prod_congr rfl
  intro j _
  rw [withDensity_apply _ (hs j)]
  exact ofReal_integral_eq_lintegral_ofReal (hw.restrict (s := s j))
    (Filter.Eventually.of_forall hn)

section WeightedPoisson

variable {d : ℕ} [NeZero d]

/-- The actual finite point intensity used to Poissonize the weighted Gaussian
antichain model. -/
def weightedPointLaw (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) : Measure (CubePoint d) :=
  (gaussianPointLaw d).withDensity (fun g => ENNReal.ofReal (singlePointWeight sigma c g))

theorem weightedPointLaw_univ (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPointLaw sigma c univ = unrestrictedSinglePointMass sigma c := by
  rw [weightedPointLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rfl

theorem weightedPointLaw_isFiniteMeasure (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) : IsFiniteMeasure (weightedPointLaw sigma c) := by
  constructor
  rw [weightedPointLaw_univ]
  exact unrestrictedSinglePointMass_lt_top sigma c hc

theorem weightedPointLaw_neZero (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) : NeZero (weightedPointLaw sigma c) := by
  constructor
  intro h
  have hm := unrestrictedSinglePointMass_pos hd sigma c
  simp only [← weightedPointLaw_univ, h, Measure.coe_zero, Pi.zero_apply, lt_self_iff_false] at hm

theorem weightedPointLaw_product (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    Measure.pi (fun _ : Fin n => weightedPointLaw sigma c) =
      (gaussianSampleLaw n d).withDensity (fun g => ENNReal.ofReal (gaussianWeight n sigma c g)) := by
  have h := pi_withDensity_real (J := Fin n) (gaussianPointLaw d)
    (singlePointWeight sigma c) (singlePointWeight_integrable sigma c hc)
    (fun _ => Real.exp_nonneg _)
  convert h using 1
  congr 1
  funext g
  congr 1
  simp only [singlePointWeight, gaussianWeight, gaussianWeightExponent, Real.exp_sum]

/-- Actual model coefficients are the antichain masses of independent marks
under the finite point intensity. -/
theorem weightedPointLaw_antichain (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    Measure.pi (fun _ : Fin n => weightedPointLaw sigma c) (strictAntichainEvent n d) =
      weightedPartitionMass n sigma c := by
  rw [weightedPointLaw_product n sigma c hc,
    withDensity_apply _ (measurableSet_strictAntichainEvent n d)]
  rfl

def weightedPoissonLaw (t : ℝ≥0) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    Measure (FiniteConfiguration (CubePoint d)) :=
  finiteIntensityPoissonLaw t (weightedPointLaw sigma c)

def poissonAntichainEvent (d : ℕ) : Set (FiniteConfiguration (CubePoint d)) :=
  configurationEvent (fun n => strictAntichainEvent n d)

theorem poissonAntichainEvent_measurable (d : ℕ) : MeasurableSet (poissonAntichainEvent d) :=
  configurationEvent_measurable _ (fun n => measurableSet_strictAntichainEvent n d)

theorem weightedPoissonLaw_isProbabilityMeasure (hd : 2 ≤ d) (t : ℝ≥0)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    IsProbabilityMeasure (weightedPoissonLaw t sigma c) := by
  letI := weightedPointLaw_isFiniteMeasure sigma c hc
  letI := weightedPointLaw_neZero hd sigma c
  unfold weightedPoissonLaw
  infer_instance

/-- The exact source Poissonization identity for the actual `Z_n`, derived from
a constructed probability law, rather than a point-process characterization
assumed as an input. -/
theorem weightedPoisson_partition_expansion (hd : 2 ≤ d) (t : ℝ≥0)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    ENNReal.ofReal (Real.exp ((t : ℝ) * (unrestrictedSinglePointMass sigma c).toReal)) *
        weightedPoissonLaw t sigma c (poissonAntichainEvent d) =
      ∑' n : ℕ, (t : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) *
        weightedPartitionMass n sigma c := by
  letI := weightedPointLaw_isFiniteMeasure sigma c hc
  letI := weightedPointLaw_neZero hd sigma c
  have h := finiteIntensityPoissonLaw_event_expansion t (weightedPointLaw sigma c)
    (fun n => strictAntichainEvent n d) (fun n => measurableSet_strictAntichainEvent n d)
  simp only [weightedPointLaw_univ, weightedPointLaw_antichain _ sigma c hc] at h
  exact h

end WeightedPoisson

/-- Expanding a finite mixture in each independent coordinate gives the sum over
all literal label-to-cell allocations. This is an equality of measures. -/
theorem pi_finite_sum_measure {K J X : Type*} [Fintype K] [Fintype J]
    [DecidableEq J] [MeasurableSpace X] (mu : K → Measure X) [∀ i, IsFiniteMeasure (mu i)] :
    Measure.pi (fun _ : J => ∑ i : K, mu i) =
      ∑ a : J → K, Measure.pi (fun j => mu (a j)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.finset_sum_apply]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sum (fun (j : J) (i : K) => mu i (s j))]
  apply Finset.prod_congr rfl
  intro j _
  rw [Measure.finset_sum_apply]

/-- Finite allocation expansion at the integral level. -/
theorem lintegral_pi_finite_sum_measure {K J X : Type*} [Fintype K] [Fintype J]
    [DecidableEq J] [MeasurableSpace X] (mu : K → Measure X) [∀ i, IsFiniteMeasure (mu i)]
    (F : (J → X) → ℝ≥0∞) :
    (∫⁻ x, F x ∂Measure.pi (fun _ : J => ∑ i : K, mu i)) =
      ∑ a : J → K, ∫⁻ x, F x ∂Measure.pi (fun j => mu (a j)) := by
  rw [pi_finite_sum_measure]
  exact lintegral_finset_sum_measure _ _ _

section ConfigurationSplitting

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem pi_add_measure {J : Type*} [Fintype J] [DecidableEq J]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    Measure.pi (fun _ : J => mu + nu) =
      ∑ S : Finset J, Measure.pi (fun j => if j ∈ S then mu else nu) := by
  classical
  letI : ∀ (S : Finset J) (j : J), SigmaFinite (if j ∈ S then mu else nu) := fun S j => by
    split_ifs <;> infer_instance
  apply Measure.pi_eq
  intro s hs
  rw [Measure.finset_sum_apply]
  simp_rw [Measure.pi_pi]
  simp only [Measure.add_apply]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  have hval (j : J) : (if j ∈ S then mu else nu) (s j) =
      if j ∈ S then mu (s j) else nu (s j) := by split_ifs <;> rfl
  simp_rw [hval]
  rw [Finset.prod_ite]
  have hcompl : (Finset.univ.filter (fun j : J => j ∉ S)) = Sᶜ := by
    ext j
    simp
  rw [hcompl]
  simp

def realizedAntichainEvent (Q : X → Fin d → ℝ) (J : Type*) : Set (J → X) :=
  {x | IsAntichain (fun j => Q (x j))}

theorem realizedAntichainEvent_measurable (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (J : Type*) [Countable J] :
    MeasurableSet (realizedAntichainEvent Q J) :=
  measurableSet_isAntichain _ (fun j i => (hQ i).comp (measurable_pi_apply j))

def realizedAntichainMass (Q : X → Fin d → ℝ) (mu : Measure X) (n : ℕ) : ℝ≥0∞ :=
  Measure.pi (fun _ : Fin n => mu) (realizedAntichainEvent Q (Fin n))

theorem realizedAntichain_measure_equiv (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (mu : Measure X) [IsFiniteMeasure mu]
    {J K : Type*} [Fintype J] [Fintype K] (e : J ≃ K) :
    Measure.pi (fun _ : J => mu) (realizedAntichainEvent Q J) =
      Measure.pi (fun _ : K => mu) (realizedAntichainEvent Q K) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : K => mu) e
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : K => X) e) ⁻¹'
      realizedAntichainEvent Q K = realizedAntichainEvent Q J := by
    ext x
    simp only [realizedAntichainEvent, Set.mem_preimage, mem_setOf_eq,
      MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
    exact isAntichain_labelEquiv_iff e.symm (fun j => Q (x j))
  have h := hmp.measure_preimage (realizedAntichainEvent_measurable Q hQ K).nullMeasurableSet
  rwa [hpre] at h

theorem realizedAntichain_measure_eq_card (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (mu : Measure X) [IsFiniteMeasure mu]
    (J : Type*) [Fintype J] :
    Measure.pi (fun _ : J => mu) (realizedAntichainEvent Q J) =
      realizedAntichainMass Q mu (Fintype.card J) :=
  realizedAntichain_measure_equiv Q hQ mu (Fintype.equivFin J)

/-- An actual antichain restricts to one in each half of a coordinate split.
The two resulting factors follow from the proved product measure law. -/
theorem realizedAntichain_mixed_measure_le (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (mu nu : Measure X)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) :
    Measure.pi (fun j : J => if j ∈ S then mu else nu) (realizedAntichainEvent Q J) ≤
      realizedAntichainMass Q mu S.card *
        realizedAntichainMass Q nu (Fintype.card J - S.card) := by
  classical
  letI : Fintype {j : J // j ∈ S} := Subtype.fintype (fun j => j ∈ S)
  letI : Fintype {j : J // j ∉ S} := Subtype.fintype (fun j => j ∉ S)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => X) (fun j => j ∈ S)
  letI : ∀ j : J, SigmaFinite (if j ∈ S then mu else nu) := fun j => by
    split_ifs <;> infer_instance
  have hmp : MeasurePreserving e
      (Measure.pi (fun j : J => if j ∈ S then mu else nu))
      ((Measure.pi (fun _ : {j : J // j ∈ S} => mu)).prod
        (Measure.pi (fun _ : {j : J // j ∉ S} => nu))) := by
    have hmp0 := measurePreserving_piEquivPiSubtypeProd
      (fun j : J => if j ∈ S then mu else nu) (fun j => j ∈ S)
    have hleft : (fun j : {j : J // j ∈ S} => if j.val ∈ S then mu else nu) =
        fun _ => mu := by funext j; exact if_pos j.property
    have hright : (fun j : {j : J // j ∉ S} => if j.val ∈ S then mu else nu) =
        fun _ => nu := by funext j; exact if_neg j.property
    rw [hleft, hright] at hmp0
    exact hmp0
  have hsub : realizedAntichainEvent Q J ⊆ e ⁻¹'
      ((realizedAntichainEvent Q {j : J // j ∈ S}) ×ˢ
        (realizedAntichainEvent Q {j : J // j ∉ S})) := by
    intro x hx
    constructor
    · intro j k hjk
      exact hx j.val k.val (fun h => hjk (Subtype.ext h))
    · intro j k hjk
      exact hx j.val k.val (fun h => hjk (Subtype.ext h))
  have h := hmp.measure_preimage
    ((realizedAntichainEvent_measurable Q hQ _).prod
      (realizedAntichainEvent_measurable Q hQ _)).nullMeasurableSet
  calc
    _ ≤ _ := measure_mono hsub
    _ = _ := h
    _ = _ := by
      rw [Measure.prod_prod,
        realizedAntichain_measure_eq_card Q hQ mu,
        realizedAntichain_measure_eq_card Q hQ nu]
      congr 2
      · exact Fintype.card_coe S
      · rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- A finite binomial splitting bound for the literal antichain mass. Its
binomial coefficient counts the subsets of labels allocated to the first law. -/
theorem realizedAntichainMass_add_le (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (mu nu : Measure X)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] (n : ℕ) :
    realizedAntichainMass Q (mu + nu) n ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) *
        (realizedAntichainMass Q mu k * realizedAntichainMass Q nu (n - k)) := by
  classical
  unfold realizedAntichainMass
  rw [pi_add_measure, Measure.finset_sum_apply]
  calc
    _ ≤ ∑ S : Finset (Fin n),
        realizedAntichainMass Q mu S.card * realizedAntichainMass Q nu (n - S.card) := by
      apply Finset.sum_le_sum
      intro S _
      simpa only [Fintype.card_fin] using realizedAntichain_mixed_measure_le Q hQ mu nu S
    _ = _ := by
      change (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        realizedAntichainMass Q mu S.card * realizedAntichainMass Q nu (n - S.card)) = _
      rw [Finset.sum_powerset]
      simp only [Finset.card_univ, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, realizedAntichainMass] using
        Finset.sum_powersetCard k (Finset.univ : Finset (Fin n))
          (fun j => realizedAntichainMass Q mu j * realizedAntichainMass Q nu (n - j))

def configurationPartition (Q : X → Fin d → ℝ) (mu : Measure X) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, t ^ n / (n.factorial : ℝ≥0∞) * realizedAntichainMass Q mu n

theorem ennreal_tsum_cauchy (f g : ℕ → ℝ≥0∞) :
    (∑' n, f n) * (∑' n, g n) =
      ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
  classical
  calc
    _ = ∑' p : ℕ × ℕ, f p.1 * g p.2 := by
      rw [ENNReal.tsum_prod (f := fun n m => f n * g m)]
      simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ = ∑' n : ℕ, ∑' p : Finset.antidiagonal n, f p.val.1 * g p.val.2 := by
      rw [← (Finset.sigmaAntidiagonalEquivProd :
        (Σ n : ℕ, Finset.antidiagonal n) ≃ ℕ × ℕ).tsum_eq]
      change (∑' p : (Σ n : ℕ, Finset.antidiagonal n), f p.2.val.1 * g p.2.val.2) = _
      exact ENNReal.tsum_sigma (fun (n : ℕ) (p : Finset.antidiagonal n) => f p.val.1 * g p.val.2)
    _ = _ := by
      apply tsum_congr
      intro n
      letI : Fintype (Finset.antidiagonal n) := Finset.fintypeCoeSort _
      rw [tsum_fintype]
      change (∑ p : Finset.antidiagonal n, (fun p : ℕ × ℕ => f p.1 * g p.2) p.val) = _
      rw [Finset.sum_coe_sort (Finset.antidiagonal n) (fun p : ℕ × ℕ => f p.1 * g p.2)]
      exact Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => f k * g l) n

theorem ennreal_binomial_egf_term (n k : ℕ) (hkn : k ≤ n) (t A B : ℝ≥0∞) :
    t ^ n / (n.factorial : ℝ≥0∞) * ((n.choose k : ℝ≥0∞) * (A * B)) =
      (t ^ k / (k.factorial : ℝ≥0∞) * A) *
        (t ^ (n - k) / ((n - k).factorial : ℝ≥0∞) * B) := by
  have hreal : (n.choose k : ℝ) / (n.factorial : ℝ) =
      1 / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    simpa only [one_mul, mul_assoc, ← Nat.cast_mul] using
      congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_mul_factorial_mul_factorial hkn)
  have hconst : (n.choose k : ℝ≥0∞) / (n.factorial : ℝ≥0∞) =
      1 / ((k.factorial : ℝ≥0∞) * ((n - k).factorial : ℝ≥0∞)) := by
    have hh := congrArg ENNReal.ofReal hreal
    simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < n.factorial),
      ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) <
        (k.factorial : ℝ) * ((n - k).factorial : ℝ)), ENNReal.ofReal_natCast,
      ENNReal.ofReal_one, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ k.factorial)] using hh
  calc
    _ = t ^ n * ((n.choose k : ℝ≥0∞) / (n.factorial : ℝ≥0∞)) * (A * B) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = _ := by
      rw [hconst, ← Nat.add_sub_of_le hkn, pow_add]
      simp only [Nat.add_sub_cancel_left]
      simp only [div_eq_mul_inv, one_mul]
      rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
      ac_rfl

/-- Dropping cross-cell comparisons gives the full exponential product
inequality for two finite measures, with the binomial label factors canceled
against the exponential factorial denominators. -/
theorem configurationPartition_add_le (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (mu nu : Measure X)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] (t : ℝ≥0∞) :
    configurationPartition Q (mu + nu) t ≤
      configurationPartition Q mu t * configurationPartition Q nu t := by
  unfold configurationPartition
  rw [ennreal_tsum_cauchy]
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ t ^ n / (n.factorial : ℝ≥0∞) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) *
          (realizedAntichainMass Q mu k * realizedAntichainMass Q nu (n - k)) :=
      mul_le_mul_left' (realizedAntichainMass_add_le Q hQ mu nu n) _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact ennreal_binomial_egf_term n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) _ _ _

theorem realizedAntichainMass_card_zero (Q : X → Fin d → ℝ) (mu : Measure X) :
    realizedAntichainMass Q mu 0 = 1 := by
  have heq : realizedAntichainEvent Q (Fin 0) = Set.univ := by
    ext x
    simp [realizedAntichainEvent, IsAntichain]
  rw [realizedAntichainMass, heq, Measure.pi_empty_univ]

theorem configurationPartition_zero (Q : X → Fin d → ℝ) (t : ℝ≥0∞) :
    configurationPartition Q 0 t = 1 := by
  unfold configurationPartition
  rw [tsum_eq_single 0]
  · rw [realizedAntichainMass_card_zero]
    simp
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hm : realizedAntichainMass Q 0 (k + 1) = 0 := by
      apply le_antisymm _ bot_le
      calc
        _ ≤ Measure.pi (fun _ : Fin (k + 1) => (0 : Measure X)) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 0 := by simp [Measure.pi_univ]
    rw [hm, mul_zero]

/-- The full finite-cell exponential product bound, proved by repeated actual
measure addition and the preceding binomial splitting argument. -/
theorem configurationPartition_finset_sum_le {K : Type*} [DecidableEq K]
    (Q : X → Fin d → ℝ) (hQ : ∀ i, Measurable (fun x => Q x i))
    (mu : K → Measure X) [∀ i, IsFiniteMeasure (mu i)] (S : Finset K) (t : ℝ≥0∞) :
    configurationPartition Q (∑ i ∈ S, mu i) t ≤
      ∏ i ∈ S, configurationPartition Q (mu i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [configurationPartition_zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (configurationPartition_add_le Q hQ (mu i) (∑ j ∈ S, mu j) t).trans
      (mul_le_mul_left' ih _)

theorem configurationPartition_eq_seriesMeasure (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (mu : Measure X) (t : ℝ≥0∞) :
    configurationPartition Q mu t = configurationSeriesMeasure t mu
      (configurationEvent (fun n => realizedAntichainEvent Q (Fin n))) := by
  rw [configurationSeriesMeasure_event _ _ _ (fun _ => realizedAntichainEvent_measurable Q hQ _)]
  rfl

theorem configurationPartition_exhaustion (Q : X → Fin d → ℝ)
    (hQ : ∀ i, Measurable (fun x => Q x i)) (mu : Measure X) [IsFiniteMeasure mu]
    (U : ℕ → Set X) (hU : ∀ m, MeasurableSet (U m)) (hmono : Monotone U)
    (hcover : (⋃ m, U m) = Set.univ) (t : ℝ≥0∞) :
    configurationPartition Q mu t = ⨆ m : ℕ, configurationPartition Q (mu.restrict (U m)) t := by
  simp_rw [configurationPartition_eq_seriesMeasure Q hQ]
  exact configurationSeriesMeasure_exhaustion t mu U hU hmono hcover _
    (fun _ => realizedAntichainEvent_measurable Q hQ _)

def encodedCellPrefix (K : Type*) [Encodable K] (m : ℕ) : Finset K :=
  (Finset.range m).preimage Encodable.encode Encodable.encode_injective.injOn

@[simp] theorem mem_encodedCellPrefix {K : Type*} [Encodable K] (m : ℕ) (i : K) :
    i ∈ encodedCellPrefix K m ↔ Encodable.encode i < m := by
  simp [encodedCellPrefix]

/-- A countable measurable spatial partition obeys the full exponential product
bound. The only local input is its separately proved one-cell integral bound.
The proof exhausts actual finite configurations; spatial independence is not
assumed. -/
theorem configurationPartition_countable_le_exp_sum {K : Type*} [Encodable K]
    (Q : X → Fin d → ℝ) (hQ : ∀ i, Measurable (fun x => Q x i))
    (mu : Measure X) [IsFiniteMeasure mu] (C : K → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : (⋃ i, C i) = Set.univ) (t : ℝ≥0∞) (V : K → ℝ)
    (hV : ∀ i, 1 ≤ V i) (hlogs : Summable (fun i => Real.log (V i)))
    (hlocal : ∀ i, configurationPartition Q (mu.restrict (C i)) t ≤ ENNReal.ofReal (V i)) :
    configurationPartition Q mu t ≤ ENNReal.ofReal (Real.exp (∑' i, Real.log (V i))) := by
  classical
  let U : ℕ → Set X := fun m => ⋃ i ∈ encodedCellPrefix K m, C i
  have hU : ∀ m, MeasurableSet (U m) := fun m =>
    (encodedCellPrefix K m).measurableSet_biUnion (fun i _ => hC i)
  have hmono : Monotone U := by
    intro m n hmn x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨(mem_encodedCellPrefix n i).mpr ((mem_encodedCellPrefix m i).mp hi |>.trans_le hmn), hx⟩⟩
  have hcov : (⋃ m, U m) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, C i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨Encodable.encode i + 1,
      Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨(mem_encodedCellPrefix _ i).mpr (Nat.lt_succ_self _), hi⟩⟩⟩
  rw [configurationPartition_exhaustion Q hQ mu U hU hmono hcov t]
  apply iSup_le
  intro m
  let S := encodedCellPrefix K m
  have hrestrict : mu.restrict (U m) = ∑ i ∈ S, mu.restrict (C i) := by
    dsimp only [U]
    rw [Measure.restrict_biUnion_finset (fun i _ j _ hij => hdisj hij) hC]
    exact Measure.sum_coe_finset S (fun i => mu.restrict (C i))
  rw [hrestrict]
  calc
    _ ≤ ∏ i ∈ S, configurationPartition Q (mu.restrict (C i)) t :=
      configurationPartition_finset_sum_le Q hQ _ S t
    _ ≤ ∏ i ∈ S, ENNReal.ofReal (V i) :=
      Finset.prod_le_prod' (fun i _ => hlocal i)
    _ = ENNReal.ofReal (Real.exp (∑ i ∈ S, Real.log (V i))) := by
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (hV i))]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact hlogs.sum_le_tsum S (fun i _ => Real.log_nonneg (hV i))

end ConfigurationSplitting

section ActualTiles

variable {d : ℕ} [NeZero d]

/-- Exact actual weighted-point integration in the paper's native floor/height
coordinates, for any measurable configuration region. -/
theorem weightedPointLaw_floorHeight_region (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    {A : Set (FloorHeightConfiguration n d)} (hA : MeasurableSet A) :
    Measure.pi (fun _ : Fin n => weightedPointLaw sigma c)
        (gaussianToFloorHeight n ⁻¹' A) =
      ∫⁻ p in A, ENNReal.ofReal (flooredPartitionKernel n sigma c p)
        ∂floorHeightReference n d := by
  have hmp : MeasurePreserving (gaussianToFloorHeight (d := d) n) (gaussianSampleLaw n d)
      ((floorSampleGaussianLaw n d).prod (heightSampleGaussianLaw n)) :=
    ⟨(gaussianToFloorHeight_continuous n).measurable, gaussianToFloorHeight_law n⟩
  rw [weightedPointLaw_product n sigma c hc,
    withDensity_apply _ ((gaussianToFloorHeight_continuous n).measurable hA)]
  have h := hmp.setLIntegral_comp_preimage hA
    (floorHeightWeight_continuous n sigma c).measurable.ennreal_ofReal
  change (∫⁻ g in gaussianToFloorHeight n ⁻¹' A,
    ENNReal.ofReal (gaussianWeight n sigma c g) ∂gaussianSampleLaw n d) = _ at h
  rw [h, floorHeightGaussianLaw_withDensity,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (floorHeightGaussianDensity_measurable n d)
      (floorHeightWeight_continuous n sigma c).measurable.ennreal_ofReal hA]
  apply lintegral_congr
  intro p
  exact flooredPartitionKernel_density_identity n sigma c p

theorem weightedPointLaw_floor_region_antichain (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    {B : Set (FloorSpace (Fin d))} (hB : MeasurableSet B) :
    realizedAntichainMass (fun g : CubePoint d => g)
        ((weightedPointLaw sigma c).restrict (actualFloor ⁻¹' B)) n =
      ∫⁻ p in flooredTileEvent B n, ENNReal.ofReal (flooredPartitionKernel n sigma c p)
        ∂floorHeightReference n d := by
  letI := weightedPointLaw_isFiniteMeasure sigma c hc
  unfold realizedAntichainMass
  rw [← Measure.restrict_pi_pi (fun _ : Fin n => weightedPointLaw sigma c)
    (fun _ => actualFloor ⁻¹' B),
    Measure.restrict_apply (realizedAntichainEvent_measurable
      (fun g : CubePoint d => g) (fun i => measurable_pi_apply i) (Fin n))]
  have heq : realizedAntichainEvent (fun g : CubePoint d => g) (Fin n) ∩
      Set.univ.pi (fun _ : Fin n => actualFloor ⁻¹' B) =
      gaussianToFloorHeight n ⁻¹' flooredTileEvent B n := by
    ext g
    change IsAntichain g ∧ (g ∈ Set.univ.pi (fun _ : Fin n => actualFloor ⁻¹' B)) ↔ _
    simp only [Set.mem_univ_pi, Set.mem_preimage, flooredTileEvent, Set.mem_setOf_eq,
      gaussianToFloorHeight, flooredAntichainEvent]
    change (IsAntichain g ∧ ∀ i, actualFloor (g i) ∈ B) ↔
      (∀ i, actualFloor (g i) ∈ B) ∧
        flooredPointCloud n (gaussianToFloorHeight n g) ∈ strictAntichainEvent n d
    rw [flooredPointCloud_gaussianToFloorHeight]
    exact and_comm
  rw [heq]
  exact weightedPointLaw_floorHeight_region n sigma c hc (flooredTileEvent_measurable hB n)

theorem actual_tile_antichainMass_bound (hd : 2 ≤ d) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    {epsilon c : ℝ} (hepsilon : 0 < epsilon) (hc : c < 1 / 2)
    (B : AlcoveTile d) (n : ℕ) :
    realizedAntichainMass (fun g : CubePoint d => g)
        ((weightedPointLaw sigma c).restrict (actualFloor ⁻¹' alcoveCell d epsilon B)) n ≤
      ENNReal.ofReal (alcoveWeightSup sigma epsilon B) ^ n *
        ENNReal.ofReal (tileCoefficient d epsilon c n) := by
  cases n with
  | zero => rw [realizedAntichainMass_card_zero, tileCoefficient_zero]; simp
  | succ r =>
    rw [weightedPointLaw_floor_region_antichain (r + 1) sigma c hc
      (measurableSet_alcoveCell d hd epsilon B)]
    have hsub : flooredTileEvent (alcoveCell d epsilon B) (r + 1) ⊆
        flooredTileEvent (scaledAlcove d epsilon B) (r + 1) :=
      fun p hp => ⟨fun j => alcoveCell_subset d epsilon B (hp.1 j), hp.2⟩
    calc
      _ ≤ ∫⁻ p in flooredTileEvent (scaledAlcove d epsilon B) (r + 1),
          ENNReal.ofReal (flooredPartitionKernel (r + 1) sigma c p)
          ∂floorHeightReference (r + 1) d :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) (fun _ => le_rfl)
      _ ≤ _ := by
        obtain ⟨word, hword⟩ := B.property
        have htile : scaledAlcove d epsilon B = epsilon • reflectionTile d word := by
          rw [scaledAlcove, hword]
          rfl
        rw [htile]
        apply oneTile_model_bound_of_upperWeight hd word r epsilon hepsilon sigma c hc
        intro u hu
        have hs := (alcoveWeightSup_attained hd sigma epsilon B).choose_spec.2.2
        exact hs u (htile.symm ▸ hu)

theorem actual_tile_configurationPartition_bound (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hc : c < 1 / 2) (ht : 0 ≤ t) (B : AlcoveTile d) :
    configurationPartition (fun g : CubePoint d => g)
        ((weightedPointLaw sigma c).restrict (actualFloor ⁻¹' alcoveCell d epsilon B))
        (ENNReal.ofReal t) ≤
      ENNReal.ofReal (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B)) := by
  have hw := (alcoveWeightSup_pos hd sigma epsilon B).le
  have hseries := tileSeries_summable hd hepsilon hc (mul_nonneg ht hw)
  have hnonneg (n : ℕ) : 0 ≤ tileCoefficient d epsilon c n *
      (t * alcoveWeightSup sigma epsilon B) ^ n / (n.factorial : ℝ) :=
    div_nonneg (mul_nonneg (tileCoefficient_pos hd hepsilon hc n).le
      (pow_nonneg (mul_nonneg ht hw) n)) (by positivity)
  unfold tileGeneratingFunction exponentialGeneratingFunction configurationPartition
  rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hseries]
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ ENNReal.ofReal t ^ n / (n.factorial : ℝ≥0∞) *
        (ENNReal.ofReal (alcoveWeightSup sigma epsilon B) ^ n *
          ENNReal.ofReal (tileCoefficient d epsilon c n)) :=
      mul_le_mul_left' (actual_tile_antichainMass_bound hd sigma hepsilon hc B n) _
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity),
        ENNReal.ofReal_mul (tileCoefficient_pos hd hepsilon hc n).le,
        ENNReal.ofReal_pow (mul_nonneg ht hw), ENNReal.ofReal_mul ht, mul_pow,
        ENNReal.ofReal_natCast]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Full source exponential product inequality for the actual Gaussian model.
The sole external input is the explicitly cited geometric alcove theorem.
The logarithmic sum on the right is independently proved summable. -/
theorem weightedPartitionSeries_le_exp_tileLogs (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 < t) :
    (∑' n : ℕ, ENNReal.ofReal t ^ n / (n.factorial : ℝ≥0∞) * weightedPartitionMass n sigma c) ≤
      ENNReal.ofReal (Real.exp (∑' B : AlcoveTile d,
        Real.log (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B)))) := by
  letI := weightedPointLaw_isFiniteMeasure sigma c hc
  let tn : ℝ≥0 := ⟨t, ht.le⟩
  have htcoe : (tn : ℝ≥0∞) = ENNReal.ofReal t :=
    (ENNReal.ofReal_eq_coe_nnreal ht.le).symm
  have hp : 0 < ((d : ℝ) - 1) / (d : ℝ) := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_pos (by linarith) (by linarith)
  have hlogs := tileSeries_weighted_logs_summable hd hepsilon hc
    (alcoveWeightSup sigma epsilon) (fun B => alcoveWeightSup_pos hd sigma epsilon B)
    (alcoveWeightSup_rpow_summable hd H sigma hp hepsilon hepsilon1) ht
  have hcover : (⋃ B : AlcoveTile d, actualFloor ⁻¹' alcoveCell d epsilon B) = Set.univ := by
    rw [← Set.preimage_iUnion, alcoveCell_covers d H hepsilon, Set.preimage_univ]
  let A : Set (FiniteConfiguration (CubePoint d)) :=
    configurationEvent (fun n => realizedAntichainEvent (fun g : CubePoint d => g) (Fin n))
  have hA : MeasurableSet A := configurationEvent_measurable _
    (fun n => realizedAntichainEvent_measurable (fun g : CubePoint d => g)
      (fun i => measurable_pi_apply i) (Fin n))
  have hhered : ∀ (U : Set (CubePoint d)) z, z ∈ A → configurationRestriction U z ∈ A := by
    intro U z hz
    let S := configurationRestrictionIndices U z.2
    change IsAntichain z.2 at hz
    change IsAntichain (fun j => z.2 (S.orderIsoOfFin rfl j))
    intro j k hjk
    apply hz _ _
    intro heq
    apply hjk
    apply (S.orderIsoOfFin rfl).injective
    exact Subtype.ext heq
  have hlocal (B : AlcoveTile d) :
      configurationSeriesMeasure (tn : ℝ≥0∞)
        ((weightedPointLaw sigma c).restrict (actualFloor ⁻¹' alcoveCell d epsilon B)) A ≤
      ENNReal.ofReal (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B)) := by
    rw [htcoe]
    change configurationSeriesMeasure _ _
      (configurationEvent (fun n => realizedAntichainEvent (fun g : CubePoint d => g) (Fin n))) ≤ _
    rw [← configurationPartition_eq_seriesMeasure (fun g : CubePoint d => g)
      (fun i => measurable_pi_apply i)]
    exact actual_tile_configurationPartition_bound hd sigma hepsilon hc ht.le B
  have h := configurationSeriesMeasure_countable_le_exp_sum_poisson
    (weightedPointLaw sigma c) (fun B => actualFloor ⁻¹' alcoveCell d epsilon B)
    (fun B => actualFloor_continuous.measurable (measurableSet_alcoveCell d hd epsilon B))
    (fun B C hBC => (alcoveCell_pairwise_disjoint d epsilon hBC).preimage actualFloor)
    hcover tn A hA hhered
    (fun B => tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B))
    (fun B => tileGeneratingFunction_one_le hd hepsilon hc
      (mul_nonneg ht.le (alcoveWeightSup_pos hd sigma epsilon B).le)) hlogs hlocal
  rw [htcoe] at h
  change configurationSeriesMeasure _ _
    (configurationEvent (fun n => realizedAntichainEvent (fun g : CubePoint d => g) (Fin n))) ≤ _ at h
  rw [← configurationPartition_eq_seriesMeasure (fun g : CubePoint d => g)
    (fun i => measurable_pi_apply i)] at h
  convert h using 1
  unfold configurationPartition
  apply tsum_congr
  intro n
  rw [show realizedAntichainMass (fun g : CubePoint d => g) (weightedPointLaw sigma c) n =
      weightedPartitionMass n sigma c from weightedPointLaw_antichain n sigma c hc]

theorem weightedPartitionSeries_summable (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 < t) :
    Summable (fun n : ℕ => weightedPartition n sigma c * t ^ n / (n.factorial : ℝ)) := by
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (weightedPartitionSeries_le_exp_tileLogs hd H sigma hepsilon hepsilon1 hc ht)
  have hs := ENNReal.summable_toReal hfinite
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ht.le, ENNReal.toReal_natCast, ENNReal.toReal_inv, weightedPartition,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs

/-- Ordinary-real generating-series version of the full product bound. -/
theorem weightedPartitionSeries_real_le_exp_tileLogs (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 < t) :
    (∑' n : ℕ, weightedPartition n sigma c * t ^ n / (n.factorial : ℝ)) ≤
      Real.exp (∑' B : AlcoveTile d,
        Real.log (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B))) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (weightedPartitionSeries_le_exp_tileLogs hd H sigma hepsilon hepsilon1 hc ht)
  have htermfinite (n : ℕ) : ENNReal.ofReal t ^ n / (n.factorial : ℝ≥0∞) *
      weightedPartitionMass n sigma c ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by positivity))
      (weightedPartitionMass_lt_top n sigma c hc).ne
  rw [ENNReal.tsum_toReal_eq htermfinite,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ht.le, ENNReal.toReal_natCast, ENNReal.toReal_inv, weightedPartition,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- The source coefficient bound, with the actual summable logarithmic product
and no partition, independence or probability-transfer hypotheses. -/
theorem weightedPartition_le_factorial_exp_tileLogs (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 < t) :
    weightedPartition n sigma c ≤ (n.factorial : ℝ) / t ^ n *
      Real.exp (∑' B : AlcoveTile d,
        Real.log (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B))) := by
  have hs := weightedPartitionSeries_summable hd H sigma hepsilon hepsilon1 hc ht
  have hterm := hs.le_tsum n (fun k _ => by
    exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg ht.le k)) (by positivity))
  have h := hterm.trans (weightedPartitionSeries_real_le_exp_tileLogs
    hd H sigma hepsilon hepsilon1 hc ht)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos ht n)).mpr
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hh := (div_le_iff₀ hfac).mp h
  simpa only [mul_comm] using hh

theorem weightedPartitionMass_empty (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartitionMass 0 sigma c = 1 := by
  simp [weightedPartitionMass, strictAntichainEvent_zero, gaussianWeight, gaussianWeightExponent]

theorem weightedPartition_empty (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartition 0 sigma c = 1 := by
  rw [weightedPartition, weightedPartitionMass_empty, ENNReal.toReal_one]

/-- Real-valued source Poissonization equality, including `t = 0`. The Poisson
law and normalized iid mark laws on the left were constructed explicitly. -/
theorem weightedPoisson_partition_expansion_real (hd : 2 ≤ d) (t : ℝ≥0)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Real.exp ((t : ℝ) * (unrestrictedSinglePointMass sigma c).toReal) *
        (weightedPoissonLaw t sigma c (poissonAntichainEvent d)).toReal =
      ∑' n : ℕ, weightedPartition n sigma c * (t : ℝ) ^ n / (n.factorial : ℝ) := by
  have h := congrArg ENNReal.toReal (weightedPoisson_partition_expansion hd t sigma c hc)
  have hterm (n : ℕ) : (t : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) *
      weightedPartitionMass n sigma c ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by positivity))
      (weightedPartitionMass_lt_top n sigma c hc).ne
  rw [ENNReal.tsum_toReal_eq hterm] at h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.coe_toReal, ENNReal.toReal_natCast, ENNReal.toReal_inv, weightedPartition,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- The same identity with the literal source intensity `Lambda`, whose exact
floor/height integral is produced by `OnePointIntegral`. -/
theorem weightedPoisson_source_expansion (hd : 2 ≤ d) (t : ℝ≥0)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) :
    Real.exp ((t : ℝ) *
        ((∫ u : FloorSpace (Fin d), standardFloorDensity u * Real.exp (sigma u)) /
          Real.sqrt (1 - 2 * c))) *
        (weightedPoissonLaw t sigma c (poissonAntichainEvent d)).toReal =
      ∑' n : ℕ, weightedPartition n sigma c * (t : ℝ) ^ n / (n.factorial : ℝ) := by
  simpa only [unrestrictedSinglePointMass_exact] using
    weightedPoisson_partition_expansion_real hd t sigma c hc

/-- Genuine convergence of the actual fixed-size partition series, proved from
the finite Poisson probability construction without any tiling input. -/
theorem weightedPartitionSeries_summable_of_nonneg (hd : 2 ≤ d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {c t : ℝ} (hc : c < 1 / 2) (ht : 0 ≤ t) :
    Summable (fun n : ℕ => weightedPartition n sigma c * t ^ n / (n.factorial : ℝ)) := by
  let tNN : ℝ≥0 := ⟨t, ht⟩
  letI := weightedPoissonLaw_isProbabilityMeasure hd tNN sigma c hc
  have hfinite : (∑' n : ℕ, (tNN : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) *
      weightedPartitionMass n sigma c) ≠ ⊤ := by
    rw [← weightedPoisson_partition_expansion hd tNN sigma c hc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hs := ENNReal.summable_toReal hfinite
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.coe_toReal, ENNReal.toReal_natCast, ENNReal.toReal_inv, weightedPartition,
    tNN, NNReal.coe_mk, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs

theorem tileGeneratingFunction_zero (d : ℕ) (epsilon c : ℝ) :
    tileGeneratingFunction d epsilon c 0 = 1 := by
  unfold tileGeneratingFunction exponentialGeneratingFunction
  rw [tsum_eq_single 0]
  · simp [tileCoefficient_zero]
  · intro n hn
    rw [zero_pow hn, mul_zero, zero_div]

theorem weightedPartitionSeries_real_zero (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    (∑' n : ℕ, weightedPartition n sigma c * (0 : ℝ) ^ n / (n.factorial : ℝ)) = 1 := by
  rw [tsum_eq_single 0]
  · simp [weightedPartition_empty]
  · intro n hn
    rw [zero_pow hn, mul_zero, zero_div]

/-- The paper's literal countable product converges to the exponential of its
summable logarithms. Thus the product is a genuine finite number. -/
theorem actual_tile_product_hasProd (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 ≤ t) :
    HasProd (fun B : AlcoveTile d => tileGeneratingFunction d epsilon c
      (t * alcoveWeightSup sigma epsilon B))
      (Real.exp (∑' B : AlcoveTile d,
        Real.log (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B)))) := by
  have hlogs : Summable (fun B : AlcoveTile d =>
      Real.log (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B))) := by
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · simp only [← ht0, zero_mul, tileGeneratingFunction_zero, Real.log_one]
      exact summable_zero
    · have hp : 0 < ((d : ℝ) - 1) / (d : ℝ) := by
        have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
        exact div_pos (by linarith) (by linarith)
      exact tileSeries_weighted_logs_summable hd hepsilon hc
        (alcoveWeightSup sigma epsilon) (fun B => alcoveWeightSup_pos hd sigma epsilon B)
        (alcoveWeightSup_rpow_summable hd H sigma hp hepsilon hepsilon1) htpos
  exact Real.hasProd_of_hasSum_log
    (fun B => lt_of_lt_of_le zero_lt_one (tileGeneratingFunction_one_le hd hepsilon hc
      (mul_nonneg ht (alcoveWeightSup_pos hd sigma epsilon B).le))) hlogs.hasSum

theorem actual_tile_product_eq_exp_sum (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 ≤ t) :
    (∏' B : AlcoveTile d, tileGeneratingFunction d epsilon c
      (t * alcoveWeightSup sigma epsilon B)) =
      Real.exp (∑' B : AlcoveTile d,
        Real.log (tileGeneratingFunction d epsilon c (t * alcoveWeightSup sigma epsilon B))) :=
  (actual_tile_product_hasProd hd H sigma hepsilon hepsilon1 hc ht).tprod_eq

/-- Full actual source Lemma 4.3 generating-series inequality, including zero
activity, with the literal convergent product over distinct geometric tiles. -/
theorem weightedPartitionSeries_le_tileProduct (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 ≤ t) :
    (∑' n : ℕ, weightedPartition n sigma c * t ^ n / (n.factorial : ℝ)) ≤
      ∏' B : AlcoveTile d, tileGeneratingFunction d epsilon c
        (t * alcoveWeightSup sigma epsilon B) := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · simp only [← ht0, zero_mul, tileGeneratingFunction_zero, weightedPartitionSeries_real_zero,
      tprod_one, le_refl]
  · rw [actual_tile_product_eq_exp_sum hd H sigma hepsilon hepsilon1 hc ht]
    exact weightedPartitionSeries_real_le_exp_tileLogs hd H sigma hepsilon hepsilon1 hc htpos

theorem weightedPartition_le_factorial_tileProduct (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) {epsilon c t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hc : c < 1 / 2) (ht : 0 < t) :
    weightedPartition n sigma c ≤ (n.factorial : ℝ) / t ^ n *
      ∏' B : AlcoveTile d, tileGeneratingFunction d epsilon c
        (t * alcoveWeightSup sigma epsilon B) := by
  rw [actual_tile_product_eq_exp_sum hd H sigma hepsilon hepsilon1 hc ht.le]
  exact weightedPartition_le_factorial_exp_tileLogs hd H n sigma hepsilon hepsilon1 hc ht

end ActualTiles


end Antichain
