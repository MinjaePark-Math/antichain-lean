import Antichain.GaussianFloorHeightLaw
import Antichain.GaussianWeighted
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact Gaussian partition integrals in actual unpinned floor/height coordinates. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section ProductDensity

variable {κ E : Type*} [Fintype κ] [MeasureSpace E] [SigmaFinite (volume : Measure E)]

/-- Finite products of actual nonnegative integrable densities have the product
density with respect to product volume. -/
theorem pi_withDensity_ofReal (μ : κ → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : κ → E → ℝ) (hf : ∀ i, Integrable (f i)) (hn : ∀ i x, 0 ≤ f i x)
    (hlaw : ∀ i, μ i = volume.withDensity (fun x => ENNReal.ofReal (f i x))) :
    Measure.pi μ = (volume : Measure (κ → E)).withDensity
      (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ENNReal.ofReal (∏ i, f i (x i))
    ∂((volume : Measure (κ → E)).restrict (Set.univ.pi s))) = _
  rw [volume_pi, Measure.restrict_pi_pi]
  have hprod := Integrable.fintype_prod (fun i => (hf i).restrict (s := s i))
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hn i (x i)))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [hlaw i, withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal ((hf i).restrict (s := s i))
    (Filter.Eventually.of_forall (hn i))

end ProductDensity

variable {d : ℕ} [NeZero d]

abbrev FloorHeightConfiguration (n d : ℕ) := (Fin n → FloorSpace (Fin d)) × (Fin n → ℝ)

def gaussianToFloorHeight (n : ℕ) (g : CubeSample n d) : FloorHeightConfiguration n d :=
  (fun j => actualFloor (g j), fun j => actualHeight (g j))

theorem gaussianToFloorHeight_continuous (n : ℕ) :
    Continuous (gaussianToFloorHeight (d := d) n) := by
  exact (continuous_pi (fun j => actualFloor_continuous.comp (continuous_apply j))).prodMk
    (continuous_pi (fun j => actualHeight_continuous.comp (continuous_apply j)))

def floorSampleGaussianLaw (n d : ℕ) : Measure (Fin n → FloorSpace (Fin d)) :=
  Measure.pi (fun _ : Fin n => radialGaussianMeasure (FloorSpace (Fin d)) 1)

def heightSampleGaussianLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

instance floorSampleGaussianLaw_isProbabilityMeasure (n d : ℕ) :
    IsProbabilityMeasure (floorSampleGaussianLaw n d) := by
  letI : IsProbabilityMeasure (radialGaussianMeasure (FloorSpace (Fin d)) 1) :=
    radialGaussianMeasure_isProbabilityMeasure (by norm_num : (0 : ℝ) < 1)
  unfold floorSampleGaussianLaw
  infer_instance

instance heightSampleGaussianLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (heightSampleGaussianLaw n) := by
  unfold heightSampleGaussianLaw
  infer_instance

/-- Independent sample law under the exact Gaussian floor/height transformation. -/
theorem gaussianToFloorHeight_law (n : ℕ) :
    (gaussianSampleLaw n d).map (gaussianToFloorHeight n) =
      (floorSampleGaussianLaw n d).prod (heightSampleGaussianLaw n) := by
  letI : IsProbabilityMeasure (radialGaussianMeasure (FloorSpace (Fin d)) 1) :=
    radialGaussianMeasure_isProbabilityMeasure (by norm_num : (0 : ℝ) < 1)
  have hpoint : MeasurePreserving (gaussianFloorHeightMap (ι := Fin d))
      (gaussianPointLaw d) ((radialGaussianMeasure (FloorSpace (Fin d)) 1).prod (gaussianReal 0 1)) :=
    ⟨gaussianFloorHeightMap_continuous.measurable, gaussianFloorHeightMap_law⟩
  have hpi := measurePreserving_pi (fun _ : Fin n => gaussianPointLaw d)
    (fun _ : Fin n => (radialGaussianMeasure (FloorSpace (Fin d)) 1).prod (gaussianReal 0 1))
    (fun _ => hpoint)
  have hsplit := measurePreserving_arrowProdEquivProdArrow (FloorSpace (Fin d)) ℝ (Fin n)
    (fun _ => radialGaussianMeasure (FloorSpace (Fin d)) 1) (fun _ => gaussianReal 0 1)
  have hfun :
      (⇑(MeasurableEquiv.arrowProdEquivProdArrow (FloorSpace (Fin d)) ℝ (Fin n)) ∘
        fun g j => gaussianFloorHeightMap (g j)) = gaussianToFloorHeight (d := d) n := by
    funext g
    apply Prod.ext
    · rfl
    · funext j
      change gaussianHeightMap (g j) = actualHeight (g j)
      simp [gaussianHeightMap, actualHeight]
  simpa only [hfun, gaussianSampleLaw, floorSampleGaussianLaw, heightSampleGaussianLaw] using
    (hsplit.comp hpi).map_eq

theorem floorSampleGaussianLaw_withDensity (n d : ℕ) :
    floorSampleGaussianLaw n d = (volume : Measure (Fin n → FloorSpace (Fin d))).withDensity
      (fun f => ENNReal.ofReal (∏ j, standardFloorDensity (f j))) := by
  letI : IsProbabilityMeasure (radialGaussianMeasure (FloorSpace (Fin d)) 1) :=
    radialGaussianMeasure_isProbabilityMeasure (by norm_num : (0 : ℝ) < 1)
  apply pi_withDensity_ofReal
  · intro j
    exact radialGaussianDensity_integrable (by norm_num : (0 : ℝ) < 1)
  · intro j x
    exact (radialGaussianDensity_pos (by norm_num : (0 : ℝ) < 1) x).le
  · intro j
    rfl

theorem heightSampleGaussianLaw_withDensity (n : ℕ) :
    heightSampleGaussianLaw n = (volume : Measure (Fin n → ℝ)).withDensity
      (fun h => ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (h j))) := by
  apply pi_withDensity_ofReal
  · intro j
    exact integrable_gaussianPDFReal 0 1
  · intro j x
    exact gaussianPDFReal_nonneg 0 1 x
  · intro j
    exact gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)

def floorHeightReference (n d : ℕ) : Measure (FloorHeightConfiguration n d) :=
  (volume : Measure (Fin n → FloorSpace (Fin d))).prod (volume : Measure (Fin n → ℝ))

def floorHeightGaussianDensity (n d : ℕ) (p : FloorHeightConfiguration n d) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ j, standardFloorDensity (p.1 j)) *
    ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (p.2 j))

theorem floorProductDensity_measurable (n d : ℕ) :
    Measurable (fun f : Fin n → FloorSpace (Fin d) => ENNReal.ofReal (∏ j, standardFloorDensity (f j))) :=
  (continuous_finset_prod _ (fun j _ =>
    (radialGaussianDensity_continuous 1).comp (continuous_apply j))).measurable.ennreal_ofReal

theorem heightProductDensity_measurable (n : ℕ) :
    Measurable (fun h : Fin n → ℝ => ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (h j))) := by
  apply Measurable.ennreal_ofReal
  exact Finset.measurable_prod _ (fun j _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply j))

theorem floorHeightGaussianDensity_measurable (n d : ℕ) :
    Measurable (floorHeightGaussianDensity n d) :=
  ((floorProductDensity_measurable n d).comp measurable_fst).mul
    ((heightProductDensity_measurable n).comp measurable_snd)

theorem floorHeightGaussianLaw_withDensity (n d : ℕ) :
    (floorSampleGaussianLaw n d).prod (heightSampleGaussianLaw n) =
      (floorHeightReference n d).withDensity (floorHeightGaussianDensity n d) := by
  rw [floorSampleGaussianLaw_withDensity, heightSampleGaussianLaw_withDensity,
    prod_withDensity (floorProductDensity_measurable n d) (heightProductDensity_measurable n)]
  rfl

def flooredPointCloud (n : ℕ) (p : FloorHeightConfiguration n d) : CubeSample n d :=
  fun j i => (p.1 j).val i + p.2 j / Real.sqrt (d : ℝ)

omit [NeZero d] in
theorem flooredPointCloud_continuous (n : ℕ) : Continuous (flooredPointCloud (d := d) n) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  exact (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp continuous_subtype_val).comp
    ((continuous_apply j).comp continuous_fst)).add
    (((continuous_apply j).comp continuous_snd).div_const _)

theorem flooredPointCloud_gaussianToFloorHeight (n : ℕ) (g : CubeSample n d) :
    flooredPointCloud n (gaussianToFloorHeight n g) = g := by
  funext j i
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  change g j i - (∑ k, g j k) / (Fintype.card (Fin d) : ℝ) +
    ((∑ k, g j k) / Real.sqrt (d : ℝ)) / Real.sqrt (d : ℝ) = g j i
  rw [div_div, ← pow_two, Real.sq_sqrt hd.le]
  simp

def flooredAntichainEvent (n d : ℕ) : Set (FloorHeightConfiguration n d) :=
  flooredPointCloud n ⁻¹' strictAntichainEvent n d

omit [NeZero d] in
theorem flooredAntichainEvent_measurable (n : ℕ) :
    MeasurableSet (flooredAntichainEvent n d) :=
  (flooredPointCloud_continuous n).measurable (measurableSet_strictAntichainEvent n d)

theorem gaussianToFloorHeight_preimage_antichainEvent (n : ℕ) :
    gaussianToFloorHeight (d := d) n ⁻¹' flooredAntichainEvent n d = strictAntichainEvent n d := by
  ext g
  change flooredPointCloud n (gaussianToFloorHeight n g) ∈ strictAntichainEvent n d ↔ _
  rw [flooredPointCloud_gaussianToFloorHeight]

def floorHeightWeight (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (p : FloorHeightConfiguration n d) : ℝ :=
  Real.exp (∑ j, (sigma (p.1 j) + c * p.2 j ^ 2))

omit [NeZero d] in
theorem floorHeightWeight_continuous (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    Continuous (floorHeightWeight n sigma c) := by
  unfold floorHeightWeight
  fun_prop

theorem weightedPartitionMass_eq_floorHeightGaussianIntegral (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartitionMass n sigma c =
      ∫⁻ p in flooredAntichainEvent n d, ENNReal.ofReal (floorHeightWeight n sigma c p)
        ∂(floorSampleGaussianLaw n d).prod (heightSampleGaussianLaw n) := by
  have hmp : MeasurePreserving (gaussianToFloorHeight (d := d) n) (gaussianSampleLaw n d)
      ((floorSampleGaussianLaw n d).prod (heightSampleGaussianLaw n)) :=
    ⟨(gaussianToFloorHeight_continuous n).measurable, gaussianToFloorHeight_law n⟩
  have h := hmp.setLIntegral_comp_preimage (flooredAntichainEvent_measurable n)
    (floorHeightWeight_continuous n sigma c).measurable.ennreal_ofReal
  rw [gaussianToFloorHeight_preimage_antichainEvent] at h
  exact h

theorem weightedPartitionMass_eq_floorHeightDensityIntegral (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartitionMass n sigma c =
      ∫⁻ p in flooredAntichainEvent n d,
        floorHeightGaussianDensity n d p * ENNReal.ofReal (floorHeightWeight n sigma c p)
        ∂floorHeightReference n d := by
  rw [weightedPartitionMass_eq_floorHeightGaussianIntegral,
    floorHeightGaussianLaw_withDensity,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (floorHeightGaussianDensity_measurable n d)
      (floorHeightWeight_continuous n sigma c).measurable.ennreal_ofReal
      (flooredAntichainEvent_measurable n)]
  rfl

theorem standardHeightDensity_product (n : ℕ) (h : Fin n → ℝ) :
    (∏ j, gaussianPDFReal 0 1 (h j)) =
      (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-(∑ j, h j ^ 2) / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  have hc : ((Real.sqrt (2 * Real.pi))⁻¹) ^ n = (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    congr 1
    ring
  rw [hc]
  congr 2
  simp_rw [neg_div]
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]

/-- The exact nonnegative kernel in equation (4.1), with its Gaussian height
normalization and unnormalized floor factor. -/
def flooredPartitionKernel (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (p : FloorHeightConfiguration n d) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) *
    Real.exp (-((1 / 2 : ℝ) - c) * ∑ j, p.2 j ^ 2) *
    ∏ j, (standardFloorDensity (p.1 j) * Real.exp (sigma (p.1 j)))

omit [NeZero d] in
theorem flooredPartitionKernel_density_identity (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (p : FloorHeightConfiguration n d) :
    floorHeightGaussianDensity n d p * ENNReal.ofReal (floorHeightWeight n sigma c p) =
      ENNReal.ofReal (flooredPartitionKernel n sigma c p) := by
  have hF : 0 ≤ ∏ j, standardFloorDensity (p.1 j) :=
    Finset.prod_nonneg (fun j _ =>
      (radialGaussianDensity_pos (by norm_num : (0 : ℝ) < 1) (p.1 j)).le)
  have hH : 0 ≤ ∏ j, gaussianPDFReal 0 1 (p.2 j) :=
    Finset.prod_nonneg (fun j _ => gaussianPDFReal_nonneg 0 1 (p.2 j))
  unfold floorHeightGaussianDensity
  rw [← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_mul (mul_nonneg hF hH)]
  congr 1
  rw [standardHeightDensity_product, floorHeightWeight, Finset.sum_add_distrib,
    ← Finset.mul_sum, Real.exp_add]
  unfold flooredPartitionKernel
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  have he : Real.exp (-(∑ j, p.2 j ^ 2) / 2) * Real.exp (c * ∑ j, p.2 j ^ 2) =
      Real.exp (-((1 / 2 : ℝ) - c) * ∑ j, p.2 j ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        (∏ j, standardFloorDensity (p.1 j)) * Real.exp (∑ j, sigma (p.1 j))) *
        (Real.exp (-(∑ j, p.2 j ^ 2) / 2) * Real.exp (c * ∑ j, p.2 j ^ 2)) := by ring
    _ = _ := by rw [he]; ring

/-- The paper's exact floor/height integral representation of the actual
weighted antichain expectation. It holds as an extended nonnegative integral
for every c; GaussianWeighted proves finiteness when c < 1/2. -/
theorem weightedPartitionMass_eq_floorHeightIntegral (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartitionMass n sigma c =
      ∫⁻ p in flooredAntichainEvent n d, ENNReal.ofReal (flooredPartitionKernel n sigma c p)
        ∂floorHeightReference n d := by
  rw [weightedPartitionMass_eq_floorHeightDensityIntegral]
  apply lintegral_congr
  intro p
  exact flooredPartitionKernel_density_identity n sigma c p

omit [NeZero d] in
theorem flooredPartitionKernel_nonneg (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (p : FloorHeightConfiguration n d) : 0 ≤ flooredPartitionKernel n sigma c p := by
  apply mul_nonneg
  · positivity
  · exact Finset.prod_nonneg (fun j _ => mul_nonneg
      (radialGaussianDensity_pos (by norm_num : (0 : ℝ) < 1) (p.1 j)).le (Real.exp_nonneg _))

omit [NeZero d] in
theorem flooredPartitionKernel_continuous (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) : Continuous (flooredPartitionKernel n sigma c) := by
  unfold flooredPartitionKernel
  apply Continuous.mul
  · fun_prop
  · apply continuous_finset_prod
    intro j _
    exact ((radialGaussianDensity_continuous 1).comp
      ((continuous_apply j).comp continuous_fst)).mul
      (Real.continuous_exp.comp (sigma.continuous.comp
        ((continuous_apply j).comp continuous_fst)))

/-- Finiteness of the new coordinate integral is inherited from the proved
actual Gaussian exponential-moment estimate. -/
theorem flooredPartitionKernel_integrableOn (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    IntegrableOn (flooredPartitionKernel n sigma c) (flooredAntichainEvent n d)
      (floorHeightReference n d) := by
  constructor
  · exact (flooredPartitionKernel_continuous n sigma c).measurable.aestronglyMeasurable
  · apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (flooredPartitionKernel_nonneg n sigma c))).mpr
    rw [← weightedPartitionMass_eq_floorHeightIntegral]
    exact weightedPartitionMass_lt_top n sigma c hc

/-- Equation (4.1) as an ordinary real integral, for the exact actual weighted Z. -/
theorem weightedPartition_eq_floorHeightIntegral (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartition n sigma c =
      ∫ p in flooredAntichainEvent n d, flooredPartitionKernel n sigma c p
        ∂floorHeightReference n d := by
  rw [weightedPartition, weightedPartitionMass_eq_floorHeightIntegral]
  symm
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (flooredPartitionKernel_nonneg n sigma c))
    (flooredPartitionKernel_continuous n sigma c).measurable.aestronglyMeasurable

end Antichain
