import Antichain.GaussianSample
import Antichain.FloorSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp

/-!
Actual weighted antichain partition functions for the Gaussian sample.
The floor is the native Euclidean orthogonal projection and the height is
the signed coordinate along the unit diagonal. Finiteness below the Gaussian
threshold is proved from the Gaussian density and independent-coordinate law.
-/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- The scalar quadratic exponential moment is integrable precisely below
the positive Gaussian threshold needed here. -/
theorem integrable_exp_mul_sq_standardGaussian (c : ℝ) (hc : c < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (c * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))).mpr
  have hi := (integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) - c by linarith)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  ext x
  simp only [smul_eq_mul, toReal_gaussianPDF, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integrable_exp_sum_sq_gaussianPoint (d : ℕ) (c : ℝ) (hc : c < 1 / 2) :
    Integrable (fun g : CubePoint d => Real.exp (c * ∑ i, g i ^ 2))
      (gaussianPointLaw d) := by
  have h := Integrable.fintype_prod (fun _ : Fin d =>
    integrable_exp_mul_sq_standardGaussian c hc)
  convert h using 1
  ext g
  rw [← Real.exp_sum, ← Finset.mul_sum]

theorem integrable_exp_sum_sq_gaussianSample (n d : ℕ) (c : ℝ) (hc : c < 1 / 2) :
    Integrable (fun g : CubeSample n d => Real.exp (c * ∑ j, ∑ i, g j i ^ 2))
      (gaussianSampleLaw n d) := by
  have h := Integrable.fintype_prod (fun _ : Fin n =>
    integrable_exp_sum_sq_gaussianPoint d c hc)
  convert h using 1
  ext g
  rw [← Real.exp_sum, ← Finset.mul_sum]

variable {d : ℕ} [NeZero d]

/-- The actual signed Gaussian height `<g,e>`, with `e_i=1/sqrt d`. -/
def actualHeight (g : CubePoint d) : ℝ := (∑ i, g i) / Real.sqrt (d : ℝ)

/-- The actual Euclidean floor projection, in the native zero-sum subspace. -/
def actualFloor (g : CubePoint d) : FloorSpace (Fin d) :=
  centeredFloor (WithLp.toLp 2 g)

omit [NeZero d] in
@[fun_prop] theorem actualHeight_continuous : Continuous (actualHeight (d := d)) := by
  unfold actualHeight
  fun_prop

@[fun_prop] theorem actualFloor_continuous : Continuous (actualFloor (d := d)) := by
  apply Continuous.subtype_mk
  change Continuous (fun g : CubePoint d =>
    WithLp.toLp 2 (fun i => g i - (∑ j, g j) / (Fintype.card (Fin d) : ℝ)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  fun_prop

theorem actualHeight_sq_le_sum_sq (g : CubePoint d) :
    actualHeight g ^ 2 ≤ ∑ i, g i ^ 2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := g)
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  rw [actualHeight, div_pow, Real.sq_sqrt hd.le]
  exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hs)

/-- The exact real exponent in the paper's definition of `Z_n(sigma,c)`. -/
def gaussianWeightExponent (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (g : CubeSample n d) : ℝ :=
  ∑ j, (sigma (actualFloor (g j)) + c * actualHeight (g j) ^ 2)

def gaussianWeight (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (g : CubeSample n d) : ℝ := Real.exp (gaussianWeightExponent n sigma c g)

@[fun_prop] theorem gaussianWeightExponent_continuous (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    Continuous (gaussianWeightExponent n sigma c) := by
  unfold gaussianWeightExponent
  fun_prop

@[fun_prop] theorem gaussianWeight_continuous (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) : Continuous (gaussianWeight n sigma c) :=
  Real.continuous_exp.comp (gaussianWeightExponent_continuous n sigma c)

theorem gaussianWeight_pos (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ)
    (g : CubeSample n d) : 0 < gaussianWeight n sigma c g := Real.exp_pos _

def weightedPartitionMass (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ g in strictAntichainEvent n d, ENNReal.ofReal (gaussianWeight n sigma c g)
    ∂gaussianSampleLaw n d

def weightedPartition (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) : ℝ :=
  (weightedPartitionMass n sigma c).toReal

/-- Exact agreement with the paper's expectation over uniform cube
antichains, using the actual inverse-normal coordinates. -/
theorem weightedPartitionMass_eq_cube (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartitionMass n sigma c =
      ∫⁻ x in strictAntichainEvent n d,
        ENNReal.ofReal (gaussianWeight n sigma c (cubeToGaussianSample n d x))
          ∂cubeSampleLaw n d :=
  (cube_antichain_lintegral_eq_gaussian n d _
    (gaussianWeight_continuous n sigma c).measurable.ennreal_ofReal).symm

theorem weightedPartition_eq_gaussian_integral (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    weightedPartition n sigma c =
      ∫ g in strictAntichainEvent n d, gaussianWeight n sigma c g ∂gaussianSampleLaw n d := by
  symm
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun g => (gaussianWeight_pos n sigma c g).le))
    (gaussianWeight_continuous n sigma c).measurable.aestronglyMeasurable

theorem weightedPartitionMass_zero (n : ℕ) :
    weightedPartitionMass (d := d) n 0 0 = antichainMass n d := by
  simp only [weightedPartitionMass, gaussianWeight, gaussianWeightExponent,
    BoundedContinuousFunction.coe_zero, Pi.zero_apply, zero_mul, add_zero,
    Finset.sum_const_zero, Real.exp_zero, ENNReal.ofReal_one, lintegral_one,
    Measure.restrict_apply_univ]
  exact gaussianSampleLaw_antichainEvent_eq_mass n d

theorem weightedPartition_zero (n : ℕ) :
    weightedPartition (d := d) n 0 0 = antichainProbability n d := by
  rw [weightedPartition, weightedPartitionMass_zero]
  rfl

theorem gaussianWeightExponent_le (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (g : CubeSample n d) :
    gaussianWeightExponent n sigma c g ≤
      (n : ℝ) * ‖sigma‖ + max c 0 * ∑ j, ∑ i, g j i ^ 2 := by
  have hpoint (j : Fin n) : c * actualHeight (g j) ^ 2 ≤
      max c 0 * ∑ i, g j i ^ 2 := by
    calc
      c * actualHeight (g j) ^ 2 ≤ max c 0 * actualHeight (g j) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ max c 0 * ∑ i, g j i ^ 2 :=
        mul_le_mul_of_nonneg_left (actualHeight_sq_le_sum_sq (g j)) (le_max_right _ _)
  calc
    gaussianWeightExponent n sigma c g ≤ ∑ j, (‖sigma‖ + max c 0 * ∑ i, g j i ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact add_le_add (sigma.apply_le_norm _) (hpoint j)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]

/-- Genuine Gaussian integrability for every bounded continuous floor weight
and every `c < 1/2`, without an integrability hypothesis. -/
theorem gaussianWeight_integrable (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) :
    Integrable (gaussianWeight n sigma c) (gaussianSampleLaw n d) := by
  have hlambda : max c 0 < (1 / 2 : ℝ) := max_lt_iff.mpr ⟨hc, by norm_num⟩
  have hi := (integrable_exp_sum_sq_gaussianSample n d (max c 0) hlambda).const_mul
    (Real.exp ((n : ℝ) * ‖sigma‖))
  apply hi.mono' (gaussianWeight_continuous n sigma c).measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro g
  rw [Real.norm_of_nonneg (gaussianWeight_pos n sigma c g).le]
  calc
    gaussianWeight n sigma c g ≤
        Real.exp ((n : ℝ) * ‖sigma‖ + max c 0 * ∑ j, ∑ i, g j i ^ 2) :=
      Real.exp_le_exp.mpr (gaussianWeightExponent_le n sigma c g)
    _ = _ := Real.exp_add _ _

theorem weightedPartitionMass_lt_top (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) : weightedPartitionMass n sigma c < ⊤ := by
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun g => (gaussianWeight_pos n sigma c g).le))).mp
  exact (gaussianWeight_integrable n sigma c hc).integrableOn.hasFiniteIntegral

theorem weightedPartitionMass_pos (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hd : 2 ≤ d) : 0 < weightedPartitionMass n sigma c := by
  have hsupport : Function.support (fun g : CubeSample n d =>
      ENNReal.ofReal (gaussianWeight n sigma c g)) = Set.univ := by
    ext g
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (gaussianWeight_pos n sigma c g)).ne'
  rw [weightedPartitionMass, setLIntegral_pos_iff
    (gaussianWeight_continuous n sigma c).measurable.ennreal_ofReal,
    hsupport, Set.univ_inter]
  exact gaussianSampleLaw_antichainEvent_pos n d hd

theorem weightedPartition_pos (n : ℕ) (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (c : ℝ) (hc : c < 1 / 2) (hd : 2 ≤ d) : 0 < weightedPartition n sigma c :=
  ENNReal.toReal_pos (weightedPartitionMass_pos n sigma c hd).ne'
    (weightedPartitionMass_lt_top n sigma c hc).ne

/-- The actual Gaussian sample conditioned on its strict-antichain event. -/
def gaussianAntichainLaw (n d : ℕ) : Measure (CubeSample n d) :=
  (antichainMass n d)⁻¹ • (gaussianSampleLaw n d).restrict (strictAntichainEvent n d)

/-- The actual uniform cube sample conditioned on its strict-antichain event. -/
def cubeAntichainLaw (n d : ℕ) : Measure (CubeSample n d) :=
  (antichainMass n d)⁻¹ • (cubeSampleLaw n d).restrict (strictAntichainEvent n d)

theorem gaussianAntichainLaw_isProbabilityMeasure (n d : ℕ) (hd : 2 ≤ d) :
    IsProbabilityMeasure (gaussianAntichainLaw n d) := by
  constructor
  simp only [gaussianAntichainLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, gaussianSampleLaw_antichainEvent_eq_mass]
  exact ENNReal.inv_mul_cancel (antichainMass_pos n d hd).ne' (antichainMass_ne_top n d)

theorem cubeAntichainLaw_isProbabilityMeasure (n d : ℕ) (hd : 2 ≤ d) :
    IsProbabilityMeasure (cubeAntichainLaw n d) := by
  constructor
  simp only [cubeAntichainLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel (antichainMass_pos n d hd).ne' (antichainMass_ne_top n d)

theorem gaussianToCubeSample_conditional_map_eq (n d : ℕ) :
    (gaussianAntichainLaw n d).map (gaussianToCubeSample n d) = cubeAntichainLaw n d := by
  rw [gaussianAntichainLaw, Measure.map_smul, gaussianToCubeSample_restrict_map_eq]
  rfl

theorem cubeToGaussianSample_conditional_map_eq (n d : ℕ) :
    (cubeAntichainLaw n d).map (cubeToGaussianSample n d) = gaussianAntichainLaw n d := by
  rw [cubeAntichainLaw, Measure.map_smul, cubeToGaussianSample_restrict_map_eq]
  rfl

theorem conditional_gaussianWeight_lintegral (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    (∫⁻ g, ENNReal.ofReal (gaussianWeight n sigma c g) ∂gaussianAntichainLaw n d) =
      (antichainMass n d)⁻¹ * weightedPartitionMass n sigma c := by
  rw [gaussianAntichainLaw, lintegral_smul_measure]
  rfl

/-- Exact conditional exponential-moment/partition-ratio identity.
The separately proved finiteness theorem applies whenever `c < 1/2`. -/
theorem conditional_gaussianWeight_moment_eq_ratio (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    (∫⁻ g, ENNReal.ofReal (gaussianWeight n sigma c g) ∂gaussianAntichainLaw n d).toReal =
      weightedPartition n sigma c / antichainProbability n d := by
  rw [conditional_gaussianWeight_lintegral, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [weightedPartition, antichainProbability, div_eq_mul_inv, mul_comm]

theorem conditional_gaussianWeight_integrable (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2) (hd : 2 ≤ d) :
    Integrable (gaussianWeight n sigma c) (gaussianAntichainLaw n d) :=
  (gaussianWeight_integrable n sigma c hc).integrableOn.smul_measure
    (ENNReal.inv_ne_top.mpr (antichainMass_pos n d hd).ne')

/-- The real conditional MGF identity, with genuine integrability proved
separately above under the same Gaussian threshold as the paper. -/
theorem conditional_gaussianWeight_integral_eq_ratio (n : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) :
    (∫ g, gaussianWeight n sigma c g ∂gaussianAntichainLaw n d) =
      weightedPartition n sigma c / antichainProbability n d := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun g => (gaussianWeight_pos n sigma c g).le))
    (gaussianWeight_continuous n sigma c).measurable.aestronglyMeasurable]
  exact conditional_gaussianWeight_moment_eq_ratio n sigma c

end Antichain
