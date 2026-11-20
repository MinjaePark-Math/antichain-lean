import Antichain.RankCounting
import Antichain.FinalIntervalApplication
import Antichain.RankShapeTransfer

/-! Actual reflected rank limits for every orientation of a forbidden pair. -/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology BoundedContinuousFunction

set_option maxHeartbeats 800000

def signedAvoidanceRankSet (n m : ℕ) (sign : Fin m → Bool) :
    Set (Fin m → Equiv.Perm (Fin n)) := {pi | AvoidsSignedPair sign pi}

def uniformSignedAvoidanceLaw (n m : ℕ) (sign : Fin m → Bool) :
    Measure (Fin m → Equiv.Perm (Fin n)) := uniformOn (signedAvoidanceRankSet n m sign)

theorem avoidancePermutation_nonempty (n m : ℕ) (hm : 1 ≤ m) : Nonempty (AvoidancePermutation n m) := by
  refine ⟨⟨fun _ => Fin.revPerm, ?_⟩⟩
  intro j k hjk h
  exact (not_lt_of_gt (Fin.rev_strictAnti hjk)) (h ⟨0, by omega⟩)

theorem uniformSignedAvoidanceLaw_reflect (n m : ℕ) (hm : 1 ≤ m) (sign : Fin m → Bool) :
    (uniformSignedAvoidanceLaw n m sign).map (reflectRankTuple sign) =
      uniformOn (avoidanceRankSet n m) := by
  letI : Nonempty (AvoidancePermutation n m) := avoidancePermutation_nonempty n m hm
  letI : Nonempty (SignedAvoidancePermutation n m sign) :=
    ⟨(signedAvoidanceEquiv n m sign).symm (Classical.choice (avoidancePermutation_nonempty n m hm))⟩
  letI : Fintype (signedAvoidanceRankSet n m sign) := signedAvoidancePermutation_fintype n m sign
  letI : Nonempty (signedAvoidanceRankSet n m sign) := inferInstanceAs (Nonempty (SignedAvoidancePermutation n m sign))
  letI : Fintype (avoidanceRankSet n m) := avoidancePermutation_fintype n m
  letI : Nonempty (avoidanceRankSet n m) := inferInstanceAs (Nonempty (AvoidancePermutation n m))
  rw [uniformSignedAvoidanceLaw, ← finite_uniform_subtype_map_uniformOn (signedAvoidanceRankSet n m sign),
    Measure.map_map (measurable_of_finite _) measurable_subtype_coe]
  change ((PMF.uniformOfFintype (SignedAvoidancePermutation n m sign)).toMeasure).map
    ((Subtype.val : AvoidancePermutation n m → (Fin m → Equiv.Perm (Fin n))) ∘
      signedAvoidanceEquiv n m sign) = _
  rw [← Measure.map_map measurable_subtype_coe (measurable_of_finite _),
    (finite_uniform_equiv_measurePreserving (signedAvoidanceEquiv n m sign)).map_eq]
  exact finite_uniform_subtype_map_uniformOn (avoidanceRankSet n m)

theorem uniformSignedAvoidanceLaw_isProbabilityMeasure (n m : ℕ) (hm : 1 ≤ m) (sign : Fin m → Bool) :
    IsProbabilityMeasure (uniformSignedAvoidanceLaw n m sign) := by
  have hne : (signedAvoidanceRankSet n m sign).Nonempty := by
    obtain ⟨pi⟩ := avoidancePermutation_nonempty n m hm
    exact ⟨((signedAvoidanceEquiv n m sign).symm pi).val,
      ((signedAvoidanceEquiv n m sign).symm pi).property⟩
  exact uniformOn_isProbabilityMeasure (Set.toFinite _) hne

def signedCubeReflection (m : ℕ) (sign : Fin m → Bool) (x : CubePoint (m + 1)) : CubePoint (m + 1) :=
  Fin.cons (x 0) (fun i => if sign i then x i.succ else 1 - x i.succ)

theorem signedCubeReflection_continuous (m : ℕ) (sign : Fin m → Bool) :
    Continuous (signedCubeReflection m sign) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact continuous_apply 0
  · cases hs : sign k <;> simp only [signedCubeReflection, Fin.cons_succ, hs, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub (continuous_apply k.succ)
    · exact continuous_apply k.succ

theorem signedCubeReflection_involutive (m : ℕ) (sign : Fin m → Bool) :
    Function.Involutive (signedCubeReflection m sign) := by
  intro x
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · cases hs : sign k <;> simp [signedCubeReflection, hs]

theorem signedCubeReflection_mem_cube (m : ℕ) (sign : Fin m → Bool) (x : CubePoint (m + 1))
    (hx : x ∈ cubePointSet (m + 1)) : signedCubeReflection m sign x ∈ cubePointSet (m + 1) := by
  intro i _
  refine Fin.cases ?_ (fun k => ?_) i
  · exact hx 0 (mem_univ _)
  · have hk := hx k.succ (mem_univ _)
    change (if sign k then x k.succ else 1 - x k.succ) ∈ Icc (0 : ℝ) 1
    cases hs : sign k
    · change 1 - x k.succ ∈ Icc (0 : ℝ) 1
      constructor <;> linarith [hk.1, hk.2]
    · exact hk

theorem permutationRankCloud_reflect (n m : ℕ) (sign : Fin m → Bool)
    (pi : Fin m → Equiv.Perm (Fin n)) :
    permutationRankCloud n m (reflectRankTuple sign pi) =
      fun j => signedCubeReflection m sign (permutationRankCloud n m pi j) := by
  funext j i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · cases hs : sign k <;> simp [permutationRankCloud, rankCenterCloud, reflectRankTuple,
      signedCubeReflection, hs, Equiv.trans_apply, Fin.revPerm_apply, rankMidpoint_rev]

def signedCubeProbabilityMap (m : ℕ) (sign : Fin m → Bool)
    (nu : ProbabilityMeasure (CubePoint (m + 1))) : ProbabilityMeasure (CubePoint (m + 1)) :=
  nu.map (signedCubeReflection_continuous m sign).measurable.aemeasurable

theorem signedCubeProbabilityMap_continuous (m : ℕ) (sign : Fin m → Bool) :
    Continuous (signedCubeProbabilityMap m sign) :=
  ProbabilityMeasure.continuous_map (signedCubeReflection_continuous m sign)

def signedLimitingCubeProbability (m : ℕ) (sign : Fin m → Bool) :
    ProbabilityMeasure (CubePoint (m + 1)) :=
  signedCubeProbabilityMap m sign (limitingCubeProbability (m + 1))

theorem permutationRankEmpiricalProbability_reflect (n m : ℕ) (hn : 0 < n)
    (sign : Fin m → Bool) (pi : Fin m → Equiv.Perm (Fin n)) :
    permutationRankEmpiricalProbability n m (reflectRankTuple sign pi) =
      signedCubeProbabilityMap m sign (permutationRankEmpiricalProbability n m pi) := by
  apply Subtype.ext
  change empiricalCubeMeasure n (m + 1) (permutationRankCloud n m (reflectRankTuple sign pi)) =
    (empiricalCubeMeasure n (m + 1) (permutationRankCloud n m pi)).map (signedCubeReflection m sign)
  rw [empiricalCubeMeasure_map_continuous hn _ (signedCubeReflection_continuous m sign),
    permutationRankCloud_reflect]

theorem signed_rank_empirical_weak_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankEmpiricalProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  have hV : signedCubeProbabilityMap m sign ⁻¹' U ∈ 𝓝 (limitingCubeProbability (m + 1)) :=
    ((signedCubeProbabilityMap_continuous m sign).tendsto (limitingCubeProbability (m + 1))).eventually hU
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_empirical_weak_concentration hm H DKW hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  rw [← uniformSignedAvoidanceLaw_reflect n m hm sign,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hn
  convert hn using 1
  congr 1
  ext pi
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have heq := permutationRankEmpiricalProbability_reflect n m hnpos sign (reflectRankTuple sign pi)
  rw [reflectRankTuple_involutive] at heq
  rw [← heq]

theorem signed_rank_empirical_test_tail {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) (sign : Fin m → Bool)
    (g : CubePoint (m + 1) →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | epsilon ≤
        |(∫ u, g u ∂(permutationRankEmpiricalProbability n m pi : Measure (CubePoint (m + 1)))) -
          ∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1)))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  let U : Set (ProbabilityMeasure (CubePoint (m + 1))) :=
    {nu | |(∫ u, g u ∂(nu : Measure (CubePoint (m + 1)))) -
      ∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1)))| < epsilon}
  have hUopen : IsOpen U :=
    isOpen_lt ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).sub continuous_const).abs
      continuous_const
  have hUmem : signedLimitingCubeProbability m sign ∈ U := by
    simp only [U, Set.mem_setOf_eq, sub_self, abs_zero]
    exact hepsilon
  obtain ⟨alpha, ha, htail⟩ := signed_rank_empirical_weak_concentration hm H DKW sign (hUopen.mem_nhds hUmem)
  refine ⟨alpha, ha, ?_⟩
  simpa only [U, Set.mem_setOf_eq, not_lt] using htail

theorem signed_rank_box_test_tail {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) (sign : Fin m → Bool)
    (g : CubePoint (m + 1) →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | epsilon ≤
        |(∫ u, g u ∂(permutationRankBoxProbability n m pi : Measure (CubePoint (m + 1)))) -
          ∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1)))|} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := signed_rank_empirical_test_tail hm H DKW sign g
    (show 0 < epsilon / 2 by positivity)
  have herr := rankBoxProbability_test_error (m + 1) g (show 0 < epsilon / 4 by positivity)
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail, herr] with n hn hnerror
  apply le_trans (measure_mono ?_) hn
  intro pi hbad
  have he := hnerror (Fin.cons (Equiv.refl (Fin n)) pi)
  change |(∫ u, g u ∂(permutationRankBoxProbability n m pi : Measure (CubePoint (m + 1)))) -
    ∫ u, g u ∂(permutationRankEmpiricalProbability n m pi : Measure (CubePoint (m + 1)))| ≤ epsilon / 4 at he
  have htri := abs_sub_le
    (∫ u, g u ∂(permutationRankBoxProbability n m pi : Measure (CubePoint (m + 1))))
    (∫ u, g u ∂(permutationRankEmpiricalProbability n m pi : Measure (CubePoint (m + 1))))
    (∫ u, g u ∂(signedLimitingCubeProbability m sign : Measure (CubePoint (m + 1))))
  change epsilon ≤ _ at hbad
  change epsilon / 2 ≤ _
  linarith

theorem signed_rank_box_weak_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  apply weak_concentration_of_test_tails (fun n => uniformSignedAvoidanceLaw n m sign)
    (fun n pi => permutationRankBoxProbability n m pi) (signedLimitingCubeProbability m sign) ?_ hU
  intro g epsilon hepsilon
  exact signed_rank_box_test_tail hm H DKW sign g hepsilon

theorem signed_rank_permuton_exponential_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (CubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | permutationRankEmpiricalProbability n m pi ∉ U ∨
        permutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  let A : Bool → ∀ n : ℕ, Set (Fin m → Equiv.Perm (Fin n)) := fun b n =>
    if b then {pi | permutationRankEmpiricalProbability n m pi ∉ U}
    else {pi | permutationRankBoxProbability n m pi ∉ U}
  have hA (b : Bool) : ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign (A b n) ≤ ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
    cases b
    · exact signed_rank_box_weak_concentration hm H DKW sign hU
    · exact signed_rank_empirical_weak_concentration hm H DKW sign hU
  obtain ⟨alpha, ha, htail⟩ := finite_union_exponential_tail
    (fun n => uniformSignedAvoidanceLaw n m sign) A hA
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  apply le_trans (measure_mono ?_) hn
  intro pi hpi
  rcases hpi with hpi | hpi
  · exact Set.mem_iUnion.mpr ⟨true, hpi⟩
  · exact Set.mem_iUnion.mpr ⟨false, hpi⟩

def signedEuclideanReflection (m : ℕ) (sign : Fin m → Bool)
    (x : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (signedCubeReflection m sign (WithLp.ofLp x))

theorem signedEuclideanReflection_isometry (m : ℕ) (sign : Fin m → Bool) :
    Isometry (signedEuclideanReflection m sign) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · change dist (if sign k then x k.succ else 1 - x k.succ)
      (if sign k then y k.succ else 1 - y k.succ) = dist (x k.succ) (y k.succ)
    cases hs : sign k
    · change dist (1 - x k.succ) (1 - y k.succ) = dist (x k.succ) (y k.succ)
      rw [Real.dist_eq, Real.dist_eq,
        show (1 - x k.succ) - (1 - y k.succ) = -(x k.succ - y k.succ) by ring, abs_neg]
    · rfl

theorem signedEuclideanReflection_involutive (m : ℕ) (sign : Fin m → Bool) :
    Function.Involutive (signedEuclideanReflection m sign) := by
  intro x
  change WithLp.toLp 2 (signedCubeReflection m sign (signedCubeReflection m sign (WithLp.ofLp x))) = x
  rw [signedCubeReflection_involutive, WithLp.toLp_ofLp]

def signedEuclideanIsometryEquiv (m : ℕ) (sign : Fin m → Bool) :
    EuclideanSpace ℝ (Fin (m + 1)) ≃ᵢ EuclideanSpace ℝ (Fin (m + 1)) where
  toEquiv :=
    { toFun := signedEuclideanReflection m sign
      invFun := signedEuclideanReflection m sign
      left_inv := signedEuclideanReflection_involutive m sign
      right_inv := signedEuclideanReflection_involutive m sign }
  isometry_toFun := signedEuclideanReflection_isometry m sign

def signedEuclideanLimitShape (m : ℕ) (sign : Fin m → Bool) :
    Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  signedEuclideanReflection m sign '' closure
    ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
      normalQuantileSurface (Fin (m + 1)))

theorem signedEuclideanLimitShape_eq_closure_reflectedSurface (m : ℕ) (sign : Fin m → Bool) :
    signedEuclideanLimitShape m sign = closure
      (signedEuclideanReflection m sign ''
        ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
          normalQuantileSurface (Fin (m + 1)))) := by
  exact (signedEuclideanIsometryEquiv m sign).toHomeomorph.image_closure _

def permutationEuclideanRankSet (n m : ℕ) (pi : Fin m → Equiv.Perm (Fin n)) :
    Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  euclideanSampleSet n (m + 1) (permutationRankCloud n m pi)

theorem permutationEuclideanRankSet_reflect (n m : ℕ) (sign : Fin m → Bool)
    (pi : Fin m → Equiv.Perm (Fin n)) :
    permutationEuclideanRankSet n m (reflectRankTuple sign pi) =
      signedEuclideanReflection m sign '' permutationEuclideanRankSet n m pi := by
  rw [permutationEuclideanRankSet, permutationRankCloud_reflect]
  change Set.range ((signedEuclideanReflection m sign) ∘
    (fun j => WithLp.toLp 2 (permutationRankCloud n m pi j))) = _
  rw [Set.range_comp]
  rfl

theorem permutationEuclideanRankSet_normalized (n m : ℕ) (x : CubeSample n (m + 1)) :
    permutationEuclideanRankSet n m (cubeNormalizedRanks n m x) = euclideanRankSampleSet n (m + 1) x := by
  let r := coordinateRankPermutations n (m + 1) x
  have hcloud : permutationRankCloud n m (cubeNormalizedRanks n m x) =
      fun j => cubeRankCloud n (m + 1) x ((r 0).symm j) := by
    funext j i
    change rankMidpoint n ((Fin.cons (Equiv.refl (Fin n)) (normalizeRankTuple n m r) :
      Fin (m + 1) → Equiv.Perm (Fin n)) i j) = rankMidpoint n (r i ((r 0).symm j))
    rw [normalized_rank_coordinate]
  rw [permutationEuclideanRankSet, hcloud]
  change Set.range ((fun j => WithLp.toLp 2 (cubeRankCloud n (m + 1) x j)) ∘ (r 0).symm) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr (r 0).symm.surjective, Set.image_univ]
  rfl

theorem permutation_rank_euclidean_shape_exponential_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformOn (avoidanceRankSet n m) {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi)
        (closure ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
          normalQuantileSurface (Fin (m + 1))))} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := rank_euclidean_shape_exponential_concentration
    (show 2 ≤ m + 1 by omega) H DKW hepsilon
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← cubeAntichain_normalizedRanks_uniformOn n m,
    Measure.map_apply (cubeNormalizedRanks_measurable n m) (Set.toFinite _).measurableSet]
  simpa only [Set.preimage_setOf_eq, permutationEuclideanRankSet_normalized] using hn

/-- The literal reflected Euclidean limit shape under actual uniform
avoidance of any prescribed two-point orientation. -/
theorem signed_rank_euclidean_shape_exponential_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) (sign : Fin m → Bool)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign
        {pi | epsilon < hausdorffDist (permutationEuclideanRankSet n m pi) (signedEuclideanLimitShape m sign)} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  obtain ⟨alpha, ha, htail⟩ := permutation_rank_euclidean_shape_exponential_concentration hm H DKW hepsilon
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  rw [← uniformSignedAvoidanceLaw_reflect n m hm sign,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hn
  have hdist (pi : Fin m → Equiv.Perm (Fin n)) :
      hausdorffDist (permutationEuclideanRankSet n m pi) (signedEuclideanLimitShape m sign) =
        hausdorffDist (permutationEuclideanRankSet n m (reflectRankTuple sign pi))
          (closure ((WithLp.toLp 2 : CubePoint (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) ''
            normalQuantileSurface (Fin (m + 1)))) := by
    rw [signedEuclideanLimitShape,
      ← reflectRankTuple_involutive sign pi, permutationEuclideanRankSet_reflect,
      hausdorffDist_image (signedEuclideanReflection_isometry m sign),
      reflectRankTuple_involutive]
  simpa only [Set.preimage_setOf_eq, hdist] using hn

def signedClosedLimitingCubeProbability (m : ℕ) (sign : Fin m → Bool) :
    ProbabilityMeasure (ClosedCubePoint (m + 1)) :=
  projectClosedCubeProbability (m + 1) (signedLimitingCubeProbability m sign)

def closedPermutationRankEmpiricalProbability (n m : ℕ) (pi : Fin m → Equiv.Perm (Fin n)) :
    ProbabilityMeasure (ClosedCubePoint (m + 1)) :=
  projectClosedCubeProbability (m + 1) (permutationRankEmpiricalProbability n m pi)

def closedPermutationRankBoxProbability (n m : ℕ) (pi : Fin m → Equiv.Perm (Fin n)) :
    ProbabilityMeasure (ClosedCubePoint (m + 1)) :=
  projectClosedCubeProbability (m + 1) (permutationRankBoxProbability n m pi)

theorem include_signedClosedLimitingCubeProbability (m : ℕ) (sign : Fin m → Bool) :
    includeClosedCubeProbability (m + 1) (signedClosedLimitingCubeProbability m sign) =
      signedLimitingCubeProbability m sign := by
  apply include_projectClosedCubeProbability_of_ae
  apply (ae_map_iff (signedCubeReflection_continuous m sign).measurable.aemeasurable
    (measurableSet_cubePointSet (m + 1))).mpr
  filter_upwards [limitingAntichainMeasure_mem_closed_cube (ι := Fin (m + 1))] with x hx
  exact signedCubeReflection_mem_cube m sign x (fun i _ => hx i)

theorem include_closedPermutationRankEmpiricalProbability (n m : ℕ)
    (pi : Fin m → Equiv.Perm (Fin n)) :
    includeClosedCubeProbability (m + 1) (closedPermutationRankEmpiricalProbability n m pi) =
      permutationRankEmpiricalProbability n m pi :=
  include_projectClosedCubeProbability_of_ae (m + 1) _
    (empiricalCubeProbability_ae_mem_cube n (m + 1) _
      (rankCenterCloud_mem_cube n (m + 1) (Fin.cons (Equiv.refl (Fin n)) pi)))

theorem include_closedPermutationRankBoxProbability (n m : ℕ)
    (pi : Fin m → Equiv.Perm (Fin n)) :
    includeClosedCubeProbability (m + 1) (closedPermutationRankBoxProbability n m pi) =
      permutationRankBoxProbability n m pi :=
  include_projectClosedCubeProbability_of_ae (m + 1) _
    (rankBoxMeasure_ae_mem_cube n (m + 1) (Fin.cons (Equiv.refl (Fin n)) pi))

/-- The weak part of the introduction's symmetry assertion, in the literal
closed-cube probability space, for actual uniform signed-avoidance classes. -/
theorem signed_rank_closed_cube_permuton_concentration {m : ℕ} (hm : 1 ≤ m)
    (H : HumphreysAlcoveInput (m + 1)) (DKW : DKWInput) (sign : Fin m → Bool)
    {U : Set (ProbabilityMeasure (ClosedCubePoint (m + 1)))}
    (hU : U ∈ 𝓝 (signedClosedLimitingCubeProbability m sign)) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ᶠ n : ℕ in atTop,
      uniformSignedAvoidanceLaw n m sign {pi | closedPermutationRankEmpiricalProbability n m pi ∉ U ∨
        closedPermutationRankBoxProbability n m pi ∉ U} ≤
        ENNReal.ofReal (Real.exp (-alpha * (n : ℝ))) := by
  change U ∈ 𝓝 (projectClosedCubeProbability (m + 1) (signedLimitingCubeProbability m sign)) at hU
  have hV : projectClosedCubeProbability (m + 1) ⁻¹' U ∈ 𝓝 (signedLimitingCubeProbability m sign) :=
    ((projectClosedCubeProbability_continuous (m + 1)).tendsto (signedLimitingCubeProbability m sign)).eventually hU
  obtain ⟨alpha, ha, htail⟩ := signed_rank_permuton_exponential_concentration hm H DKW sign hV
  refine ⟨alpha, ha, ?_⟩
  filter_upwards [htail] with n hn
  change uniformSignedAvoidanceLaw n m sign
    {pi | projectClosedCubeProbability (m + 1) (permutationRankEmpiricalProbability n m pi) ∉ U ∨
      projectClosedCubeProbability (m + 1) (permutationRankBoxProbability n m pi) ∉ U} ≤ _ at hn
  exact hn

end Antichain
