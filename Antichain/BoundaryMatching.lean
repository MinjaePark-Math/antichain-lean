import Antichain.BoundaryProfiles
import Antichain.GaussianPartitionIntegral
import Antichain.ConfigurationContraction
import Antichain.ConfigurationTube
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.Lattice

/-! Finite-minimum boundary profiles and the measurable matching construction. -/

noncomputable section

namespace Antichain

open Set Metric Finset MeasureTheory
open scoped Topology BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

@[simp] theorem nativeFloorCost_self (u : FloorSpace (Fin d)) : nativeFloorCost u u = 0 := by
  simp [nativeFloorCost]

theorem nativeFloorCost_triangle (u v w : FloorSpace (Fin d)) :
    nativeFloorCost u w ≤ nativeFloorCost u v + nativeFloorCost v w := by
  have heq : (fun i => u.val i - v.val i + (v.val i - w.val i)) =
      (fun i => u.val i - w.val i) := by
    funext i
    ring
  simpa only [nativeFloorCost, heq] using
    heightGauge_add_le (Real.sqrt (d : ℝ)) (fun i => u.val i - v.val i)
      (fun i => v.val i - w.val i)

theorem nativeFloorCost_continuous :
    Continuous (fun p : FloorSpace (Fin d) × FloorSpace (Fin d) => nativeFloorCost p.1 p.2) := by
  unfold nativeFloorCost heightGauge
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  exact continuous_const.mul (((continuous_floor_coordinate i).comp continuous_fst).sub
    ((continuous_floor_coordinate i).comp continuous_snd))

def finiteFloorExtension (n : ℕ) [NeZero n] (p : FloorHeightConfiguration n d)
    (u : FloorSpace (Fin d)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => p.2 j + nativeFloorCost u (p.1 j))

theorem finiteFloorExtension_joint_continuous (n : ℕ) [NeZero n] :
    Continuous (fun p : FloorHeightConfiguration n d × FloorSpace (Fin d) =>
      finiteFloorExtension n p.1 p.2) := by
  unfold finiteFloorExtension
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro j _
  exact (((continuous_apply j).comp continuous_snd).comp continuous_fst).add
    (nativeFloorCost_continuous.comp (continuous_snd.prodMk
      (((continuous_apply j).comp continuous_fst).comp continuous_fst)))

theorem finiteFloorExtension_directed (n : ℕ) [NeZero n] (p : FloorHeightConfiguration n d)
    (u v : FloorSpace (Fin d)) :
    finiteFloorExtension n p u - finiteFloorExtension n p v ≤ nativeFloorCost u v := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j : Fin n => p.2 j + nativeFloorCost v (p.1 j))
  have hu := Finset.inf'_le (fun j : Fin n => p.2 j + nativeFloorCost u (p.1 j))
    (Finset.mem_univ j)
  have htri := nativeFloorCost_triangle u v (p.1 j)
  change finiteFloorExtension n p v = p.2 j + nativeFloorCost v (p.1 j) at hj
  change finiteFloorExtension n p u ≤ p.2 j + nativeFloorCost u (p.1 j) at hu
  rw [hj]
  linarith

theorem finiteFloorExtension_agrees (n : ℕ) [NeZero n] (p : FloorHeightConfiguration n d)
    (hc : ∀ j k, p.2 j - p.2 k ≤ nativeFloorCost (p.1 j) (p.1 k)) (j : Fin n) :
    finiteFloorExtension n p (p.1 j) = p.2 j := by
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun k : Fin n => p.2 k + nativeFloorCost (p.1 j) (p.1 k)) (Finset.mem_univ j)
    simpa only [nativeFloorCost_self, add_zero] using h
  · apply (Finset.le_inf'_iff Finset.univ_nonempty
      (fun k : Fin n => p.2 k + nativeFloorCost (p.1 j) (p.1 k))).mpr
    intro k _
    have h := hc j k
    linarith

/-- A continuous function on the actual compact boundary, carrying the finite
minimum extension used by the source proof. -/
def finiteBoundaryProfile (hd : 2 ≤ d) (n : ℕ) [NeZero n]
    (p : FloorHeightConfiguration n d) : SimplexBoundary d →ᵇ ℝ := by
  letI : CompactSpace (SimplexBoundary d) := simplexBoundary_compactSpace hd
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun u => finiteFloorExtension n p u.val,
      (finiteFloorExtension_joint_continuous n).comp (continuous_const.prodMk continuous_subtype_val)⟩

@[simp] theorem finiteBoundaryProfile_apply (hd : 2 ≤ d) (n : ℕ) [NeZero n]
    (p : FloorHeightConfiguration n d) (u : SimplexBoundary d) :
    finiteBoundaryProfile hd n p u = finiteFloorExtension n p u.val := rfl

/-- Uniform boundary-profile continuity, which makes the finite-net classes
measurable without assuming measurability of an optimizer. -/
theorem finiteBoundaryProfile_continuous (hd : 2 ≤ d) (n : ℕ) [NeZero n] :
    Continuous (finiteBoundaryProfile hd n : FloorHeightConfiguration n d → SimplexBoundary d →ᵇ ℝ) := by
  letI : CompactSpace (SimplexBoundary d) := simplexBoundary_compactSpace hd
  let F : C(FloorHeightConfiguration n d × SimplexBoundary d, ℝ) :=
    ⟨fun p => finiteFloorExtension n p.1 p.2.val,
      (finiteFloorExtension_joint_continuous n).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  exact (ContinuousMap.isometryEquivBoundedOfCompact (SimplexBoundary d) ℝ).continuous.comp
    F.curry.continuous

theorem finiteBoundaryProfile_directional (hd : 2 ≤ d) (n : ℕ) [NeZero n]
    (p : FloorHeightConfiguration n d) (u v : SimplexBoundary d) :
    finiteBoundaryProfile hd n p u - finiteBoundaryProfile hd n p v ≤ nativeFloorCost u.val v.val :=
  finiteFloorExtension_directed n p u.val v.val

theorem flooredAntichainEvent_iff_native_constraints (n : ℕ)
    (p : FloorHeightConfiguration n d) :
    p ∈ flooredAntichainEvent n d ↔
      ∀ j k, p.2 j - p.2 k ≤ nativeFloorCost (p.1 j) (p.1 k) := by
  have h := floor_antichain_iff_height_constraints
    (fun j : Fin n => floorCoordinatesEquiv (p.1 j)) p.2
  simpa only [flooredAntichainEvent, Set.mem_preimage, strictAntichainEvent,
    Set.mem_setOf_eq, flooredPointCloud, Fintype.card_fin, nativeFloorCost, floorDistance,
    floorCoordinatesEquiv] using h

theorem flooredAntichainHeight_lipschitz (hd : 2 ≤ d) (n : ℕ)
    (p : FloorHeightConfiguration n d) (hp : p ∈ flooredAntichainEvent n d) (j k : Fin n) :
    |p.2 j - p.2 k| ≤ Real.sqrt ((d : ℝ) - 1) * ‖p.1 j - p.1 k‖ := by
  have hc := (flooredAntichainEvent_iff_native_constraints n p).mp hp
  have hjk := (hc j k).trans (nativeFloorCost_le_norm hd (p.1 j) (p.1 k))
  have hkj := (hc k j).trans (nativeFloorCost_le_norm hd (p.1 k) (p.1 j))
  rw [norm_sub_rev] at hkj
  exact abs_le.mpr ⟨by linarith, hjk⟩

theorem heights_bounded_of_anchor (hd : 2 ≤ d) (n : ℕ)
    (p : FloorHeightConfiguration n d) (hp : p ∈ flooredAntichainEvent n d)
    (hf : ∀ j, p.1 j ∈ referenceSimplex d) (k : Fin n) (hk : |p.2 k| ≤ 1) :
    ∀ j, |p.2 j| ≤ 1 + 2 * Real.sqrt ((d : ℝ) - 1) * (d : ℝ) := by
  intro j
  have hdist : ‖p.1 j - p.1 k‖ ≤ 2 * (d : ℝ) := by
    exact (norm_sub_le _ _).trans (by
      have hj := norm_le_dimension_of_mem_referenceSimplex hd (hf j)
      have hk := norm_le_dimension_of_mem_referenceSimplex hd (hf k)
      linarith)
  have hlip := (flooredAntichainHeight_lipschitz hd n p hp j k).trans
    (mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg _))
  calc
    |p.2 j| = |(p.2 j - p.2 k) + p.2 k| := by congr 1; ring
    _ ≤ |p.2 j - p.2 k| + |p.2 k| := abs_add_le _ _
    _ ≤ _ := by nlinarith

theorem native_cost_separation_of_boundary_distance (hd : 2 ≤ d)
    (u : FloorSpace (Fin d)) (R : ℝ)
    (hR : ∀ v : SimplexBoundary d, R ≤ dist u v.val) :
    ∀ v : SimplexBoundary d,
      R / Real.sqrt ((d : ℝ) - 1) ≤ nativeFloorCost u v.val ∧
      R / Real.sqrt ((d : ℝ) - 1) ≤ nativeFloorCost v.val u := by
  intro v
  have hroot : 0 ≤ Real.sqrt ((d : ℝ) - 1) := Real.sqrt_nonneg _
  have hnorm : R ≤ ‖u - v.val‖ := by simpa only [dist_eq_norm] using hR v
  have hdiv := div_le_div_of_nonneg_right hnorm hroot
  refine ⟨hdiv.trans (norm_div_sqrt_le_nativeFloorCost hd u v.val), ?_⟩
  rw [norm_sub_rev u v.val] at hdiv
  exact hdiv.trans (norm_div_sqrt_le_nativeFloorCost hd v.val u)

theorem finiteFloorExtension_abs_bound (hd : 2 ≤ d) (n : ℕ) [NeZero n]
    (p : FloorHeightConfiguration n d) (H : ℝ) (_hH : 0 ≤ H)
    (hp : ∀ j, p.1 j ∈ referenceSimplex d) (hh : ∀ j, |p.2 j| ≤ H)
    (u : FloorSpace (Fin d)) (hu : u ∈ referenceSimplex d) :
    |finiteFloorExtension n p u| ≤ H + 2 * Real.sqrt ((d : ℝ) - 1) * (d : ℝ) := by
  have hlo : -H ≤ finiteFloorExtension n p u := by
    apply (Finset.le_inf'_iff Finset.univ_nonempty
      (fun j : Fin n => p.2 j + nativeFloorCost u (p.1 j))).mpr
    intro j _
    have hj := (abs_le.mp (hh j)).1
    have hcost := nativeFloorCost_nonneg u (p.1 j)
    linarith
  let j : Fin n := Classical.arbitrary (Fin n)
  have hnorm : ‖u - p.1 j‖ ≤ 2 * (d : ℝ) := by
    exact (norm_sub_le _ _).trans (by
      have hu' := norm_le_dimension_of_mem_referenceSimplex hd hu
      have hj' := norm_le_dimension_of_mem_referenceSimplex hd (hp j)
      linarith)
  have hcost := (nativeFloorCost_le_norm hd u (p.1 j)).trans
    (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _))
  have hup := Finset.inf'_le
    (fun k : Fin n => p.2 k + nativeFloorCost u (p.1 k)) (Finset.mem_univ j)
  have hhj := (abs_le.mp (hh j)).2
  change finiteFloorExtension n p u ≤ _ at hup
  exact abs_le.mpr ⟨by nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1)], by nlinarith⟩

theorem finiteBoundaryProfile_mem_admissible (hd : 2 ≤ d) (n : ℕ) [NeZero n]
    (p : FloorHeightConfiguration n d) (H : ℝ) (hH : 0 ≤ H)
    (hp : ∀ j, p.1 j ∈ referenceSimplex d) (hh : ∀ j, |p.2 j| ≤ H) :
    finiteBoundaryProfile hd n p ∈
      admissibleBoundaryProfiles d (H + 2 * Real.sqrt ((d : ℝ) - 1) * (d : ℝ)) := by
  refine ⟨?_, finiteBoundaryProfile_directional hd n p⟩
  intro u
  exact finiteFloorExtension_abs_bound hd n p H hH hp hh u.val
    (frontier_subset_closure.trans (isClosed_referenceSimplex d).closure_subset u.property)

/-- Covering by finitely many measurable profile balls yields an actual class
of at least the reciprocal-cardinality fraction of the starting volume. The
balls may overlap, so a measurable choice of first index is unnecessary. -/
theorem exists_large_profile_ball {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MetricSpace Y] (μ : MeasureTheory.Measure X)
    (A : Set X) (hA : MeasurableSet A) (F : X → Y) (hF : Continuous F)
    (reps : Finset Y) (hne : reps.Nonempty) (τ : ℝ)
    (hcover : ∀ x ∈ A, ∃ q ∈ reps, dist (F x) q < τ) :
    ∃ q ∈ reps, MeasurableSet (A ∩ F ⁻¹' Metric.ball q τ) ∧
      μ A ≤ (reps.card : ENNReal) * μ (A ∩ F ⁻¹' Metric.ball q τ) := by
  classical
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image reps
    (fun q => μ (A ∩ F ⁻¹' Metric.ball q τ)) hne
  refine ⟨q, hq, hA.inter ((isOpen_ball.preimage hF).measurableSet), ?_⟩
  have hsub : A ⊆ ⋃ q ∈ reps, A ∩ F ⁻¹' Metric.ball q τ := by
    intro x hx
    obtain ⟨q, hq, hdist⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, ⟨hx, hdist⟩⟩⟩
  calc
    μ A ≤ μ (⋃ q ∈ reps, A ∩ F ⁻¹' Metric.ball q τ) := measure_mono hsub
    _ ≤ ∑ q ∈ reps, μ (A ∩ F ⁻¹' Metric.ball q τ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ reps, μ (A ∩ F ⁻¹' Metric.ball q τ) :=
      Finset.sum_le_sum (fun a ha => hmax a ha)
    _ = _ := by simp

def indexedFloorExtension {I : Type*} (q : I → FloorSpace (Fin d)) (h : I → ℝ)
    (u : FloorSpace (Fin d)) : ℝ :=
  sInf (Set.range (fun i => h i + nativeFloorCost u (q i)))

theorem indexedFloorExtension_values_bddBelow {I : Type*}
    (q : I → FloorSpace (Fin d)) (h : I → ℝ) (hb : BddBelow (Set.range h))
    (u : FloorSpace (Fin d)) :
    BddBelow (Set.range (fun i => h i + nativeFloorCost u (q i))) := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  rintro t ⟨i, rfl⟩
  exact (ha (Set.mem_range_self i)).trans (le_add_of_nonneg_right (nativeFloorCost_nonneg _ _))

theorem indexedFloorExtension_agrees {I : Type*} [Nonempty I]
    (q : I → FloorSpace (Fin d)) (h : I → ℝ) (hb : BddBelow (Set.range h))
    (hc : ∀ i j, h i - h j ≤ nativeFloorCost (q i) (q j)) (i : I) :
    indexedFloorExtension q h (q i) = h i := by
  apply le_antisymm
  · have hh := csInf_le (indexedFloorExtension_values_bddBelow q h hb (q i)) (Set.mem_range_self i)
    simpa only [indexedFloorExtension, nativeFloorCost_self, add_zero] using hh
  · apply le_csInf (Set.range_nonempty _)
    rintro t ⟨j, rfl⟩
    have hh := hc i j
    linarith

theorem indexedFloorExtension_directed {I : Type*} [Nonempty I]
    (q : I → FloorSpace (Fin d)) (h : I → ℝ) (hb : BddBelow (Set.range h))
    (u v : FloorSpace (Fin d)) :
    indexedFloorExtension q h u - indexedFloorExtension q h v ≤ nativeFloorCost u v := by
  have haux : indexedFloorExtension q h u - nativeFloorCost u v ≤ indexedFloorExtension q h v := by
    apply le_csInf (Set.range_nonempty _)
    rintro t ⟨i, rfl⟩
    have hu : indexedFloorExtension q h u ≤ h i + nativeFloorCost u (q i) :=
      csInf_le (indexedFloorExtension_values_bddBelow q h hb u) (Set.mem_range_self i)
    have ht := nativeFloorCost_triangle u v (q i)
    linarith
  linarith

/-- Consistent finite interior heights and a bounded continuous boundary profile
extend together. Possible repeated floor positions are handled by the indexed
infimum, with agreement forced by the actual directional constraints. -/
theorem compatible_interior_boundary_extend (n : ℕ) [NeZero n]
    (p : FloorHeightConfiguration n d) (q : SimplexBoundary d →ᵇ ℝ)
    (hii : ∀ j k, p.2 j - p.2 k ≤ nativeFloorCost (p.1 j) (p.1 k))
    (hbb : ∀ u v, q u - q v ≤ nativeFloorCost u.val v.val)
    (hib : ∀ j v, p.2 j - q v ≤ nativeFloorCost (p.1 j) v.val)
    (hbi : ∀ v j, q v - p.2 j ≤ nativeFloorCost v.val (p.1 j)) :
    ∃ H : FloorSpace (Fin d) → ℝ,
      (∀ j, H (p.1 j) = p.2 j) ∧ (∀ v : SimplexBoundary d, H v.val = q v) ∧
      (∀ u v, H u - H v ≤ nativeFloorCost u v) := by
  let locations : Fin n ⊕ SimplexBoundary d → FloorSpace (Fin d) := Sum.elim p.1 Subtype.val
  let heights : Fin n ⊕ SimplexBoundary d → ℝ := Sum.elim p.2 q
  have hb : BddBelow (Set.range heights) := by
    obtain ⟨a, ha⟩ := (Set.finite_range p.2).bddBelow
    refine ⟨min a (-‖q‖), ?_⟩
    rintro t ⟨i, rfl⟩
    cases i with
    | inl j => exact (min_le_left _ _).trans (ha (Set.mem_range_self j))
    | inr v =>
      have hnorm := BoundedContinuousFunction.norm_coe_le_norm q v
      have hlo : -‖q‖ ≤ q v := by simpa only [Real.norm_eq_abs] using (neg_le_of_abs_le hnorm)
      exact (min_le_right _ _).trans hlo
  have hc : ∀ i j, heights i - heights j ≤ nativeFloorCost (locations i) (locations j) := by
    intro i j
    cases i with
    | inl a => cases j with
      | inl b => exact hii a b
      | inr v => exact hib a v
    | inr u => cases j with
      | inl b => exact hbi u b
      | inr v => exact hbb u v
  refine ⟨indexedFloorExtension locations heights, ?_, ?_, ?_⟩
  · intro j
    exact indexedFloorExtension_agrees locations heights hb hc (Sum.inl j)
  · intro v
    exact indexedFloorExtension_agrees locations heights hb hc (Sum.inr v)
  · exact indexedFloorExtension_directed locations heights hb

theorem contraction_absorbs_profile_error (lam δ τ a b D : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hτ0 : 0 ≤ τ) (hτ : τ ≤ lam * δ)
    (hD : δ ≤ D) (hab : a - b ≤ D + τ) :
    (1 - lam) * a - (1 - lam) * b ≤ D := by
  have hmul := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hlam1)
  have hsmall : (1 - lam) * τ ≤ τ := by nlinarith
  have hslack : τ ≤ lam * D := hτ.trans (mul_le_mul_of_nonneg_left hD hlam0)
  nlinarith

theorem contraction_preserves_directed (lam a b D : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hD : 0 ≤ D) (hab : a - b ≤ D) :
    (1 - lam) * a - (1 - lam) * b ≤ D := by
  have hmul := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hlam1)
  nlinarith

/-- The deterministic matching step of Lemma 5.2: every configuration in the
same uniform-profile ball has, after height contraction, exactly the same
boundary data and an actual directional extension. -/
theorem close_boundary_profile_has_common_extension (hd : 2 ≤ d) (n : ℕ) [NeZero n]
    (p : FloorHeightConfiguration n d) (q : SimplexBoundary d →ᵇ ℝ)
    (lam δ τ : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hτ0 : 0 ≤ τ) (hτ : τ ≤ lam * δ)
    (hclose : dist (finiteBoundaryProfile hd n p) q < τ)
    (hii : ∀ j k, p.2 j - p.2 k ≤ nativeFloorCost (p.1 j) (p.1 k))
    (hbb : ∀ u v, q u - q v ≤ nativeFloorCost u.val v.val)
    (hsep : ∀ (j : Fin n) (v : SimplexBoundary d),
      δ ≤ nativeFloorCost (p.1 j) v.val ∧ δ ≤ nativeFloorCost v.val (p.1 j)) :
    ∃ H : FloorSpace (Fin d) → ℝ,
      (∀ j, H (p.1 j) = (1 - lam) * p.2 j) ∧
      (∀ v : SimplexBoundary d, H v.val = (1 - lam) * q v) ∧
      (∀ u v, H u - H v ≤ nativeFloorCost u v) := by
  let p' : FloorHeightConfiguration n d := (p.1, fun j => (1 - lam) * p.2 j)
  let q' : SimplexBoundary d →ᵇ ℝ := (1 - lam) • q
  apply compatible_interior_boundary_extend n p' q'
  · intro j k
    exact contraction_preserves_directed lam _ _ _ hlam0 hlam1
      (nativeFloorCost_nonneg _ _) (hii j k)
  · intro u v
    exact contraction_preserves_directed lam _ _ _ hlam0 hlam1
      (nativeFloorCost_nonneg _ _) (hbb u v)
  · intro j v
    have hpoint : |finiteBoundaryProfile hd n p v - q v| < τ := by
      exact (BoundedContinuousFunction.dist_coe_le_dist v).trans_lt hclose
    have hdir := finiteFloorExtension_directed n p (p.1 j) v.val
    rw [finiteFloorExtension_agrees n p hii j] at hdir
    have herror := (abs_lt.mp hpoint).2
    exact contraction_absorbs_profile_error lam δ τ _ _ _ hlam0 hlam1 hτ0 hτ (hsep j v).1
      (by change p.2 j - q v ≤ _; change finiteFloorExtension n p v.val - q v < τ at herror; linarith)
  · intro v j
    have hpoint : |finiteBoundaryProfile hd n p v - q v| < τ := by
      exact (BoundedContinuousFunction.dist_coe_le_dist v).trans_lt hclose
    have hdir := finiteFloorExtension_directed n p v.val (p.1 j)
    rw [finiteFloorExtension_agrees n p hii j] at hdir
    have herror := (abs_lt.mp hpoint).1
    exact contraction_absorbs_profile_error lam δ τ _ _ _ hlam0 hlam1 hτ0 hτ (hsep j v).2
      (by change q v - p.2 j ≤ _; change -τ < finiteFloorExtension n p v.val - q v at herror; linarith)

/-- The actual measurable family selected from one profile ball. All geometric,
extension, and exact volume conclusions are proved from properties of the
starting family; the source family itself is constructed from pinned tubes. -/
theorem measurable_matching_family_from_profile_net (hd : 2 ≤ d) (n : ℕ) [NeZero n]
    (A : Set (FloorHeightConfiguration n d)) (hA : MeasurableSet A)
    (H R lam τ : ℝ) (hH : 0 ≤ H) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ lam * (R / Real.sqrt ((d : ℝ) - 1)))
    (hfloor : ∀ p ∈ A, ∀ j, p.1 j ∈ referenceSimplex d)
    (hevent : ∀ p ∈ A, p ∈ flooredAntichainEvent n d)
    (hheight : ∀ p ∈ A, ∀ j, |p.2 j| ≤ H)
    (hmargin : ∀ p ∈ A, ∀ (j : Fin n) (v : SimplexBoundary d), R ≤ dist (p.1 j) v.val)
    (reps : Finset (SimplexBoundary d →ᵇ ℝ)) (hne : reps.Nonempty)
    (hreps : ∀ q ∈ reps,
      q ∈ admissibleBoundaryProfiles d (H + 2 * Real.sqrt ((d : ℝ) - 1) * (d : ℝ)))
    (hcover : ∀ h ∈ admissibleBoundaryProfiles d (H + 2 * Real.sqrt ((d : ℝ) - 1) * (d : ℝ)),
      ∃ q ∈ reps, dist h q < τ) :
    ∃ q ∈ reps, ∃ B : Set (FloorHeightConfiguration n d), MeasurableSet B ∧
      (∀ p ∈ B, (∀ j, p.1 j ∈ referenceSimplex d) ∧ p ∈ flooredAntichainEvent n d) ∧
      (∀ p ∈ B, ∀ j, |p.2 j| ≤ H) ∧
      (∀ p ∈ B, ∀ (j : Fin n) (v : SimplexBoundary d), R ≤ dist (p.1 j) v.val) ∧
      (∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
        (∀ j, E (p.1 j) = p.2 j) ∧ (∀ v : SimplexBoundary d, E v.val = (1 - lam) * q v) ∧
        (∀ u v, E u - E v ≤ nativeFloorCost u v)) ∧
      ENNReal.ofReal (1 - lam) ^ n * ((reps.card : ENNReal)⁻¹ * volume A) ≤ volume B := by
  classical
  have hcoverA : ∀ p ∈ A, ∃ q ∈ reps, dist (finiteBoundaryProfile hd n p) q < τ := by
    intro p hp
    exact hcover _ (finiteBoundaryProfile_mem_admissible hd n p H hH
      (hfloor p hp) (hheight p hp))
  obtain ⟨q, hq, hclass, hlarge⟩ := exists_large_profile_ball volume A hA
    (finiteBoundaryProfile hd n) (finiteBoundaryProfile_continuous hd n) reps hne τ hcoverA
  let S := A ∩ (finiteBoundaryProfile hd n) ⁻¹' Metric.ball q τ
  have hS : MeasurableSet S := hclass
  let T := heightScalingEquiv n d (1 - lam) (sub_pos.mpr hlam1).ne'
  let B := T '' S
  have ht0 : 0 < 1 - lam := sub_pos.mpr hlam1
  have ht1 : 1 - lam ≤ 1 := by linarith
  refine ⟨q, hq, B, T.measurableSet_image.mpr hS, ?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨p₀, hp₀, rfl⟩
    refine ⟨hfloor p₀ hp₀.1, ?_⟩
    apply (flooredAntichainEvent_iff_native_constraints n _).mpr
    intro j k
    exact contraction_preserves_directed lam _ _ _ hlam0 hlam1.le
      (nativeFloorCost_nonneg _ _) (((flooredAntichainEvent_iff_native_constraints n p₀).mp
        (hevent p₀ hp₀.1)) j k)
  · rintro p ⟨p₀, hp₀, rfl⟩ j
    change |(1 - lam) * p₀.2 j| ≤ H
    rw [abs_mul, abs_of_pos ht0]
    exact (mul_le_mul_of_nonneg_left (hheight p₀ hp₀.1 j) ht0.le).trans
      (mul_le_of_le_one_left hH ht1)
  · rintro p ⟨p₀, hp₀, rfl⟩ j v
    exact hmargin p₀ hp₀.1 j v
  · rintro p ⟨p₀, hp₀, rfl⟩
    exact close_boundary_profile_has_common_extension hd n p₀ q lam _ τ hlam0 hlam1.le hτ0 hτ hp₀.2
      ((flooredAntichainEvent_iff_native_constraints n p₀).mp (hevent p₀ hp₀.1))
      (hreps q hq).2
      (fun j => native_cost_separation_of_boundary_distance hd (p₀.1 j) R (hmargin p₀ hp₀.1 j))
  · have hM0 : (reps.card : ENNReal) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hne).ne'
    have hMinv : (reps.card : ENNReal)⁻¹ * volume A ≤ volume S := by
      calc
        _ ≤ (reps.card : ENNReal)⁻¹ * ((reps.card : ENNReal) * volume S) :=
          mul_le_mul_left' hlarge _
        _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hM0 (ENNReal.natCast_ne_top _), one_mul]
    change _ ≤ volume (heightScalingEquiv n d (1 - lam) ht0.ne' '' S)
    rw [heightScalingEquiv_volume n d (1 - lam) ht0 hS]
    exact mul_le_mul_left' hMinv _

omit [NeZero d] in
/-- The matching families have genuine finite ordinary volume, proved from their
actual compact floor region and bounded height coordinates. -/
theorem matching_family_volume_lt_top (hd : 2 ≤ d) (n : ℕ)
    (B : Set (FloorHeightConfiguration n d)) (H : ℝ)
    (hfloor : ∀ p ∈ B, ∀ j, p.1 j ∈ referenceSimplex d)
    (hheight : ∀ p ∈ B, ∀ j, |p.2 j| ≤ H) : volume B < ⊤ := by
  let F : Set (Fin n → FloorSpace (Fin d)) := univ.pi (fun _ => referenceSimplex d)
  let G : Set (Fin n → ℝ) := univ.pi (fun _ => Set.Icc (-H) H)
  have hsub : B ⊆ F ×ˢ G := by
    intro p hp
    exact ⟨fun j _ => hfloor p hp j, fun j _ => abs_le.mp (hheight p hp j)⟩
  have hF : (volume : Measure (Fin n → FloorSpace (Fin d))) F =
      floorVolume (referenceSimplex d) ^ n := by
    simp only [F, volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, floorVolume]
  have hG : (volume : Measure (Fin n → ℝ)) G = ENNReal.ofReal (H - -H) ^ n := by
    simp only [G, volume_pi_pi, Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    volume B ≤ volume (F ×ˢ G) := measure_mono hsub
    _ = floorVolume (referenceSimplex d) ^ n * ENNReal.ofReal (H - -H) ^ n := by
      change ((volume : Measure (Fin n → FloorSpace (Fin d))).prod
        (volume : Measure (Fin n → ℝ))) (F ×ˢ G) = _
      rw [Measure.prod_prod, hF, hG]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top (floorVolume_referenceSimplex_lt_top hd))
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

omit [NeZero d] in
theorem flooredPointCloud_jointConfigurationContraction (n : ℕ)
    (center : FloorSpace (Fin d)) (eta : ℝ) (p : FloorHeightConfiguration n d) :
    flooredPointCloud n (jointConfigurationContraction n center eta p) =
      (fun j i => eta * center.val i + (1 - eta) * flooredPointCloud n p j i) := by
  funext j i
  simp only [flooredPointCloud, jointConfigurationContraction_floor,
    jointConfigurationContraction_height, Submodule.coe_add, Submodule.coe_smul,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

omit [NeZero d] in
theorem jointConfigurationContraction_antichain_iff (n : ℕ)
    (center : FloorSpace (Fin d)) (eta : ℝ) (heta : eta < 1)
    (p : FloorHeightConfiguration n d) :
    jointConfigurationContraction n center eta p ∈ flooredAntichainEvent n d ↔
      p ∈ flooredAntichainEvent n d := by
  change IsAntichain (flooredPointCloud n (jointConfigurationContraction n center eta p)) ↔
    IsAntichain (flooredPointCloud n p)
  rw [flooredPointCloud_jointConfigurationContraction]
  rw [isAntichain_translate_iff
    (fun j i => (1 - eta) * flooredPointCloud n p j i) (fun i => eta * center.val i)]
  exact isAntichain_coordinatewise_iff (strictMono_mul_left_of_pos (sub_pos.mpr heta)) _

theorem contractedTube_matching_data (hd : 2 ≤ d) (eta : ℝ) (heta0 : 0 < eta)
    (heta1 : eta < 1) (r : ℕ) (rho : ℝ)
    (hmargin : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ referenceSimplex d,
      t * rho ≤ infDist (t • referenceSimplexInteriorPoint d + (1 - t) • x)
        (frontier (referenceSimplex d))) :
    ∀ p ∈ contractedTube d eta r,
      (∀ j, p.1 j ∈ referenceSimplex d) ∧ p ∈ flooredAntichainEvent (r + 1) d ∧
      (∀ j, |p.2 j| ≤ 1 + 2 * Real.sqrt ((d : ℝ) - 1) * (d : ℝ)) ∧
      (∀ (j : Fin (r + 1)) (v : SimplexBoundary d), eta * rho ≤ dist (p.1 j) v.val) := by
  rintro p ⟨p₀, hp₀, rfl⟩
  have hf : ∀ j, p₀.1 j ∈ referenceSimplex d := hp₀.1.1
  have he : p₀ ∈ flooredAntichainEvent (r + 1) d := hp₀.1.2
  have hh := heights_bounded_of_anchor hd (r + 1) p₀ he hf 0 (abs_le.mpr hp₀.2)
  have hcenter : referenceSimplexInteriorPoint d ∈ referenceSimplex d :=
    referenceSimplexCore_subset d (referenceSimplexInteriorPoint_mem_core d)
  refine ⟨?_, (jointConfigurationContraction_antichain_iff _ _ eta heta1 p₀).mpr he, ?_, ?_⟩
  · intro j
    exact (convex_referenceSimplex d) hcenter (hf j) heta0.le
      (sub_pos.mpr heta1).le (by ring : eta + (1 - eta) = 1)
  · intro j
    rw [jointConfigurationContraction_height, abs_mul, abs_of_pos (sub_pos.mpr heta1)]
    have hH : 0 ≤ 1 + 2 * Real.sqrt ((d : ℝ) - 1) * (d : ℝ) := by positivity
    exact (mul_le_mul_of_nonneg_left (hh j) (sub_pos.mpr heta1).le).trans
      (mul_le_of_le_one_left hH (by linarith : 1 - eta ≤ 1))
  · intro j v
    have hi := hmargin eta heta0 heta1.le (p₀.1 j) (hf j)
    exact hi.trans (infDist_le_dist_of_mem v.property)

/-- Complete source Lemma 5.2, with constants chosen before the sample count,
actual measurable full-dimensional families, a common boundary profile,
genuine directional extensions, and the stated ordinary-volume lower bound. -/
theorem boundary_matching_source (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eta lam : ℝ, eta ∈ Set.Ioo 0 (1 / 2 : ℝ) →
      lam ∈ Set.Ioo 0 (1 / 2 : ℝ) → ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ,
      ∃ B : Set (FloorHeightConfiguration (r + 1) d), ∃ hBoundary : SimplexBoundary d →ᵇ ℝ,
        MeasurableSet B ∧
        (∀ p ∈ B, (∀ j, p.1 j ∈ referenceSimplex d) ∧ p ∈ flooredAntichainEvent (r + 1) d) ∧
        (∀ p ∈ B, ∀ j, |p.2 j| ≤ C ∧ eta / C ≤ infDist (p.1 j) (frontier (referenceSimplex d))) ∧
        (∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
          (∀ j, E (p.1 j) = p.2 j) ∧ (∀ v : SimplexBoundary d, E v.val = hBoundary v) ∧
          (∀ u v, E u - E v ≤ nativeFloorCost u v)) ∧
        (2 / (M : ℝ)) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
          pinnedVolume (referenceSimplex d) r ≤ (volume B).toReal := by
  obtain ⟨rho, hrho, _hball, hmargin⟩ := referenceSimplex_exists_contraction_radius hd
  let K : ℝ := Real.sqrt ((d : ℝ) - 1)
  let H : ℝ := 1 + 2 * K * (d : ℝ)
  let C₀ : ℝ := H + 2 * K * (d : ℝ)
  let C : ℝ := max C₀ (max 1 (1 / rho))
  have hK : 0 < K := by
    apply Real.sqrt_pos.mpr
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hHC : H ≤ C := by
    apply le_trans (show H ≤ C₀ by
      dsimp [C₀]
      exact le_add_of_nonneg_right (by positivity)) (le_max_left _ _)
  have hC1 : 1 ≤ C := (le_max_left 1 (1 / rho)).trans (le_max_right C₀ _)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCrho : 1 / rho ≤ C := (le_max_right 1 (1 / rho)).trans (le_max_right C₀ _)
  refine ⟨C, hC1, ?_⟩
  intro eta lam heta hlam
  have heta0 := heta.1
  have hlam0 := hlam.1
  have heta1 : eta < 1 := lt_trans heta.2 (by norm_num)
  have hlam1 : lam < 1 := lt_trans hlam.2 (by norm_num)
  let τ : ℝ := lam * eta * rho / (2 * K)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτslack : τ ≤ lam * (eta * rho / K) := by
    dsimp [τ]
    have hpos : 0 ≤ lam * eta * rho := by positivity
    rw [show lam * (eta * rho / K) = (lam * eta * rho) / K by ring]
    exact div_le_div_of_nonneg_left hpos hK (by linarith : K ≤ 2 * K)
  obtain ⟨reps, hne, hreps, hcover⟩ := finite_admissible_boundary_profile_net hd C₀ hC₀ τ hτ
  refine ⟨reps.card, Finset.card_pos.mpr hne, ?_⟩
  intro r
  have hdata := contractedTube_matching_data hd eta heta.1 heta1 r rho hmargin
  obtain ⟨q, hq, B, hB, hBevent, hBheight, hBmargin, hBextend, hBvolume⟩ :=
    measurable_matching_family_from_profile_net hd (r + 1) (contractedTube d eta r)
      (measurableSet_contractedTube d eta heta1 r) H (eta * rho) lam τ hH hlam.1.le hlam1
      hτ.le hτslack (fun p hp => (hdata p hp).1) (fun p hp => (hdata p hp).2.1)
      (fun p hp => (hdata p hp).2.2.1) (fun p hp => (hdata p hp).2.2.2)
      reps hne hreps hcover
  refine ⟨B, (1 - lam) • q, hB, hBevent, ?_, hBextend, ?_⟩
  · intro p hp j
    refine ⟨(hBheight p hp j).trans hHC, ?_⟩
    have hR : eta / C ≤ eta * rho := by
      apply (div_le_iff₀ hCpos).mpr
      have hprod := (div_le_iff₀ hrho).mp hCrho
      have hmul := mul_le_mul_of_nonneg_left hprod heta.1.le
      nlinarith
    apply hR.trans
    apply (le_infDist (referenceSimplex_frontier_nonempty hd)).mpr
    intro v hv
    exact hBmargin p hp j ⟨v, hv⟩
  · have hBfinite := matching_family_volume_lt_top hd (r + 1) B H
      (fun p hp => (hBevent p hp).1) hBheight
    have hreal := ENNReal.toReal_mono hBfinite.ne hBvolume
    rw [contractedTube_volume d eta heta1 r] at hreal
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal (sub_pos.mpr heta1).le,
      ENNReal.toReal_ofReal (sub_pos.mpr hlam1).le, ENNReal.toReal_ofNat] at hreal
    change (1 - lam) ^ (r + 1) * ((reps.card : ℝ)⁻¹ *
      (2 * (1 - eta) ^ (d * (r + 1)) * pinnedVolume (referenceSimplex d) r)) ≤ _ at hreal
    convert hreal using 1
    ring

end Antichain
