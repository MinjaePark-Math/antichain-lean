import Antichain.RankModel
import Antichain.GaussianWeighted
import Antichain.FiniteConditioning

/-!
Uniformity and independence of the actual coordinate ranks, proved from finite
relabeling symmetries of iid samples and measurable rank chambers.
-/

noncomputable section

namespace Antichain

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

theorem finite_uniform_joint_law {Ω K Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace K] [Fintype K] [Nonempty K] [MeasurableSingletonClass K]
    [MeasurableSpace Y] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (R : Ω → K) (S : Ω → Y) (hR : Measurable R) (hS : Measurable S)
    (hfiber : ∀ k : K, ∀ A : Set Y, MeasurableSet A →
      mu (R ⁻¹' {k} ∩ S ⁻¹' A) =
        (Fintype.card K : ℝ≥0∞)⁻¹ * mu (S ⁻¹' A)) :
    mu.map (fun x => (R x, S x)) =
      (PMF.uniformOfFintype K).toMeasure.prod (mu.map S) := by
  classical
  symm
  apply Measure.prod_eq
  intro B A hB hA
  letI : Fintype B := Fintype.ofFinite B
  rw [Measure.map_apply (hR.prodMk hS) (hB.prod hA),
    PMF.toMeasure_uniformOfFintype_apply B hB, Measure.map_apply hS hA]
  have heq : (fun x => (R x, S x)) ⁻¹' (B ×ˢ A) =
      ⋃ k : B, (R ⁻¹' {k.val} ∩ S ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨⟨R x, hx.1⟩, rfl, hx.2⟩
    · rintro ⟨k, hk, hSA⟩
      exact ⟨hk ▸ k.property, hSA⟩
  rw [heq, measure_iUnion, tsum_fintype]
  · simp_rw [hfiber _ A hA]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv, mul_assoc]
  · intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hkl (Subtype.ext (hx.1.symm.trans hy.1))
  · intro k
    exact (hR (measurableSet_singleton k.val)).inter (hS hA)

theorem finite_uniform_marginal_law {Ω K Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace K] [Fintype K] [Nonempty K] [MeasurableSingletonClass K]
    [MeasurableSpace Y] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (R : Ω → K) (S : Ω → Y) (hR : Measurable R) (hS : Measurable S)
    (hjoint : mu.map (fun x => (R x, S x)) =
      (PMF.uniformOfFintype K).toMeasure.prod (mu.map S)) :
    mu.map R = (PMF.uniformOfFintype K).toMeasure := by
  letI : IsProbabilityMeasure (mu.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hfst : MeasurePreserving (Prod.fst : K × Y → K)
      ((PMF.uniformOfFintype K).toMeasure.prod (mu.map S))
      (PMF.uniformOfFintype K).toMeasure := measurePreserving_fst
  rw [← hfst.map_eq, ← hjoint, Measure.map_map measurable_fst (hR.prodMk hS)]
  rfl

theorem scalar_labelPermute_measurePreserving {n : ℕ} (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (e : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → ℝ => fun j => x (e j))
      (Measure.pi (fun _ : Fin n => mu)) (Measure.pi (fun _ : Fin n => mu)) := by
  convert measurePreserving_piCongrLeft (fun _ : Fin n => mu) e.symm using 1
  funext x j
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq,
    Equiv.symm_symm]

theorem trans_perm_eq_self_iff {n : ℕ} (e r : Equiv.Perm (Fin n)) :
    e.trans r = e ↔ r = Equiv.refl _ := by
  constructor
  · intro h
    apply Equiv.ext
    intro j
    have hh := congrArg (fun f : Equiv.Perm (Fin n) => f (e.symm j)) h
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.refl_apply] using hh
  · intro h
    subst r
    rfl

theorem scalar_rank_sorted_fiber_mass (n : ℕ) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NoAtoms mu] (e : Equiv.Perm (Fin n))
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin n => mu))
        (sampleRankPermutation ⁻¹' {e} ∩ sampleSortedValues ⁻¹' A) =
      (n.factorial : ℝ≥0∞)⁻¹ * (Measure.pi (fun _ : Fin n => mu))
        (sampleSortedValues ⁻¹' A) := by
  classical
  let P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => mu)
  let E : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun p =>
    sampleRankPermutation ⁻¹' {p} ∩ sampleSortedValues ⁻¹' A
  have hE (p : Equiv.Perm (Fin n)) : MeasurableSet (E p) :=
    ((sampleRankPermutation_measurable n) (measurableSet_singleton p)).inter
      ((sampleSortedValues_measurable n) hA)
  have hm (p : Equiv.Perm (Fin n)) : P (E p) = P (E (Equiv.refl _)) := by
    have hp := (scalar_labelPermute_measurePreserving mu p).measure_preimage (hE p).nullMeasurableSet
    have hpre : (fun x : Fin n → ℝ => fun j => x (p j)) ⁻¹' E p =ᵐ[P] E (Equiv.refl _) := by
      filter_upwards [iid_scalar_injective_ae n mu] with x hx
      apply propext
      change (sampleRankPermutation (fun j => x (p j)) = p ∧
        sampleSortedValues (fun j => x (p j)) ∈ A) ↔
        (sampleRankPermutation x = Equiv.refl _ ∧ sampleSortedValues x ∈ A)
      rw [sampleRankPermutation_comp_perm x hx p, sampleSortedValues_comp_perm x hx p,
        trans_perm_eq_self_iff]
    exact hp.symm.trans (measure_congr hpre)
  have hcover : (⋃ p : Equiv.Perm (Fin n), E p) = sampleSortedValues ⁻¹' A := by
    ext x
    simp only [Set.mem_iUnion, E, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, _, hx⟩ => hx, fun hx => ⟨sampleRankPermutation x, rfl, hx⟩⟩
  have hdisj : Pairwise (fun p q : Equiv.Perm (Fin n) => Disjoint (E p) (E q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hpq (hx.1.symm.trans hy.1)
  have hsum : P (sampleSortedValues ⁻¹' A) =
      (n.factorial : ℝ≥0∞) * P (E (Equiv.refl _)) := by
    rw [← hcover, measure_iUnion hdisj hE, tsum_fintype]
    simp_rw [hm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  change P (E e) = _
  rw [hm e, hsum, ENNReal.inv_mul_cancel_left (by positivity) (by finiteness)]

/-- Exact independence of a scalar sample's uniform rank permutation and its
actual sorted coordinate values, derived from the atomless iid law. -/
theorem scalar_rank_sorted_joint_law (n : ℕ) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NoAtoms mu] :
    (Measure.pi (fun _ : Fin n => mu)).map
        (fun x => (sampleRankPermutation x, sampleSortedValues x)) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.prod
        ((Measure.pi (fun _ : Fin n => mu)).map sampleSortedValues) := by
  apply finite_uniform_joint_law _ _ _ (sampleRankPermutation_measurable n) (sampleSortedValues_measurable n)
  intro e A hA
  simpa only [Fintype.card_perm, Fintype.card_fin] using scalar_rank_sorted_fiber_mass n mu e A hA

theorem scalar_rank_uniform_law (n : ℕ) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NoAtoms mu] :
    (Measure.pi (fun _ : Fin n => mu)).map sampleRankPermutation =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure :=
  finite_uniform_marginal_law _ _ _ (sampleRankPermutation_measurable n)
    (sampleSortedValues_measurable n) (scalar_rank_sorted_joint_law n mu)

theorem scalar_ranks_independent_sorted_values (n : ℕ) (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NoAtoms mu] :
    IndepFun sampleRankPermutation sampleSortedValues (Measure.pi (fun _ : Fin n => mu)) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (sampleRankPermutation_measurable n).aemeasurable
    (sampleSortedValues_measurable n).aemeasurable).mpr
  rw [scalar_rank_uniform_law]
  exact scalar_rank_sorted_joint_law n mu

def scalarUniformRankLaw (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance scalarUniformRankLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (scalarUniformRankLaw n) := by
  unfold scalarUniformRankLaw
  infer_instance

def scalarSortedLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (Measure.pi (fun _ : Fin n => cubeCoordinateLaw)).map sampleSortedValues

instance scalarSortedLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (scalarSortedLaw n) :=
  Measure.isProbabilityMeasure_map (sampleSortedValues_measurable n).aemeasurable

theorem cube_rank_sorted_joint_law (n d : ℕ) :
    (cubeSampleLaw n d).map (fun x => (coordinateRankPermutations n d x, coordinateSortedValues n d x)) =
      (Measure.pi (fun _ : Fin d => scalarUniformRankLaw n)).prod
        (Measure.pi (fun _ : Fin d => scalarSortedLaw n)) := by
  have hscalar : MeasurePreserving
      (fun x : Fin n → ℝ => (sampleRankPermutation x, sampleSortedValues x))
      (Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
      ((scalarUniformRankLaw n).prod (scalarSortedLaw n)) :=
    ⟨(sampleRankPermutation_measurable n).prodMk (sampleSortedValues_measurable n),
      scalar_rank_sorted_joint_law n cubeCoordinateLaw⟩
  have hpi := measurePreserving_pi
    (fun _ : Fin d => Measure.pi (fun _ : Fin n => cubeCoordinateLaw))
    (fun _ : Fin d => (scalarUniformRankLaw n).prod (scalarSortedLaw n)) (fun _ => hscalar)
  have hsplit := measurePreserving_arrowProdEquivProdArrow (Equiv.Perm (Fin n))
    (Fin n → ℝ) (Fin d) (fun _ => scalarUniformRankLaw n) (fun _ => scalarSortedLaw n)
  have ht := measurePreserving_iid_transpose (I := Fin n) (J := Fin d) cubeCoordinateLaw
  exact ((hsplit.comp hpi).comp ht).map_eq

theorem cube_coordinateRanks_uniform_law (n d : ℕ) :
    (cubeSampleLaw n d).map (coordinateRankPermutations n d) =
      Measure.pi (fun _ : Fin d => scalarUniformRankLaw n) := by
  have hmp : MeasurePreserving (Prod.fst :
      (Fin d → Equiv.Perm (Fin n)) × (Fin d → Fin n → ℝ) → (Fin d → Equiv.Perm (Fin n)))
      ((Measure.pi (fun _ : Fin d => scalarUniformRankLaw n)).prod
        (Measure.pi (fun _ : Fin d => scalarSortedLaw n)))
      (Measure.pi (fun _ : Fin d => scalarUniformRankLaw n)) := measurePreserving_fst
  rw [← hmp.map_eq, ← cube_rank_sorted_joint_law n d,
    Measure.map_map measurable_fst
      ((coordinateRankPermutations_measurable n d).prodMk (coordinateSortedValues_measurable n d))]
  rfl

theorem cube_sortedCoordinates_law (n d : ℕ) :
    (cubeSampleLaw n d).map (coordinateSortedValues n d) =
      Measure.pi (fun _ : Fin d => scalarSortedLaw n) := by
  have hmp : MeasurePreserving (Prod.snd :
      (Fin d → Equiv.Perm (Fin n)) × (Fin d → Fin n → ℝ) → (Fin d → Fin n → ℝ))
      ((Measure.pi (fun _ : Fin d => scalarUniformRankLaw n)).prod
        (Measure.pi (fun _ : Fin d => scalarSortedLaw n)))
      (Measure.pi (fun _ : Fin d => scalarSortedLaw n)) := measurePreserving_snd
  rw [← hmp.map_eq, ← cube_rank_sorted_joint_law n d,
    Measure.map_map measurable_snd
      ((coordinateRankPermutations_measurable n d).prodMk (coordinateSortedValues_measurable n d))]
  rfl

theorem cube_ranks_independent_sorted_values (n d : ℕ) :
    IndepFun (coordinateRankPermutations n d) (coordinateSortedValues n d) (cubeSampleLaw n d) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (coordinateRankPermutations_measurable n d).aemeasurable
    (coordinateSortedValues_measurable n d).aemeasurable).mpr
  rw [cube_coordinateRanks_uniform_law, cube_sortedCoordinates_law]
  exact cube_rank_sorted_joint_law n d

theorem finite_uniform_pi_law {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] :
    Measure.pi (fun _ : I => (PMF.uniformOfFintype K).toMeasure) =
      (PMF.uniformOfFintype (I → K)).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro r
  conv_lhs => rw [← Set.univ_pi_singleton r, Measure.pi_pi]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Nat.cast_pow, ENNReal.inv_pow]

theorem finite_uniform_equiv_measurePreserving {K L : Type*} [Fintype K] [Fintype L]
    [Nonempty K] [Nonempty L] [MeasurableSpace K] [MeasurableSingletonClass K]
    [MeasurableSpace L] [MeasurableSingletonClass L] (e : K ≃ L) :
    MeasurePreserving e (PMF.uniformOfFintype K).toMeasure (PMF.uniformOfFintype L).toMeasure := by
  refine ⟨measurable_of_finite e, ?_⟩
  apply Measure.ext_of_singleton
  intro r
  have hp : e ⁻¹' {r} = {e.symm r} := by
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.eq_symm_apply]
  rw [Measure.map_apply (measurable_of_finite e) (measurableSet_singleton r),
    hp, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- First-coordinate sorting removes the common label order. The remaining
`m` permutations describe a `(m+1)`-dimensional permutation. -/
def normalizeRankTuple (n m : ℕ) (r : Fin (m + 1) → Equiv.Perm (Fin n)) :
    Fin m → Equiv.Perm (Fin n) := fun i => (r 0).symm.trans (r i.succ)

def normalizedRankTupleEquiv (n m : ℕ) :
    (Fin (m + 1) → Equiv.Perm (Fin n)) ≃
      Equiv.Perm (Fin n) × (Fin m → Equiv.Perm (Fin n)) where
  toFun r := (r 0, normalizeRankTuple n m r)
  invFun p := Fin.cons p.1 (fun i => p.1.trans (p.2 i))
  left_inv r := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · apply Equiv.ext
      intro k
      simp [normalizeRankTuple, Equiv.trans_apply]
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      apply Equiv.ext
      intro k
      simp [normalizeRankTuple, Equiv.trans_apply]

def cubeNormalizedRanks (n m : ℕ) (x : CubeSample n (m + 1)) :
    Fin m → Equiv.Perm (Fin n) :=
  normalizeRankTuple n m (coordinateRankPermutations n (m + 1) x)

theorem cubeNormalizedRanks_measurable (n m : ℕ) : Measurable (cubeNormalizedRanks n m) :=
  (measurable_of_finite (normalizeRankTuple n m)).comp (coordinateRankPermutations_measurable n (m + 1))

theorem normalized_uniform_rank_law (n m : ℕ) :
    (Measure.pi (fun _ : Fin (m + 1) => scalarUniformRankLaw n)).map (normalizeRankTuple n m) =
      (PMF.uniformOfFintype (Fin m → Equiv.Perm (Fin n))).toMeasure := by
  rw [show Measure.pi (fun _ : Fin (m + 1) => scalarUniformRankLaw n) =
      (PMF.uniformOfFintype (Fin (m + 1) → Equiv.Perm (Fin n))).toMeasure from finite_uniform_pi_law]
  have he := finite_uniform_equiv_measurePreserving (normalizedRankTupleEquiv n m)
  have hprod : (PMF.uniformOfFintype
      (Equiv.Perm (Fin n) × (Fin m → Equiv.Perm (Fin n)))).toMeasure =
      (scalarUniformRankLaw n).prod
        (PMF.uniformOfFintype (Fin m → Equiv.Perm (Fin n))).toMeasure := by
    symm
    apply Measure.prod_eq
    intro A B hA hB
    letI : Fintype A := Fintype.ofFinite A
    letI : Fintype B := Fintype.ofFinite B
    letI : Fintype (A ×ˢ B) := Fintype.ofFinite (A ×ˢ B)
    unfold scalarUniformRankLaw
    rw [PMF.toMeasure_uniformOfFintype_apply _ (hA.prod hB),
      PMF.toMeasure_uniformOfFintype_apply _ hA, PMF.toMeasure_uniformOfFintype_apply _ hB]
    have hc : Fintype.card (A ×ˢ B) = Fintype.card A * Fintype.card B := by
      exact Fintype.card_congr (Equiv.Set.prod A B) |>.trans (Fintype.card_prod _ _)
    rw [hc, Fintype.card_prod]
    simp only [Nat.cast_mul, div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
    ac_rfl
  have hsnd : MeasurePreserving (Prod.snd :
      Equiv.Perm (Fin n) × (Fin m → Equiv.Perm (Fin n)) → (Fin m → Equiv.Perm (Fin n)))
      ((scalarUniformRankLaw n).prod
        (PMF.uniformOfFintype (Fin m → Equiv.Perm (Fin n))).toMeasure)
      (PMF.uniformOfFintype (Fin m → Equiv.Perm (Fin n))).toMeasure := measurePreserving_snd
  rw [← hsnd.map_eq, ← hprod, ← he.map_eq,
    Measure.map_map measurable_snd (measurable_of_finite (normalizedRankTupleEquiv n m))]
  rfl

theorem cubeNormalizedRanks_uniform_law (n m : ℕ) :
    (cubeSampleLaw n (m + 1)).map (cubeNormalizedRanks n m) =
      (PMF.uniformOfFintype (Fin m → Equiv.Perm (Fin n))).toMeasure := by
  change (cubeSampleLaw n (m + 1)).map
    ((normalizeRankTuple n m) ∘ (coordinateRankPermutations n (m + 1))) = _
  rw [← Measure.map_map (measurable_of_finite (normalizeRankTuple n m))
    (coordinateRankPermutations_measurable n (m + 1)), cube_coordinateRanks_uniform_law]
  exact normalized_uniform_rank_law n m

theorem cubeNormalizedRanks_independent_sorted_values (n m : ℕ) :
    IndepFun (cubeNormalizedRanks n m) (coordinateSortedValues n (m + 1))
      (cubeSampleLaw n (m + 1)) := by
  exact (cube_ranks_independent_sorted_values n (m + 1)).comp
    (measurable_of_finite (normalizeRankTuple n m)) measurable_id

/-- Avoiding the increasing two-point pattern after fixing the first ranking
to the identity. Here `m` is the number of remaining coordinate permutations. -/
def AvoidsIncreasingPair {n m : ℕ} (pi : Fin m → Equiv.Perm (Fin n)) : Prop :=
  ∀ j k : Fin n, j < k → ¬ ∀ i : Fin m, pi i j < pi i k

def avoidanceRankSet (n m : ℕ) : Set (Fin m → Equiv.Perm (Fin n)) :=
  {pi | AvoidsIncreasingPair pi}

abbrev AvoidancePermutation (n m : ℕ) :=
  {pi : Fin m → Equiv.Perm (Fin n) // AvoidsIncreasingPair pi}

instance avoidancePermutation_fintype (n m : ℕ) : Fintype (AvoidancePermutation n m) :=
  Fintype.ofFinite _

theorem measurableSet_avoidanceRankSet (n m : ℕ) : MeasurableSet (avoidanceRankSet n m) :=
  (Set.to_countable _).measurableSet

/-- The literal original sample is an antichain exactly when its actual
first-coordinate-normalized rank tuple avoids the increasing pair. -/
theorem cube_antichain_iff_rank_avoidance (n m : ℕ) (x : CubeSample n (m + 1))
    (hx : CoordinateTieFree n (m + 1) x) :
    IsAntichain x ↔ AvoidsIncreasingPair (cubeNormalizedRanks n m x) := by
  let r := coordinateRankPermutations n (m + 1) x
  have hcoord (i : Fin (m + 1)) (j k : Fin n) : r i j < r i k ↔ x j i < x k i :=
    sampleRankPermutation_lt_iff (fun l => x l i) (hx i) j k
  constructor
  · intro h j k hjk htail
    let e : Equiv.Perm (Fin n) := (r 0).symm
    apply h (e j) (e k) (fun hh => (ne_of_lt hjk) (e.injective hh))
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · apply (hcoord 0 (e j) (e k)).mp
      simpa only [e, Equiv.apply_symm_apply] using hjk
    · apply (hcoord l.succ (e j) (e k)).mp
      exact htail l
  · intro h j k _ hbelow
    apply h (r 0 j) (r 0 k) ((hcoord 0 j k).mpr (hbelow 0))
    intro i
    change r i.succ ((r 0).symm (r 0 j)) < r i.succ ((r 0).symm (r 0 k))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact (hcoord i.succ j k).mpr (hbelow i.succ)

theorem cube_antichainEvent_ae_rank_avoidance (n m : ℕ) :
    strictAntichainEvent n (m + 1) =ᵐ[cubeSampleLaw n (m + 1)]
      (cubeNormalizedRanks n m) ⁻¹' avoidanceRankSet n m := by
  filter_upwards [cubeSample_coordinateTieFree_ae n (m + 1)] with x hx
  exact propext (cube_antichain_iff_rank_avoidance n m x hx)

/-- Exact finite counting identity, derived from actual cube ranks and their
proved uniform law. No counting or rank-probability identity is supplied. -/
theorem antichainMass_eq_avoidance_card_div (n m : ℕ) :
    antichainMass n (m + 1) =
      (Fintype.card (AvoidancePermutation n m) : ℝ≥0∞) /
        (n.factorial : ℝ≥0∞) ^ m := by
  letI : Fintype (avoidanceRankSet n m) := Fintype.ofFinite _
  change (cubeSampleLaw n (m + 1)) (strictAntichainEvent n (m + 1)) = _
  rw [measure_congr (cube_antichainEvent_ae_rank_avoidance n m)]
  rw [← Measure.map_apply (cubeNormalizedRanks_measurable n m)
      (measurableSet_avoidanceRankSet n m), cubeNormalizedRanks_uniform_law,
    PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_avoidanceRankSet n m)]
  simp only [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Nat.cast_pow]
  congr 2

theorem avoidance_card_eq_factorial_mul_antichainProbability (n m : ℕ) :
    (Fintype.card (AvoidancePermutation n m) : ℝ) =
      (n.factorial : ℝ) ^ m * antichainProbability n (m + 1) := by
  have h := congrArg ENNReal.toReal (antichainMass_eq_avoidance_card_div n m)
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast] at h
  change antichainProbability n (m + 1) = _ at h
  rw [h]
  field_simp

/-- Cardinality of the source `d`-dimensional avoidance class, including the
fixed identity ranking. -/
def avoidanceClassCard (n d : ℕ) : ℕ := Fintype.card (AvoidancePermutation n (d - 1))

theorem avoidanceClassCard_exact (n d : ℕ) (hd : 1 ≤ d) :
    (avoidanceClassCard n d : ℝ) =
      (n.factorial : ℝ) ^ (d - 1) * antichainProbability n d := by
  simpa only [Nat.sub_add_cancel hd, avoidanceClassCard] using
    avoidance_card_eq_factorial_mul_antichainProbability n (d - 1)

/-- Antichain conditioning gives exactly the conditional uniform finite rank
law on the actual avoidance class. -/
theorem cubeAntichain_normalizedRanks_law (n m : ℕ) :
    (cubeAntichainLaw n (m + 1)).map (cubeNormalizedRanks n m) =
      (antichainMass n (m + 1))⁻¹ •
        (PMF.uniformOfFintype (Fin m → Equiv.Perm (Fin n))).toMeasure.restrict
          (avoidanceRankSet n m) := by
  rw [cubeAntichainLaw, Measure.map_smul,
    Measure.restrict_congr_set (cube_antichainEvent_ae_rank_avoidance n m),
    ← Measure.restrict_map (cubeNormalizedRanks_measurable n m) (measurableSet_avoidanceRankSet n m),
    cubeNormalizedRanks_uniform_law]

/-- Sorted uniform order statistics keep their exact joint law after actual
antichain conditioning. This is the independence step used with DKW. -/
theorem cubeAntichain_sortedCoordinates_law (n m : ℕ) (hm : 1 ≤ m) :
    (cubeAntichainLaw n (m + 1)).map (coordinateSortedValues n (m + 1)) =
      (cubeSampleLaw n (m + 1)).map (coordinateSortedValues n (m + 1)) := by
  ext A hA
  rw [Measure.map_apply (coordinateSortedValues_measurable n (m + 1)) hA,
    cubeAntichainLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply ((coordinateSortedValues_measurable n (m + 1)) hA),
    Measure.map_apply (coordinateSortedValues_measurable n (m + 1)) hA]
  have heq : ((coordinateSortedValues n (m + 1) ⁻¹' A) ∩ strictAntichainEvent n (m + 1) :
      Set (CubeSample n (m + 1))) =ᵐ[cubeSampleLaw n (m + 1)]
      ((cubeNormalizedRanks n m ⁻¹' avoidanceRankSet n m) ∩
        (coordinateSortedValues n (m + 1) ⁻¹' A) : Set (CubeSample n (m + 1))) := by
    filter_upwards [cube_antichainEvent_ae_rank_avoidance n m] with x hx
    apply propext
    change (coordinateSortedValues n (m + 1) x ∈ A ∧ strictAntichainEvent n (m + 1) x) ↔
      ((cubeNormalizedRanks n m ⁻¹' avoidanceRankSet n m) x ∧ coordinateSortedValues n (m + 1) x ∈ A)
    rw [hx]
    exact and_comm
  rw [measure_congr heq,
    (cubeNormalizedRanks_independent_sorted_values n m).measure_inter_preimage_eq_mul
      (avoidanceRankSet n m) A (measurableSet_avoidanceRankSet n m) hA,
    ← measure_congr (cube_antichainEvent_ae_rank_avoidance n m)]
  change (antichainMass n (m + 1))⁻¹ * (antichainMass n (m + 1) * _) = _
  exact ENNReal.inv_mul_cancel_left (antichainMass_pos n (m + 1) (by omega)).ne'
    (antichainMass_ne_top n (m + 1))

/-- The actual rank tuple of a uniform cube antichain is uniform on the finite
avoidance class, with the usual normalized counting-measure definition. -/
theorem cubeAntichain_normalizedRanks_uniformOn (n m : ℕ) :
    (cubeAntichainLaw n (m + 1)).map (cubeNormalizedRanks n m) =
      ProbabilityTheory.uniformOn (avoidanceRankSet n m) := by
  have hmass : antichainMass n (m + 1) =
      (PMF.uniformOfFintype (Fin m → Equiv.Perm (Fin n))).toMeasure (avoidanceRankSet n m) := by
    change (cubeSampleLaw n (m + 1)) (strictAntichainEvent n (m + 1)) = _
    rw [measure_congr (cube_antichainEvent_ae_rank_avoidance n m),
      ← Measure.map_apply (cubeNormalizedRanks_measurable n m) (measurableSet_avoidanceRankSet n m),
      cubeNormalizedRanks_uniform_law]
  rw [cubeAntichain_normalizedRanks_law, hmass,
    finite_uniform_restrict_normalize_eq_uniformOn]

end Antichain
