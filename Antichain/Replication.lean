import Antichain.ReflectionGluing
import Antichain.ReplicationLabels
import Mathlib.Data.Fintype.Perm

/-! Actual measurable copying of independent configurations into alcoves. -/

noncomputable section

namespace Antichain

open Set MeasureTheory Module Metric
open scoped ENNReal Pointwise BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

theorem volume_preserving_uncurry {I J E : Type*} [Fintype I] [Fintype J]
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    MeasurePreserving (MeasurableEquiv.curry I J E).symm := by
  refine ⟨(MeasurableEquiv.curry I J E).symm.measurable, ?_⟩
  symm
  change Measure.pi (fun _ : I × J => (volume : Measure E)) = _
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have hp : (MeasurableEquiv.curry I J E).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i => univ.pi (fun j => s (i, j))) := by
    ext f
    simp [Set.mem_pi, MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hp, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_prod_type]

def configurationBlocksEquiv (m q N : ℕ) (e : Fin N ≃ Fin q × Fin m) :
    (Fin q → FloorHeightConfiguration m d) ≃ᵐ FloorHeightConfiguration N d :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Fin m → FloorSpace (Fin d))
    (Fin m → ℝ) (Fin q)).trans
    (((MeasurableEquiv.curry (Fin q) (Fin m) (FloorSpace (Fin d))).symm.prodCongr
      (MeasurableEquiv.curry (Fin q) (Fin m) ℝ).symm).trans
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin q × Fin m => FloorSpace (Fin d)) e).symm.prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : Fin q × Fin m => ℝ) e).symm))

omit [NeZero d] in
@[simp] theorem configurationBlocksEquiv_apply (m q N : ℕ)
    (e : Fin N ≃ Fin q × Fin m) (p : Fin q → FloorHeightConfiguration m d) :
    configurationBlocksEquiv m q N e p =
      (fun j => (p (e j).1).1 (e j).2, fun j => (p (e j).1).2 (e j).2) := rfl

omit [NeZero d] in
theorem configurationBlocksEquiv_volumePreserving (m q N : ℕ)
    (e : Fin N ≃ Fin q × Fin m) :
    MeasurePreserving (configurationBlocksEquiv (d := d) m q N e) := by
  letI : SigmaFinite (volume : Measure (Fin q → Fin m → FloorSpace (Fin d))) :=
    Measure.pi.sigmaFinite (fun _ => (volume : Measure (Fin m → FloorSpace (Fin d))))
  letI : SigmaFinite (volume : Measure (Fin q → Fin m → ℝ)) :=
    Measure.pi.sigmaFinite (fun _ => (volume : Measure (Fin m → ℝ)))
  exact ((volume_measurePreserving_piCongrLeft
      (fun _ : Fin q × Fin m => FloorSpace (Fin d)) e).symm.prod
    (volume_measurePreserving_piCongrLeft (fun _ : Fin q × Fin m => ℝ) e).symm).comp
    (((volume_preserving_uncurry (I := Fin q) (J := Fin m) (E := FloorSpace (Fin d))).prod
      (volume_preserving_uncurry (I := Fin q) (J := Fin m) (E := ℝ))).comp
      (volume_measurePreserving_arrowProdEquivProdArrow (Fin m → FloorSpace (Fin d))
        (Fin m → ℝ) (Fin q)))

def reflectedConfigurationEquiv (m : ℕ) (t : AlcoveTile d) :
    FloorHeightConfiguration m d ≃ᵐ FloorHeightConfiguration m d :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin m => (alcoveChart t).toMeasurableEquiv)).prodCongr
    (MeasurableEquiv.refl _)

@[simp] theorem reflectedConfigurationEquiv_apply (m : ℕ) (t : AlcoveTile d)
    (p : FloorHeightConfiguration m d) :
    reflectedConfigurationEquiv m t p = (fun j => alcoveChart t (p.1 j), p.2) := rfl

theorem alcoveChart_volumePreserving (t : AlcoveTile d) : MeasurePreserving (alcoveChart t) := by
  change MeasurePreserving (reflectionWordHomeomorph d (alcoveWord t))
  exact (measurePreserving_add_left volume (wordTranslation d (alcoveWord t))).comp
    (floorPermutation (wordPermutation d (alcoveWord t))).measurePreserving

theorem reflectedConfigurationEquiv_volumePreserving (m : ℕ) (t : AlcoveTile d) :
    MeasurePreserving (reflectedConfigurationEquiv m t) := by
  exact (volume_preserving_pi (fun _ : Fin m => alcoveChart_volumePreserving t)).prod
    (MeasurePreserving.id volume)

theorem volume_image_measurePreserving {X Y : Type*}
    [MeasureSpace X] [MeasureSpace Y] (e : X ≃ᵐ Y)
    (he : MeasurePreserving e) {A : Set X} (hA : MeasurableSet A) :
    volume (e '' A) = volume A := by
  have hh : e '' A = e.symm ⁻¹' A := e.toEquiv.image_eq_preimage A
  rw [hh]
  exact he.symm.measure_preimage hA.nullMeasurableSet

def replicatedLabelFamily (m q N : ℕ) (ε : ℝ) (tiles : Fin q → AlcoveTile d)
    (e : Fin N ≃ Fin q × Fin m) (B : Set (FloorHeightConfiguration m d)) :
    Set (FloorHeightConfiguration N d) :=
  ε • (configurationBlocksEquiv m q N e ''
    (univ.pi (fun i => reflectedConfigurationEquiv m (tiles i) '' B)))

theorem measurableSet_replicatedLabelFamily (m q N : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (tiles : Fin q → AlcoveTile d) (e : Fin N ≃ Fin q × Fin m)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B) :
    MeasurableSet (replicatedLabelFamily m q N ε tiles e B) := by
  exact ((configurationBlocksEquiv m q N e).measurableSet_image.mpr
    (MeasurableSet.univ_pi (fun i =>
      (reflectedConfigurationEquiv m (tiles i)).measurableSet_image.mpr hB))).const_smul_of_ne_zero hε

theorem volume_replicatedLabelFamily (m q N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (e : Fin N ≃ Fin q × Fin m)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B) :
    volume (replicatedLabelFamily m q N ε tiles e B) =
      ENNReal.ofReal ε ^ (d * N) * volume B ^ q := by
  letI : BorelSpace (FloorHeightConfiguration N d) := by infer_instance
  unfold replicatedLabelFamily
  rw [Measure.addHaar_smul_of_nonneg (volume : Measure (FloorHeightConfiguration N d)) hε.le,
    finrank_floorHeightConfiguration,
    ENNReal.ofReal_pow hε.le, volume_image_measurePreserving _
      (configurationBlocksEquiv_volumePreserving m q N e)]
  · rw [volume_pi_pi]
    simp_rw [volume_image_measurePreserving _ (reflectedConfigurationEquiv_volumePreserving _ _) hB]
    simp
  · exact MeasurableSet.univ_pi (fun i =>
      (reflectedConfigurationEquiv m (tiles i)).measurableSet_image.mpr hB)

theorem mem_replicatedLabelFamily_iff (m q N : ℕ) (ε : ℝ)
    (tiles : Fin q → AlcoveTile d) (e : Fin N ≃ Fin q × Fin m)
    (B : Set (FloorHeightConfiguration m d)) (p : FloorHeightConfiguration N d) :
    p ∈ replicatedLabelFamily m q N ε tiles e B ↔
      ∃ b : Fin q → FloorHeightConfiguration m d,
        (∀ i, b i ∈ B) ∧ replicatedConfiguration m q N ε tiles b e = p := by
  classical
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    have hx (i : Fin q) : ∃ b ∈ B, reflectedConfigurationEquiv m (tiles i) b = a i :=
      ha i (mem_univ i)
    choose b hb hbe using hx
    refine ⟨b, hb, ?_⟩
    apply Prod.ext
    · funext j
      change ε • alcoveChart (tiles (e j).1) ((b (e j).1).1 (e j).2) = _
      have hh := congrArg (fun p : FloorHeightConfiguration m d => p.1 (e j).2) (hbe (e j).1)
      exact congrArg (ε • ·) hh
    · funext j
      change ε * (b (e j).1).2 (e j).2 = _
      have hh := congrArg (fun p : FloorHeightConfiguration m d => p.2 (e j).2) (hbe (e j).1)
      exact congrArg (ε * ·) hh
  · rintro ⟨b, hb, rfl⟩
    refine ⟨configurationBlocksEquiv m q N e
      (fun i => reflectedConfigurationEquiv m (tiles i) (b i)), ?_, rfl⟩
    refine ⟨(fun i => reflectedConfigurationEquiv m (tiles i) (b i)), ?_, rfl⟩
    intro i _
    exact ⟨b i, hb i, rfl⟩

theorem scaled_alcoveChart_mem_interior (ε : ℝ) (hε : ε ≠ 0) (t : AlcoveTile d)
    {a : FloorSpace (Fin d)} (ha : a ∈ interior (referenceSimplex d)) :
    ε • alcoveChart t a ∈ interior (scaledAlcove d ε t) := by
  rw [scaledAlcove, interior_smul₀ hε]
  refine ⟨alcoveChart t a, ?_, rfl⟩
  change alcoveChart t a ∈ interior (t : Set (FloorSpace (Fin d)))
  rw [← alcoveChart_image_reference, ← (alcoveChart t).image_interior]
  exact ⟨a, ha, rfl⟩

theorem replicatedLabelFamily_floor_interior (m q N : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (tiles : Fin q → AlcoveTile d) (e : Fin N ≃ Fin q × Fin m)
    {B : Set (FloorHeightConfiguration m d)}
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    {p : FloorHeightConfiguration N d} (hp : p ∈ replicatedLabelFamily m q N ε tiles e B) :
    ∀ j, p.1 j ∈ interior (scaledAlcove d ε (tiles (e j).1)) := by
  obtain ⟨b, hb, rfl⟩ := (mem_replicatedLabelFamily_iff m q N ε tiles e B p).mp hp
  intro j
  exact scaled_alcoveChart_mem_interior ε hε _ (hf _ (hb _) _)

theorem replicatedLabelFamily_disjoint (h : HumphreysAlcoveInput d)
    (m q N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    (e e' : Fin N ≃ Fin q × Fin m)
    (he : ∃ j, (e j).1 ≠ (e' j).1)
    {B : Set (FloorHeightConfiguration m d)}
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d)) :
    Disjoint (replicatedLabelFamily m q N ε tiles e B)
      (replicatedLabelFamily m q N ε tiles e' B) := by
  apply Set.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨j, hj⟩ := he
  exact Set.disjoint_left.mp
    (scaledAlcove_disjoint_interiors d h hε (show tiles (e j).1 ≠ tiles (e' j).1 from
      fun ht => hj (htiles ht)))
    (replicatedLabelFamily_floor_interior m q N ε hε.ne' tiles e hf hp j)
    (replicatedLabelFamily_floor_interior m q N ε hε.ne' tiles e' hf hp' j)

theorem replicatedLabelFamily_admissible (hd : 2 ≤ d) (h : HumphreysAlcoveInput d)
    (m q N : ℕ) [NeZero q] (ε C : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    (e : Fin N ≃ Fin q × Fin m) {B : Set (FloorHeightConfiguration m d)}
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ referenceSimplex d)
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧
      (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b)) :
    ∀ p ∈ replicatedLabelFamily m q N ε tiles e B,
      p ∈ flooredAntichainEvent N d ∧ (∀ j, |p.2 j| ≤ C * ε) ∧
      (∀ j, p.1 j ∈ scaledAlcove d ε (tiles (e j).1)) := by
  intro p hp
  obtain ⟨b, hb, rfl⟩ := (mem_replicatedLabelFamily_iff m q N ε tiles e B p).mp hp
  refine ⟨(replicatedConfiguration_admissible hd h m q N ε hε tiles htiles b boundary
    (fun i j => hf _ (hb i) j) (fun i => hext _ (hb i)) e).1,
    replicatedConfiguration_height_bound m q N ε C hε.le tiles b (fun i j => hh _ (hb i) j) e, ?_⟩
  intro j
  refine ⟨alcoveChart (tiles (e j).1) ((b (e j).1).1 (e j).2), ?_, rfl⟩
  change alcoveChart (tiles (e j).1) ((b (e j).1).1 (e j).2) ∈
    (tiles (e j).1 : Set (FloorSpace (Fin d)))
  rw [← alcoveChart_image_reference]
  exact ⟨(b (e j).1).1 (e j).2, hf _ (hb _) _, rfl⟩

/-- The exact source family, with unordered label sets and increasing order
inside every tile. -/
def replicationFamily (m q N : ℕ) (ε : ℝ) (tiles : Fin q → AlcoveTile d)
    (B : Set (FloorHeightConfiguration m d)) : Set (FloorHeightConfiguration N d) :=
  ⋃ f : BalancedLabeling m q N,
    replicatedLabelFamily m q N ε tiles (balancedLabelEquiv m q N f) B

theorem measurableSet_replicationFamily (m q N : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (tiles : Fin q → AlcoveTile d) {B : Set (FloorHeightConfiguration m d)}
    (hB : MeasurableSet B) : MeasurableSet (replicationFamily m q N ε tiles B) :=
  MeasurableSet.iUnion (fun _ => measurableSet_replicatedLabelFamily m q N ε hε tiles _ hB)

theorem replicationFamily_pairwise_disjoint (h : HumphreysAlcoveInput d)
    (m q N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    {B : Set (FloorHeightConfiguration m d)}
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d)) :
    Pairwise (fun f g : BalancedLabeling m q N =>
      Disjoint (replicatedLabelFamily m q N ε tiles (balancedLabelEquiv m q N f) B)
        (replicatedLabelFamily m q N ε tiles (balancedLabelEquiv m q N g) B)) := by
  classical
  intro f g hfg
  apply replicatedLabelFamily_disjoint h m q N ε hε tiles htiles _ _ ?_ hf
  by_contra hn
  apply hfg
  apply Subtype.ext
  funext j
  by_contra hj
  exact hn ⟨j, hj⟩

theorem volume_replicationFamily (h : HumphreysAlcoveInput d)
    (m q N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d)) :
    volume (replicationFamily m q N ε tiles B) =
      (Fintype.card (BalancedLabeling m q N) : ℝ≥0∞) *
        (ENNReal.ofReal ε ^ (d * N) * volume B ^ q) := by
  unfold replicationFamily
  rw [measure_iUnion (replicationFamily_pairwise_disjoint h m q N ε hε tiles htiles hf)
    (fun _ => measurableSet_replicatedLabelFamily m q N ε hε.ne' tiles _ hB)]
  simp_rw [volume_replicatedLabelFamily m q N ε hε tiles _ hB]
  simp [tsum_fintype]

theorem replicationFamily_admissible (hd : 2 ≤ d) (h : HumphreysAlcoveInput d)
    (m q N : ℕ) [NeZero q] (ε C : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    {B : Set (FloorHeightConfiguration m d)} (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ referenceSimplex d)
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧
      (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b)) :
    ∀ p ∈ replicationFamily m q N ε tiles B,
      p ∈ flooredAntichainEvent N d ∧ (∀ j, |p.2 j| ≤ C * ε) ∧
      (∀ j, p.1 j ∈ ⋃ i, scaledAlcove d ε (tiles i)) := by
  intro p hp
  obtain ⟨f, hfam⟩ := Set.mem_iUnion.mp hp
  have hp := replicatedLabelFamily_admissible hd h m q N ε C hε tiles htiles
    (balancedLabelEquiv m q N f) boundary hf hh hext p hfam
  refine ⟨hp.1, hp.2.1, fun j => Set.mem_iUnion.mpr ?_⟩
  exact ⟨(balancedLabelEquiv m q N f j).1, hp.2.2 j⟩

/-- The printed ordinary-volume formula, including the exact label factor
and the full floor-plus-height Jacobian. -/
theorem replicationFamily_volume_formula (h : HumphreysAlcoveInput d)
    (m q N : ℕ) (hN : N = q * m) (ε : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d)) :
    (volume (replicationFamily m q N ε tiles B)).toReal =
      ((Nat.factorial N : ℝ) / (Nat.factorial m : ℝ) ^ q) *
        (ε ^ (d * m) * (volume B).toReal) ^ q := by
  rw [volume_replicationFamily h m q N ε hε tiles htiles hB hf]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hε.le]
  have hcard : (Fintype.card (BalancedLabeling m q N) : ℝ) =
      (Nat.factorial N : ℝ) / (Nat.factorial m : ℝ) ^ q := by
    apply (eq_div_iff (pow_ne_zero q (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)))).mpr
    exact_mod_cast card_balancedLabeling_mul m q N hN
  rw [hcard, mul_pow, ← pow_mul]
  congr 2
  rw [hN]
  congr 1
  ring

theorem replicationFamily_volume_lt_top (h : HumphreysAlcoveInput d)
    (m q N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    (hfinite : volume B < ⊤) : volume (replicationFamily m q N ε tiles B) < ⊤ := by
  rw [volume_replicationFamily h m q N ε hε tiles htiles hB hf]
  exact ENNReal.mul_lt_top (by simp)
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      (ENNReal.pow_lt_top hfinite))

/-- Full source replication conclusion for the literal family defined above.
Every hypothesis describes the one-tile family produced in Lemma 5.2;
measurability, admissibility, absence of multiplicity and the volume formula
are proved here. -/
theorem replicationFamily_full_spec (hd : 2 ≤ d) (h : HumphreysAlcoveInput d)
    (m q N : ℕ) (hN : N = q * m) [NeZero q] (ε C : ℝ) (hε : 0 < ε)
    (tiles : Fin q → AlcoveTile d) (htiles : Function.Injective tiles)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧
      (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b)) :
    MeasurableSet (replicationFamily m q N ε tiles B) ∧
      volume (replicationFamily m q N ε tiles B) < ⊤ ∧
      (∀ p ∈ replicationFamily m q N ε tiles B,
        p ∈ flooredAntichainEvent N d ∧ (∀ j, |p.2 j| ≤ C * ε) ∧
        (∀ j, p.1 j ∈ ⋃ i, scaledAlcove d ε (tiles i))) ∧
      (volume (replicationFamily m q N ε tiles B)).toReal =
        ((Nat.factorial N : ℝ) / (Nat.factorial m : ℝ) ^ q) *
          (ε ^ (d * m) * (volume B).toReal) ^ q := by
  have hfloor : ∀ p ∈ B, ∀ j, p.1 j ∈ referenceSimplex d :=
    fun p hp j => interior_subset (hf p hp j)
  exact ⟨measurableSet_replicationFamily m q N ε hε.ne' tiles hB,
    replicationFamily_volume_lt_top h m q N ε hε tiles htiles hB hf
      (matching_family_volume_lt_top hd m B C hfloor hh),
    replicationFamily_admissible hd h m q N ε C hε tiles htiles boundary hfloor hh hext,
    replicationFamily_volume_formula h m q N hN ε hε tiles htiles hB hf⟩

/-- Lemmas 5.2 and 5.3 composed at the actual matched families. The constants
precede the sample count, and the only external input is the cited geometric
alcove theorem. Here the paper's r is written r+1 so positivity is explicit. -/
theorem matching_replication_source (hd : 2 ≤ d) (h : HumphreysAlcoveInput d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eta lam : ℝ, eta ∈ Set.Ioo 0 (1 / 2 : ℝ) →
      lam ∈ Set.Ioo 0 (1 / 2 : ℝ) → ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ,
      ∃ B : Set (FloorHeightConfiguration (r + 1) d), ∃ boundary : SimplexBoundary d →ᵇ ℝ,
        MeasurableSet B ∧
        (∀ p ∈ B, (∀ j, p.1 j ∈ referenceSimplex d) ∧ p ∈ flooredAntichainEvent (r + 1) d) ∧
        (∀ p ∈ B, ∀ j, |p.2 j| ≤ C ∧ eta / C ≤ infDist (p.1 j) (frontier (referenceSimplex d))) ∧
        (∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
          (∀ j, E (p.1 j) = p.2 j) ∧ (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
          (∀ a b, E a - E b ≤ nativeFloorCost a b)) ∧
        (2 / (M : ℝ)) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
          pinnedVolume (referenceSimplex d) r ≤ (volume B).toReal ∧
        ∀ q : ℕ, 1 ≤ q → ∀ ε : ℝ, 0 < ε → ∀ tiles : Fin q → AlcoveTile d,
          Function.Injective tiles →
          MeasurableSet (replicationFamily (r + 1) q (q * (r + 1)) ε tiles B) ∧
          volume (replicationFamily (r + 1) q (q * (r + 1)) ε tiles B) < ⊤ ∧
          (∀ p ∈ replicationFamily (r + 1) q (q * (r + 1)) ε tiles B,
            p ∈ flooredAntichainEvent (q * (r + 1)) d ∧ (∀ j, |p.2 j| ≤ C * ε) ∧
            (∀ j, p.1 j ∈ ⋃ i, scaledAlcove d ε (tiles i))) ∧
          (volume (replicationFamily (r + 1) q (q * (r + 1)) ε tiles B)).toReal =
            ((Nat.factorial (q * (r + 1)) : ℝ) / (Nat.factorial (r + 1) : ℝ) ^ q) *
              (ε ^ (d * (r + 1)) * (volume B).toReal) ^ q := by
  obtain ⟨C, hC, hCM⟩ := boundary_matching_source hd
  refine ⟨C, hC, fun eta lam heta hlam => ?_⟩
  obtain ⟨M, hM, hMB⟩ := hCM eta lam heta hlam
  refine ⟨M, hM, fun r => ?_⟩
  obtain ⟨B, boundary, hB, hBevent, hBbound, hBext, hBvolume⟩ := hMB r
  refine ⟨B, boundary, hB, hBevent, hBbound, hBext, hBvolume, ?_⟩
  intro q hq ε hε tiles htiles
  letI : NeZero q := ⟨by omega⟩
  have hfloor : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d) := by
    intro p hp j
    by_contra hn
    have hfront : p.1 j ∈ frontier (referenceSimplex d) :=
      ⟨subset_closure ((hBevent p hp).1 j), hn⟩
    have hm := (hBbound p hp j).2
    rw [Metric.infDist_zero_of_mem hfront] at hm
    have hpos : 0 < eta / C := div_pos heta.1 (lt_of_lt_of_le zero_lt_one hC)
    linarith
  exact replicationFamily_full_spec hd h (r + 1) q (q * (r + 1)) rfl ε C hε tiles htiles hB
    boundary hfloor (fun p hp j => (hBbound p hp j).1) hBext

end Antichain
