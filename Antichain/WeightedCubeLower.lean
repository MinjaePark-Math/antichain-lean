import Antichain.Replication
import Antichain.CubeTileCount
import Antichain.FloorIntegralApproximation
import Antichain.PinnedVolumeBounds

/-! Actual finite-scale weighted lower constructions in separated floor regions. -/

noncomputable section

namespace Antichain

open Set MeasureTheory Metric Finset
open scoped ENNReal Pointwise BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

def heterogeneousReplicatedConfiguration (m q N : ℕ) (ε : Fin q → ℝ)
    (tiles : Fin q → AlcoveTile d) (p : Fin q → FloorHeightConfiguration m d)
    (e : Fin N → Fin q × Fin m) : FloorHeightConfiguration N d :=
  (fun j => ε (e j).1 • alcoveChart (tiles (e j).1) ((p (e j).1).1 (e j).2),
    fun j => ε (e j).1 * (p (e j).1).2 (e j).2)

def heterogeneousLabelFamily (m q N : ℕ) (ε : Fin q → ℝ)
    (tiles : Fin q → AlcoveTile d) (e : Fin N ≃ Fin q × Fin m)
    (B : Set (FloorHeightConfiguration m d)) : Set (FloorHeightConfiguration N d) :=
  configurationBlocksEquiv m q N e ''
    (univ.pi (fun i => ε i • (reflectedConfigurationEquiv m (tiles i) '' B)))

theorem measurableSet_heterogeneousLabelFamily (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, ε i ≠ 0) (tiles : Fin q → AlcoveTile d)
    (e : Fin N ≃ Fin q × Fin m) {B : Set (FloorHeightConfiguration m d)}
    (hB : MeasurableSet B) : MeasurableSet (heterogeneousLabelFamily m q N ε tiles e B) := by
  exact (configurationBlocksEquiv m q N e).measurableSet_image.mpr
    (MeasurableSet.univ_pi (fun i =>
      ((reflectedConfigurationEquiv m (tiles i)).measurableSet_image.mpr hB).const_smul_of_ne_zero (hε i)))

theorem volume_heterogeneousLabelFamily (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, 0 < ε i) (tiles : Fin q → AlcoveTile d)
    (e : Fin N ≃ Fin q × Fin m) {B : Set (FloorHeightConfiguration m d)}
    (hB : MeasurableSet B) :
    volume (heterogeneousLabelFamily m q N ε tiles e B) =
      ∏ i, (ENNReal.ofReal (ε i) ^ (d * m) * volume B) := by
  letI : BorelSpace (FloorHeightConfiguration m d) := by infer_instance
  unfold heterogeneousLabelFamily
  rw [volume_image_measurePreserving _ (configurationBlocksEquiv_volumePreserving m q N e)
    (MeasurableSet.univ_pi (fun i =>
      ((reflectedConfigurationEquiv m (tiles i)).measurableSet_image.mpr hB).const_smul_of_ne_zero (hε i).ne')),
    volume_pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.addHaar_smul_of_nonneg (volume : Measure (FloorHeightConfiguration m d)) (hε i).le,
    finrank_floorHeightConfiguration, ENNReal.ofReal_pow (hε i).le,
    volume_image_measurePreserving _ (reflectedConfigurationEquiv_volumePreserving m (tiles i)) hB]

theorem mem_heterogeneousLabelFamily_iff (m q N : ℕ) (ε : Fin q → ℝ)
    (tiles : Fin q → AlcoveTile d) (e : Fin N ≃ Fin q × Fin m)
    (B : Set (FloorHeightConfiguration m d)) (p : FloorHeightConfiguration N d) :
    p ∈ heterogeneousLabelFamily m q N ε tiles e B ↔
      ∃ b : Fin q → FloorHeightConfiguration m d, (∀ i, b i ∈ B) ∧
        heterogeneousReplicatedConfiguration m q N ε tiles b e = p := by
  classical
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hx (i : Fin q) : ∃ b ∈ B, ε i • reflectedConfigurationEquiv m (tiles i) b = a i := by
      obtain ⟨c, ⟨b, hb, rfl⟩, heq⟩ := ha i (mem_univ i)
      exact ⟨b, hb, heq⟩
    choose b hb hbe using hx
    refine ⟨b, hb, ?_⟩
    apply Prod.ext
    · funext j
      exact congrArg (fun p : FloorHeightConfiguration m d => p.1 (e j).2) (hbe (e j).1)
    · funext j
      exact congrArg (fun p : FloorHeightConfiguration m d => p.2 (e j).2) (hbe (e j).1)
  · rintro ⟨b, hb, rfl⟩
    refine ⟨(fun i => ε i • reflectedConfigurationEquiv m (tiles i) (b i)), ?_, rfl⟩
    intro i _
    exact ⟨reflectedConfigurationEquiv m (tiles i) (b i), ⟨b i, hb i, rfl⟩, rfl⟩

def heterogeneousReplicationFamily (m q N : ℕ) (ε : Fin q → ℝ)
    (tiles : Fin q → AlcoveTile d) (B : Set (FloorHeightConfiguration m d)) :
    Set (FloorHeightConfiguration N d) :=
  ⋃ f : BalancedLabeling m q N,
    heterogeneousLabelFamily m q N ε tiles (balancedLabelEquiv m q N f) B

theorem heterogeneousLabelFamily_floor_interior (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, ε i ≠ 0) (tiles : Fin q → AlcoveTile d)
    (e : Fin N ≃ Fin q × Fin m) {B : Set (FloorHeightConfiguration m d)}
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    {p : FloorHeightConfiguration N d} (hp : p ∈ heterogeneousLabelFamily m q N ε tiles e B) :
    ∀ j, p.1 j ∈ interior (scaledAlcove d (ε (e j).1) (tiles (e j).1)) := by
  obtain ⟨b, hb, rfl⟩ := (mem_heterogeneousLabelFamily_iff m q N ε tiles e B p).mp hp
  intro j
  exact scaled_alcoveChart_mem_interior _ (hε _) _ (hf _ (hb _) _)

theorem heterogeneousReplicationFamily_pairwise_disjoint (m q N : ℕ)
    (ε : Fin q → ℝ) (hε : ∀ i, ε i ≠ 0) (tiles : Fin q → AlcoveTile d)
    (htiles : Pairwise (fun i j => Disjoint (interior (scaledAlcove d (ε i) (tiles i)))
      (interior (scaledAlcove d (ε j) (tiles j)))))
    {B : Set (FloorHeightConfiguration m d)}
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d)) :
    Pairwise (fun f g : BalancedLabeling m q N =>
      Disjoint (heterogeneousLabelFamily m q N ε tiles (balancedLabelEquiv m q N f) B)
        (heterogeneousLabelFamily m q N ε tiles (balancedLabelEquiv m q N g) B)) := by
  classical
  intro f g hfg
  apply Set.disjoint_left.mpr
  intro p hp hp'
  have hne : ∃ j, f.val j ≠ g.val j := by
    by_contra hn
    apply hfg
    apply Subtype.ext
    funext j
    by_contra hj
    exact hn ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hne
  exact Set.disjoint_left.mp (htiles hj)
    (heterogeneousLabelFamily_floor_interior m q N ε hε tiles _ hf hp j)
    (heterogeneousLabelFamily_floor_interior m q N ε hε tiles _ hf hp' j)

theorem heterogeneousReplicationFamily_volume (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, 0 < ε i) (tiles : Fin q → AlcoveTile d)
    (htiles : Pairwise (fun i j => Disjoint (interior (scaledAlcove d (ε i) (tiles i)))
      (interior (scaledAlcove d (ε j) (tiles j)))))
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d)) :
    MeasurableSet (heterogeneousReplicationFamily m q N ε tiles B) ∧
    volume (heterogeneousReplicationFamily m q N ε tiles B) =
      (Fintype.card (BalancedLabeling m q N) : ℝ≥0∞) *
        ∏ i, (ENNReal.ofReal (ε i) ^ (d * m) * volume B) := by
  refine ⟨MeasurableSet.iUnion (fun _ =>
    measurableSet_heterogeneousLabelFamily m q N ε (fun i => (hε i).ne') tiles _ hB), ?_⟩
  unfold heterogeneousReplicationFamily
  rw [measure_iUnion (heterogeneousReplicationFamily_pairwise_disjoint m q N ε
      (fun i => (hε i).ne') tiles htiles hf)
    (fun _ => measurableSet_heterogeneousLabelFamily m q N ε (fun i => (hε i).ne') tiles _ hB)]
  simp_rw [volume_heterogeneousLabelFamily m q N ε hε tiles _ hB]
  simp [tsum_fintype]

theorem two_transported_extensions_constraint (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (t u : AlcoveTile d) (htu : t ≠ u) (ε : ℝ) (hε : 0 < ε)
    (E F : FloorSpace (Fin d) → ℝ) (boundary : SimplexBoundary d → ℝ)
    (hE : ∀ a b, E a - E b ≤ nativeFloorCost a b)
    (hF : ∀ a b, F a - F b ≤ nativeFloorCost a b)
    (hEb : ∀ a : SimplexBoundary d, E a.val = boundary a)
    (hFb : ∀ a : SimplexBoundary d, F a.val = boundary a)
    {a b : FloorSpace (Fin d)} (ha : a ∈ referenceSimplex d) (hb : b ∈ referenceSimplex d) :
    ε * E a - ε * F b ≤ nativeFloorCost (ε • alcoveChart t a) (ε • alcoveChart u b) := by
  classical
  let G : AlcoveTile d → FloorSpace (Fin d) → ℝ := fun s => if s = t then E else F
  have hGb : ∀ s a (ha : a ∈ frontier (referenceSimplex d)), G s a = boundary ⟨a, ha⟩ := by
    intro s a ha
    dsimp [G]
    split_ifs
    · exact hEb ⟨a, ha⟩
    · exact hFb ⟨a, ha⟩
  have hG : ∀ s, ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
      G s a - G s b ≤ nativeFloorCost a b := by
    intro s a _ b _
    dsimp [G]
    split_ifs
    · exact hE a b
    · exact hF a b
  have hg := scaledGluedAlcoveHeight_directional hd H ε hε G boundary hGb hG
    (ε • alcoveChart t a) (ε • alcoveChart u b)
  rw [scaledGluedAlcoveHeight_eq_transport H ε hε.ne' G boundary hGb t ha,
    scaledGluedAlcoveHeight_eq_transport H ε hε.ne' G boundary hGb u hb] at hg
  simpa only [G, if_pos rfl, if_neg (Ne.symm htu)] using hg

theorem heterogeneousReplicatedConfiguration_admissible (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, 0 < ε i) (C : ℝ) (tiles : Fin q → AlcoveTile d)
    (B : Set (FloorHeightConfiguration m d)) (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ referenceSimplex d)
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧ (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b))
    (hpair : ∀ i l, i ≠ l → (ε i = ε l ∧ tiles i ≠ tiles l) ∨
      ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
        C * (ε i + ε l) ≤ nativeFloorCost
          (ε i • alcoveChart (tiles i) a) (ε l • alcoveChart (tiles l) b))
    (p : Fin q → FloorHeightConfiguration m d) (hp : ∀ i, p i ∈ B)
    (e : Fin N → Fin q × Fin m) :
    heterogeneousReplicatedConfiguration m q N ε tiles p e ∈ flooredAntichainEvent N d := by
  choose E hE using (fun i => hext (p i) (hp i))
  apply (flooredAntichainEvent_iff_native_constraints N _).mpr
  intro j k
  change ε (e j).1 * (p (e j).1).2 (e j).2 - ε (e k).1 * (p (e k).1).2 (e k).2 ≤ _
  by_cases hik : (e j).1 = (e k).1
  · simp only [← hik]
    have hc := mul_le_mul_of_nonneg_left
      ((hE (e j).1).2.2 ((p (e j).1).1 (e j).2) ((p (e j).1).1 (e k).2)) (hε (e j).1).le
    rw [(hE (e j).1).1, (hE (e j).1).1, mul_sub] at hc
    exact hc.trans_eq (by
      simp only [heterogeneousReplicatedConfiguration, ← hik]
      rw [nativeFloorCost_smul _ (hε (e j).1).le, alcoveChart_apply, alcoveChart_apply,
        nativeFloorCost_reflectionWord])
  · rcases hpair (e j).1 (e k).1 hik with ⟨hscale, htile⟩ | hcross
    · have hc := two_transported_extensions_constraint hd H (tiles (e j).1) (tiles (e k).1)
        htile (ε (e j).1) (hε _) (E (e j).1) (E (e k).1) boundary
        (hE _).2.2 (hE _).2.2 (hE _).2.1 (hE _).2.1
        (hf (p (e j).1) (hp (e j).1) (e j).2) (hf (p (e k).1) (hp (e k).1) (e k).2)
      rw [(hE (e j).1).1, (hE (e k).1).1] at hc
      simpa only [heterogeneousReplicatedConfiguration, hscale] using hc
    · have hj : ε (e j).1 * (p (e j).1).2 (e j).2 ≤ C * ε (e j).1 := by
        calc
          _ ≤ |ε (e j).1 * (p (e j).1).2 (e j).2| := le_abs_self _
          _ = ε (e j).1 * |(p (e j).1).2 (e j).2| := by
            rw [abs_mul, abs_of_pos (hε _)]
          _ ≤ ε (e j).1 * C := mul_le_mul_of_nonneg_left (hh _ (hp _) _) (hε _).le
          _ = _ := mul_comm _ _
      have hk : -(ε (e k).1 * (p (e k).1).2 (e k).2) ≤ C * ε (e k).1 := by
        calc
          _ ≤ |ε (e k).1 * (p (e k).1).2 (e k).2| := neg_le_abs _
          _ = ε (e k).1 * |(p (e k).1).2 (e k).2| := by
            rw [abs_mul, abs_of_pos (hε _)]
          _ ≤ ε (e k).1 * C := mul_le_mul_of_nonneg_left (hh _ (hp _) _) (hε _).le
          _ = _ := mul_comm _ _
      exact (show ε (e j).1 * (p (e j).1).2 (e j).2 -
          ε (e k).1 * (p (e k).1).2 (e k).2 ≤ C * (ε (e j).1 + ε (e k).1) by nlinarith).trans
        (hcross _ (hf _ (hp _) _) _ (hf _ (hp _) _))

theorem heterogeneousReplicationFamily_admissible (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, 0 < ε i) (C R : ℝ) (hC : 0 ≤ C) (hR : ∀ i, ε i ≤ R)
    (tiles : Fin q → AlcoveTile d) (B : Set (FloorHeightConfiguration m d))
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ referenceSimplex d)
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧ (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b))
    (hpair : ∀ i l, i ≠ l → (ε i = ε l ∧ tiles i ≠ tiles l) ∨
      ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
        C * (ε i + ε l) ≤ nativeFloorCost
          (ε i • alcoveChart (tiles i) a) (ε l • alcoveChart (tiles l) b)) :
    ∀ p ∈ heterogeneousReplicationFamily m q N ε tiles B,
      p ∈ flooredAntichainEvent N d ∧ ∀ j, |p.2 j| ≤ C * R := by
  intro p hp
  obtain ⟨f, hfam⟩ := Set.mem_iUnion.mp hp
  obtain ⟨b, hb, rfl⟩ := (mem_heterogeneousLabelFamily_iff m q N ε tiles _ B p).mp hfam
  refine ⟨heterogeneousReplicatedConfiguration_admissible hd H m q N ε hε C tiles B boundary
    hf hh hext hpair b hb _, ?_⟩
  intro j
  change |ε _ * (b _).2 _| ≤ _
  rw [abs_mul, abs_of_pos (hε _)]
  exact (mul_le_mul_of_nonneg_left (hh _ (hb _) _) (hε _).le).trans
    (by simpa only [mul_comm C] using mul_le_mul_of_nonneg_right (hR _) hC)

theorem product_tile_weights (m q N : ℕ) (e : Fin N ≃ Fin q × Fin m) (w : Fin q → ℝ) :
    (∏ j, w (e j).1) = ∏ i, w i ^ m := by
  rw [e.prod_comp (fun p : Fin q × Fin m => w p.1)]
  rw [Fintype.prod_prod_type]
  simp

omit [NeZero d] in
/-- A pointwise lower bound for the actual Gaussian kernel, including its
height normalization and actual floor density. -/
theorem flooredPartitionKernel_lower_of_height_weight (m q N : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (p : FloorHeightConfiguration N d) (T : ℝ) (hT : 0 ≤ T)
    (hh : ∀ j, |p.2 j| ≤ T) (e : Fin N ≃ Fin q × Fin m)
    (w : Fin q → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ j, w (e j).1 ≤ standardFloorDensity (p.1 j) * Real.exp (sigma (p.1 j))) :
    (2 * Real.pi) ^ (-(N : ℝ) / 2) *
      Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * T ^ 2)) *
        (∏ i, w i ^ m) ≤ flooredPartitionKernel N sigma c p := by
  have hsq : ∑ j, p.2 j ^ 2 ≤ (N : ℝ) * T ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin N, T ^ 2 := Finset.sum_le_sum (fun j _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (p.2 j)) hT).mpr (hh j))
      _ = _ := by simp
  have hexp : Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * T ^ 2)) ≤
      Real.exp (-((1 / 2 : ℝ) - c) * ∑ j, p.2 j ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprod : (∏ i, w i ^ m) ≤
      ∏ j, (standardFloorDensity (p.1 j) * Real.exp (sigma (p.1 j))) := by
    rw [← product_tile_weights m q N e w]
    exact Finset.prod_le_prod (fun j _ => hw _) (fun j _ => hf j)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (by positivity) _)) hprod
    (Finset.prod_nonneg (fun i _ => pow_nonneg (hw i) _))
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _))

/-- A genuine family lower bound for the actual partition function, proved
directly from the exact Gaussian integral and positivity. -/
theorem weightedPartition_ge_kernel_lower_times_volume (N : ℕ)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    {A : Set (FloorHeightConfiguration N d)} (hA : MeasurableSet A)
    (hsub : A ⊆ flooredAntichainEvent N d) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ p ∈ A, L ≤ flooredPartitionKernel N sigma c p) :
    L * (volume A).toReal ≤ weightedPartition N sigma c := by
  have hmass : ENNReal.ofReal L * volume A ≤ weightedPartitionMass N sigma c := by
    rw [weightedPartitionMass_eq_floorHeightIntegral]
    change ENNReal.ofReal L * volume A ≤
      ∫⁻ p in flooredAntichainEvent N d, ENNReal.ofReal (flooredPartitionKernel N sigma c p) ∂volume
    calc
      _ = ∫⁻ _ in A, ENNReal.ofReal L ∂volume := by simp
      _ ≤ ∫⁻ p in A, ENNReal.ofReal (flooredPartitionKernel N sigma c p) ∂volume := by
        apply setLIntegral_mono' hA
        exact fun p hp => ENNReal.ofReal_le_ofReal (hbound p hp)
      _ ≤ _ := lintegral_mono_set hsub
  have hreal := ENNReal.toReal_mono (weightedPartitionMass_lt_top N sigma c hc).ne hmass
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL, weightedPartition] using hreal

theorem heterogeneousReplicationFamily_volume_real (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, 0 < ε i) (tiles : Fin q → AlcoveTile d)
    (htiles : Pairwise (fun i j => Disjoint (interior (scaledAlcove d (ε i) (tiles i)))
      (interior (scaledAlcove d (ε j) (tiles j)))))
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d)) :
    (volume (heterogeneousReplicationFamily m q N ε tiles B)).toReal =
      (Fintype.card (BalancedLabeling m q N) : ℝ) *
        ∏ i, ((ε i) ^ (d * m) * (volume B).toReal) := by
  rw [(heterogeneousReplicationFamily_volume m q N ε hε tiles htiles hB hf).2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod, ENNReal.toReal_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [ENNReal.toReal_ofReal (hε i).le]

theorem heterogeneousReplicationFamily_kernel_lower (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (m q N : ℕ) (ε : Fin q → ℝ)
    (hε : ∀ i, 0 < ε i) (C R : ℝ) (hC : 0 ≤ C) (hR0 : 0 ≤ R) (hR : ∀ i, ε i ≤ R)
    (tiles : Fin q → AlcoveTile d)
    (htiles : Pairwise (fun i j => Disjoint (interior (scaledAlcove d (ε i) (tiles i)))
      (interior (scaledAlcove d (ε j) (tiles j)))))
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧ (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b))
    (hpair : ∀ i l, i ≠ l → (ε i = ε l ∧ tiles i ≠ tiles l) ∨
      ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
        C * (ε i + ε l) ≤ nativeFloorCost
          (ε i • alcoveChart (tiles i) a) (ε l • alcoveChart (tiles l) b))
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (w : Fin q → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hweight : ∀ i x, x ∈ scaledAlcove d (ε i) (tiles i) →
      w i ≤ standardFloorDensity x * Real.exp (sigma x)) :
    (2 * Real.pi) ^ (-(N : ℝ) / 2) *
      Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * R) ^ 2)) *
        (∏ i, w i ^ m) * (volume (heterogeneousReplicationFamily m q N ε tiles B)).toReal ≤
      weightedPartition N sigma c := by
  have hfloor : ∀ p ∈ B, ∀ j, p.1 j ∈ referenceSimplex d :=
    fun p hp j => interior_subset (hf p hp j)
  have hadm := heterogeneousReplicationFamily_admissible hd H m q N ε hε C R hC hR
    tiles B boundary hfloor hh hext hpair
  apply weightedPartition_ge_kernel_lower_times_volume N sigma c hc
    (heterogeneousReplicationFamily_volume m q N ε hε tiles htiles hB hf).1
    (fun p hp => (hadm p hp).1) _ (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _))
      (Finset.prod_nonneg (fun i _ => pow_nonneg (hw i) _)))
  intro p hp
  obtain ⟨f, hfam⟩ := Set.mem_iUnion.mp hp
  apply flooredPartitionKernel_lower_of_height_weight m q N sigma c hc p (C * R)
    (mul_nonneg hC hR0) (hadm p hp).2 (balancedLabelEquiv m q N f) w hw
  intro j
  apply hweight (balancedLabelEquiv m q N f j).1
  exact interior_subset (heterogeneousLabelFamily_floor_interior m q N ε
    (fun i => (hε i).ne') tiles _ hf hfam j)

omit [NeZero d] in
theorem tile_scale_weight_cancellation (m q N : ℕ) (hN : N = q * m)
    (ε : Fin q → ℝ) (w : Fin q → ℝ) (ε₀ v : ℝ)
    (hcancel : ∀ i, w i * ε i ^ d = ε₀ ^ d) :
    (∏ i, w i ^ m) * (∏ i, (ε i ^ (d * m) * v)) = ε₀ ^ (d * N) * v ^ q := by
  calc
    _ = ∏ i, w i ^ m * (ε i ^ (d * m) * v) := (Finset.prod_mul_distrib).symm
    _ = ∏ _ : Fin q, (ε₀ ^ d) ^ m * v := by
      apply Finset.prod_congr rfl
      intro i _
      rw [pow_mul (ε i) d m, ← mul_assoc, ← mul_pow, hcancel]
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul]
      rw [hN]
      congr 2
      ring

/-- The exact finite-scale source lower bound, with actual antichain Z,
actual independent copied families, the full label factor, the Gaussian
height penalty and cancellation w_i ε_i^d = ε^d. -/
theorem heterogeneous_weighted_partition_lower (hd : 2 ≤ d)
    (H : HumphreysAlcoveInput d) (m q N : ℕ) (hN : N = q * m)
    (ε : Fin q → ℝ) (hε : ∀ i, 0 < ε i) (ε₀ C R : ℝ)
    (hC : 0 ≤ C) (hR0 : 0 ≤ R) (hR : ∀ i, ε i ≤ R)
    (tiles : Fin q → AlcoveTile d)
    (htiles : Pairwise (fun i j => Disjoint (interior (scaledAlcove d (ε i) (tiles i)))
      (interior (scaledAlcove d (ε j) (tiles j)))))
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧ (∀ a : SimplexBoundary d, E a.val = boundary a) ∧
      (∀ a b, E a - E b ≤ nativeFloorCost a b))
    (hpair : ∀ i l, i ≠ l → (ε i = ε l ∧ tiles i ≠ tiles l) ∨
      ∀ a ∈ referenceSimplex d, ∀ b ∈ referenceSimplex d,
        C * (ε i + ε l) ≤ nativeFloorCost
          (ε i • alcoveChart (tiles i) a) (ε l • alcoveChart (tiles l) b))
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (w : Fin q → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hweight : ∀ i x, x ∈ scaledAlcove d (ε i) (tiles i) →
      w i ≤ standardFloorDensity x * Real.exp (sigma x))
    (hcancel : ∀ i, w i * ε i ^ d = ε₀ ^ d) :
    (Nat.factorial N : ℝ) * Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * R) ^ 2)) *
      (2 * Real.pi) ^ (-(N : ℝ) / 2) *
        ((volume B).toReal / (Nat.factorial m : ℝ)) ^ q * ε₀ ^ (d * N) ≤
      weightedPartition N sigma c := by
  have hb := heterogeneousReplicationFamily_kernel_lower hd H m q N ε hε C R hC hR0 hR
    tiles htiles hB boundary hf hh hext hpair sigma c hc w hw hweight
  rw [heterogeneousReplicationFamily_volume_real m q N ε hε tiles htiles hB hf,
    card_balancedLabeling_real m q N hN] at hb
  have heq : (2 * Real.pi) ^ (-(N : ℝ) / 2) *
      Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * R) ^ 2)) *
        (∏ i, w i ^ m) * ((Nat.factorial N : ℝ) / (Nat.factorial m : ℝ) ^ q *
          ∏ i, (ε i ^ (d * m) * (volume B).toReal)) =
      (Nat.factorial N : ℝ) * Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * R) ^ 2)) *
        (2 * Real.pi) ^ (-(N : ℝ) / 2) *
          ((volume B).toReal / (Nat.factorial m : ℝ)) ^ q * ε₀ ^ (d * N) := by
    calc
      _ = ((2 * Real.pi) ^ (-(N : ℝ) / 2) *
          Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * R) ^ 2))) *
            ((Nat.factorial N : ℝ) / (Nat.factorial m : ℝ) ^ q) *
              ((∏ i, w i ^ m) * ∏ i, (ε i ^ (d * m) * (volume B).toReal)) := by ring
      _ = _ := by
        rw [tile_scale_weight_cancellation m q N hN ε w ε₀ _ hcancel, div_pow]
        ring
  rwa [heq] at hb

/-- Positive separation supplies exactly the missing inequalities between
different cubes; pairs within a cube use the already proved reflection gluing. -/
theorem separated_region_tile_conditions (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J q : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (g : Fin q → Fin J)
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) (tiles : Fin q → AlcoveTile d)
    (hinj : Function.Injective (fun i => (g i, tiles i)))
    (hcontain : ∀ i, scaledAlcove d (ε (g i)) (tiles i) ⊆ K (g i))
    (a C R : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (hR : ∀ j, ε j ≤ R)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, a ≤ dist x y)
    (hsmall : 2 * C * R ≤ a / Real.sqrt ((d : ℝ) - 1)) :
    Pairwise (fun i j => Disjoint (interior (scaledAlcove d (ε (g i)) (tiles i)))
      (interior (scaledAlcove d (ε (g j)) (tiles j)))) ∧
    (∀ i l, i ≠ l → (ε (g i) = ε (g l) ∧ tiles i ≠ tiles l) ∨
      ∀ x ∈ referenceSimplex d, ∀ y ∈ referenceSimplex d,
        C * (ε (g i) + ε (g l)) ≤ nativeFloorCost
          (ε (g i) • alcoveChart (tiles i) x) (ε (g l) • alcoveChart (tiles l) y)) := by
  have htile_ne : ∀ i l, i ≠ l → g i = g l → tiles i ≠ tiles l := by
    intro i l hil hgroup ht
    exact hil (hinj (Prod.ext hgroup ht))
  have hpoint (i : Fin q) {x : FloorSpace (Fin d)} (hx : x ∈ referenceSimplex d) :
      ε (g i) • alcoveChart (tiles i) x ∈ K (g i) := by
    apply hcontain i
    refine ⟨alcoveChart (tiles i) x, ?_, rfl⟩
    change alcoveChart (tiles i) x ∈ (tiles i : Set (FloorSpace (Fin d)))
    rw [← alcoveChart_image_reference]
    exact ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · intro i l hil
    by_cases hg : g i = g l
    · rw [hg]
      exact scaledAlcove_disjoint_interiors d H (hε _) (htile_ne i l hil hg)
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hs := hsep (g i) (g l) hg x (hcontain i (interior_subset hx))
        x (hcontain l (interior_subset hy))
      simp only [dist_self] at hs
      linarith
  · intro i l hil
    by_cases hg : g i = g l
    · exact Or.inl ⟨congrArg ε hg, htile_ne i l hil hg⟩
    · right
      intro x hx y hy
      have hdR : 0 < Real.sqrt ((d : ℝ) - 1) := by
        apply Real.sqrt_pos.mpr
        have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      calc
        C * (ε (g i) + ε (g l)) ≤ 2 * C * R := by nlinarith [hR (g i), hR (g l)]
        _ ≤ a / Real.sqrt ((d : ℝ) - 1) := hsmall
        _ ≤ dist (ε (g i) • alcoveChart (tiles i) x) (ε (g l) • alcoveChart (tiles l) y) /
            Real.sqrt ((d : ℝ) - 1) := div_le_div_of_nonneg_right
          (hsep _ _ hg _ (hpoint i hx) _ (hpoint l hy)) hdR.le
        _ ≤ _ := by
          rw [dist_eq_norm]
          exact norm_div_sqrt_le_nativeFloorCost hd _ _

/-- The actual total collection of complete alcoves, retaining the region
index because different cubes use different scales. -/
def CompleteRegionTiles (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (hK : ∀ j, IsCompact (K j))
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) :=
  Σ j : Fin J, {t // t ∈ completeAlcoves hd H (ε j) (hε j) (K j) (hK j)}

instance (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (hK : ∀ j, IsCompact (K j))
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) :
    Fintype (CompleteRegionTiles hd H J K hK ε hε) := by
  classical
  unfold CompleteRegionTiles
  infer_instance

def completeRegionTileCount (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (hK : ∀ j, IsCompact (K j))
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) : ℕ :=
  Fintype.card (CompleteRegionTiles hd H J K hK ε hε)

def completeRegionTileEquiv (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (hK : ∀ j, IsCompact (K j))
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) :
    Fin (completeRegionTileCount hd H J K hK ε hε) ≃ CompleteRegionTiles hd H J K hK ε hε :=
  (Fintype.equivFin _).symm

theorem completeRegionTileCount_eq_sum (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (hK : ∀ j, IsCompact (K j))
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) :
    completeRegionTileCount hd H J K hK ε hε =
      ∑ j, (completeAlcoves hd H (ε j) (hε j) (K j) (hK j)).card := by
  classical
  simp only [completeRegionTileCount, CompleteRegionTiles, Fintype.card_sigma,
    Fintype.card_coe]

theorem completeRegionTile_index_injective (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (hK : ∀ j, IsCompact (K j))
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) :
    Function.Injective (fun i =>
      ((completeRegionTileEquiv hd H J K hK ε hε i).1,
        (completeRegionTileEquiv hd H J K hK ε hε i).2.val)) := by
  intro i l hil
  apply (completeRegionTileEquiv hd H J K hK ε hε).injective
  dsimp only at hil
  generalize hx : completeRegionTileEquiv hd H J K hK ε hε i = x at hil ⊢
  generalize hy : completeRegionTileEquiv hd H J K hK ε hε l = y at hil ⊢
  rcases x with ⟨j, t⟩
  rcases y with ⟨k, u⟩
  have hj := congrArg Prod.fst hil
  dsimp only at hj
  subst k
  have ht : t = u := Subtype.ext (congrArg Prod.snd hil)
  subst u
  rfl

theorem complete_regions_weighted_lower (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (J m : ℕ) (K : Fin J → Set (FloorSpace (Fin d))) (hK : ∀ j, IsCompact (K j))
    (ε : Fin J → ℝ) (hε : ∀ j, 0 < ε j) (ε₀ a C R : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hR0 : 0 ≤ R) (hR : ∀ j, ε j ≤ R)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, a ≤ dist x y)
    (hsmall : 2 * C * R ≤ a / Real.sqrt ((d : ℝ) - 1))
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧ (∀ v : SimplexBoundary d, E v.val = boundary v) ∧
      (∀ u v, E u - E v ≤ nativeFloorCost u v))
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (w : Fin J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hweight : ∀ j x, x ∈ K j → w j ≤ weightedFloorDensity sigma x)
    (hcancel : ∀ j, w j * ε j ^ d = ε₀ ^ d) :
    let Q := completeRegionTileCount hd H J K hK ε hε
    let N := Q * m
    (Nat.factorial N : ℝ) * Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * R) ^ 2)) *
      (2 * Real.pi) ^ (-(N : ℝ) / 2) * ((volume B).toReal / (Nat.factorial m : ℝ)) ^ Q *
        ε₀ ^ (d * N) ≤ weightedPartition N sigma c := by
  let Q := completeRegionTileCount hd H J K hK ε hε
  let e := completeRegionTileEquiv hd H J K hK ε hε
  let g : Fin Q → Fin J := fun i => (e i).1
  let tiles : Fin Q → AlcoveTile d := fun i => (e i).2.val
  have hcontain : ∀ i, scaledAlcove d (ε (g i)) (tiles i) ⊆ K (g i) := by
    intro i
    exact (mem_completeAlcoves hd H (ε (g i)) (hε (g i)) (K (g i)) (hK (g i)) (tiles i)).mp
      (e i).2.property
  have hdata := separated_region_tile_conditions hd H J Q K g ε hε tiles
    (completeRegionTile_index_injective hd H J K hK ε hε) hcontain a C R ha hC hR hsep hsmall
  exact heterogeneous_weighted_partition_lower hd H m Q (Q * m) rfl (fun i => ε (g i))
    (fun i => hε _) ε₀ C R hC hR0 (fun i => hR _) tiles hdata.1 hB boundary hf hh hext hdata.2
    sigma c hc (fun i => w (g i)) (fun i => hw _)
    (fun i x hx => hweight _ x (hcontain i hx)) (fun i => hcancel _)

def cubeScaleMultiplier (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (j : Fin J) : ℝ :=
  floorCubeWeightInf sigma b (a j) (L j) ^ (-1 / (d : ℝ))

def cubeScaleBound (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) : ℝ :=
  1 + ∑ j, cubeScaleMultiplier sigma b J a L j

def weightedCubeTileCount (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (ε : ℝ) : ℕ :=
  ∑ j, completeCubeTileCount b (a j) (L j) (ε * cubeScaleMultiplier sigma b J a L j)

omit [NeZero d] in
theorem cubeScaleMultiplier_pos (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (j : Fin J) : 0 < cubeScaleMultiplier sigma b J a L j :=
  Real.rpow_pos_of_pos (floorCubeWeightInf_pos sigma b (a j) (hL j)) _

omit [NeZero d] in
theorem cubeScaleBound_pos (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 ≤ L j) :
    0 < cubeScaleBound sigma b J a L := by
  unfold cubeScaleBound
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun j _ => (cubeScaleMultiplier_pos sigma b J a L hL j).le))

omit [NeZero d] in
theorem cubeScaleMultiplier_le_bound (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (j : Fin J) :
    cubeScaleMultiplier sigma b J a L j ≤ cubeScaleBound sigma b J a L := by
  exact (Finset.single_le_sum (fun i _ => (cubeScaleMultiplier_pos sigma b J a L hL i).le)
    (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

theorem cubeScaleMultiplier_cancellation (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (ε : ℝ) (j : Fin J) :
    floorCubeWeightInf sigma b (a j) (L j) *
      (ε * cubeScaleMultiplier sigma b J a L j) ^ d = ε ^ d := by
  let w := floorCubeWeightInf sigma b (a j) (L j)
  have hw : 0 < w := floorCubeWeightInf_pos sigma b (a j) (hL j)
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hpow : (w ^ (-1 / (d : ℝ))) ^ d = w⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    rw [div_mul_cancel₀ _ hdR, Real.rpow_neg_one]
  change w * (ε * w ^ (-1 / (d : ℝ))) ^ d = ε ^ d
  rw [mul_pow, hpow]
  field_simp

theorem weightedCubeTileCount_eq_regions (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ)
    (hL : ∀ j, 0 ≤ L j) (ε : ℝ) (hε : 0 < ε) :
    weightedCubeTileCount sigma b J a L ε =
      completeRegionTileCount hd H J (fun j => orthonormalFloorCube b (a j) (L j))
        (fun j => isCompact_orthonormalFloorCube b (a j) (L j))
        (fun j => ε * cubeScaleMultiplier sigma b J a L j)
        (fun j => mul_pos hε (cubeScaleMultiplier_pos sigma b J a L hL j)) := by
  rw [completeRegionTileCount_eq_sum]
  unfold weightedCubeTileCount
  apply Finset.sum_congr rfl
  intro j _
  exact completeCubeTileCount_eq_card hd H b (a j) (L j) _
    (mul_pos hε (cubeScaleMultiplier_pos sigma b J a L hL j))

/-- The exact finite-scale lower bound for the paper's actual complete cubes,
using their true infimum floor weights and their prescribed weight-dependent
tile scales. This is the geometric/integral step of Lemma 5.4. -/
theorem weighted_cubes_partition_lower (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J m : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (sep C : ℝ) (hsep0 : 0 < sep) (hC : 0 ≤ C)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ orthonormalFloorCube b (a i) (L i),
      ∀ y ∈ orthonormalFloorCube b (a j) (L j), sep ≤ dist x y)
    {B : Set (FloorHeightConfiguration m d)} (hB : MeasurableSet B)
    (boundary : SimplexBoundary d → ℝ)
    (hf : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d))
    (hh : ∀ p ∈ B, ∀ j, |p.2 j| ≤ C)
    (hext : ∀ p ∈ B, ∃ E : FloorSpace (Fin d) → ℝ,
      (∀ j, E (p.1 j) = p.2 j) ∧ (∀ v : SimplexBoundary d, E v.val = boundary v) ∧
      (∀ u v, E u - E v ≤ nativeFloorCost u v))
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : 2 * C * (ε * cubeScaleBound sigma b J a L) ≤
      sep / Real.sqrt ((d : ℝ) - 1)) :
    let Q := weightedCubeTileCount sigma b J a L ε
    let N := Q * m
    (Nat.factorial N : ℝ) *
      Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) * (C * (ε * cubeScaleBound sigma b J a L)) ^ 2)) *
        (2 * Real.pi) ^ (-(N : ℝ) / 2) * ((volume B).toReal / (Nat.factorial m : ℝ)) ^ Q *
          ε ^ (d * N) ≤ weightedPartition N sigma c := by
  have hL0 : ∀ j, 0 ≤ L j := fun j => (hL j).le
  have hscalepos : ∀ j, 0 < ε * cubeScaleMultiplier sigma b J a L j :=
    fun j => mul_pos hε (cubeScaleMultiplier_pos sigma b J a L hL0 j)
  have hbound : ∀ j, ε * cubeScaleMultiplier sigma b J a L j ≤ ε * cubeScaleBound sigma b J a L :=
    fun j => mul_le_mul_of_nonneg_left (cubeScaleMultiplier_le_bound sigma b J a L hL0 j) hε.le
  have hweight : ∀ j x, x ∈ orthonormalFloorCube b (a j) (L j) →
      floorCubeWeightInf sigma b (a j) (L j) ≤ weightedFloorDensity sigma x := by
    intro j x hx
    exact (floorCubeWeightInf_attained sigma b (a j) (hL0 j)).choose_spec.2.2 x hx
  have hb := complete_regions_weighted_lower hd H J m
    (fun j => orthonormalFloorCube b (a j) (L j))
    (fun j => isCompact_orthonormalFloorCube b (a j) (L j))
    (fun j => ε * cubeScaleMultiplier sigma b J a L j) hscalepos ε sep C
    (ε * cubeScaleBound sigma b J a L) hsep0 hC
    (mul_nonneg hε.le (cubeScaleBound_pos sigma b J a L hL0).le) hbound hsep hsmall
    hB boundary hf hh hext sigma c hc (fun j => floorCubeWeightInf sigma b (a j) (L j))
    (fun j => (floorCubeWeightInf_pos sigma b (a j) (hL0 j)).le) hweight
    (cubeScaleMultiplier_cancellation sigma b J a L hL0 ε)
  dsimp only at hb ⊢
  rw [weightedCubeTileCount_eq_regions hd H sigma b J a L hL0 ε hε]
  exact hb

/-- The source local family and the complete-cube construction composed,
ready for the scalar size-selection and limiting arguments. V is the actual
ordinary volume of the proved measurable matched family, not an assumed
coefficient. The scale cutoff is fixed before the local sample count. -/
theorem matching_weighted_cubes_finite_scale (hd : 2 ≤ d) (H : HumphreysAlcoveInput d)
    (sigma : FloorSpace (Fin d) →ᵇ ℝ) (c : ℝ) (hc : c < 1 / 2)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (J : ℕ) (a : Fin J → Fin (d - 1) → ℝ) (L : Fin J → ℝ) (hL : ∀ j, 0 < L j)
    (sep : ℝ) (hsep0 : 0 < sep)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ orthonormalFloorCube b (a i) (L i),
      ∀ y ∈ orthonormalFloorCube b (a j) (L j), sep ≤ dist x y) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ eta lam : ℝ, eta ∈ Ioo 0 (1 / 2 : ℝ) → lam ∈ Ioo 0 (1 / 2 : ℝ) →
      ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ, ∃ V : ℝ, 0 < V ∧
        (2 / (M : ℝ)) * (1 - eta) ^ (d * (r + 1)) * (1 - lam) ^ (r + 1) *
          pinnedVolume (referenceSimplex d) r ≤ V ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          let Q := weightedCubeTileCount sigma b J a L ε
          let N := Q * (r + 1)
          (Nat.factorial N : ℝ) *
            Real.exp (-(N : ℝ) * (((1 / 2 : ℝ) - c) *
              (C * (ε * cubeScaleBound sigma b J a L)) ^ 2)) *
            (2 * Real.pi) ^ (-(N : ℝ) / 2) * (V / (Nat.factorial (r + 1) : ℝ)) ^ Q *
              ε ^ (d * N) ≤ weightedPartition N sigma c := by
  obtain ⟨C, hC, hCM⟩ := boundary_matching_source hd
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hL0 : ∀ j, 0 ≤ L j := fun j => (hL j).le
  let A := cubeScaleBound sigma b J a L
  have hA : 0 < A := cubeScaleBound_pos sigma b J a L hL0
  have hsqrt : 0 < Real.sqrt ((d : ℝ) - 1) := by
    apply Real.sqrt_pos.mpr
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let δ := (sep / Real.sqrt ((d : ℝ) - 1)) / (2 * C * A)
  have hδ : 0 < δ := div_pos (div_pos hsep0 hsqrt) (by positivity)
  refine ⟨C, hC, δ, hδ, fun eta lam heta hlam => ?_⟩
  obtain ⟨M, hM, hMB⟩ := hCM eta lam heta hlam
  refine ⟨M, hM, fun r => ?_⟩
  obtain ⟨B, boundary, hB, hBevent, hBbound, hBext, hBvolume⟩ := hMB r
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have heta1 : eta < 1 := heta.2.trans (by norm_num)
  have hlam1 : lam < 1 := hlam.2.trans (by norm_num)
  have hbase : 0 < (2 / (M : ℝ)) * (1 - eta) ^ (d * (r + 1)) *
      (1 - lam) ^ (r + 1) * pinnedVolume (referenceSimplex d) r :=
    mul_pos (mul_pos (mul_pos (div_pos (by norm_num) hMpos)
      (pow_pos (sub_pos.mpr heta1) _)) (pow_pos (sub_pos.mpr hlam1) _))
      (pinnedVolume_referenceSimplex_pos hd r)
  refine ⟨(volume B).toReal, hbase.trans_le hBvolume, hBvolume, ?_⟩
  intro ε hε hεδ
  have hsmall : 2 * C * (ε * cubeScaleBound sigma b J a L) ≤
      sep / Real.sqrt ((d : ℝ) - 1) := by
    have hm := (le_div_iff₀ (show 0 < 2 * C * A by positivity)).mp hεδ
    nlinarith
  have hfloor : ∀ p ∈ B, ∀ j, p.1 j ∈ interior (referenceSimplex d) := by
    intro p hp j
    by_contra hn
    have hfront : p.1 j ∈ frontier (referenceSimplex d) :=
      ⟨subset_closure ((hBevent p hp).1 j), hn⟩
    have hm := (hBbound p hp j).2
    rw [Metric.infDist_zero_of_mem hfront] at hm
    have hpos : 0 < eta / C := div_pos heta.1 hCp
    linarith
  exact weighted_cubes_partition_lower hd H sigma c hc b J (r + 1) a L hL sep C hsep0 hCp.le
    hsep hB boundary hfloor (fun p hp j => (hBbound p hp j).1) hBext ε hε hsmall

end Antichain
