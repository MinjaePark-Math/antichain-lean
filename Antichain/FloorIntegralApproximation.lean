import Antichain.TileGaussianSums
import Antichain.CubeTileCount
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Actual positive Gaussian weight integrals and finite cube lower approximations. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Finset Filter
open scoped Topology ENNReal BoundedContinuousFunction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem weightedFloorDensity_rpow_continuous (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p) : Continuous (fun u ↦ weightedFloorDensity σ u ^ p) :=
  (Real.continuous_rpow_const hp.le).comp (weightedFloorDensity_continuous σ)

theorem weightedFloorDensity_rpow_le_gaussian (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p) (u : FloorSpace (Fin d)) :
    weightedFloorDensity σ u ^ p ≤ gaussianTileMajorantConstant σ p *
      Real.exp (-(p / 4) * ‖u‖ ^ 2) := by
  rw [weightedFloorDensity, standardFloorDensity_formula, Fintype.card_fin]
  let C : ℝ := (2 * Real.pi) ^ (-((d : ℝ) - 1) / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  change (C * Real.exp (-‖u‖ ^ 2 / 2) * Real.exp (σ u)) ^ p ≤ _
  rw [mul_assoc, ← Real.exp_add, Real.mul_rpow hC (Real.exp_nonneg _), ← Real.exp_mul]
  unfold gaussianTileMajorantConstant
  change C ^ p * Real.exp ((-‖u‖ ^ 2 / 2 + σ u) * p) ≤
    (C ^ p * Real.exp (p * ‖σ‖ + p * (2 * (d : ℝ)) ^ 2 / 2)) *
      Real.exp (-(p / 4) * ‖u‖ ^ 2)
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC p)
  apply Real.exp_le_exp.mpr
  have hσ := σ.apply_le_norm u
  nlinarith [sq_nonneg ‖u‖, sq_nonneg (2 * (d : ℝ))]

theorem weightedFloorDensity_rpow_integrable (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p) : Integrable (fun u ↦ weightedFloorDensity σ u ^ p) := by
  apply (integrable_gaussianTileMajorant σ hp).mono'
    (weightedFloorDensity_rpow_continuous σ hp).aestronglyMeasurable
  exact Eventually.of_forall (fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (weightedFloorDensity_pos σ u).le p)]
    exact weightedFloorDensity_rpow_le_gaussian σ hp u)

theorem weightedFloorDensity_rpow_integral_pos (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p) : 0 < ∫ u, weightedFloorDensity σ u ^ p :=
  integral_pos_of_integrable_nonneg_nonzero (weightedFloorDensity_rpow_continuous σ hp)
    (weightedFloorDensity_rpow_integrable σ hp)
    (fun u ↦ (Real.rpow_pos_of_pos (weightedFloorDensity_pos σ u) p).le)
    (ne_of_gt (Real.rpow_pos_of_pos (weightedFloorDensity_pos σ 0) p))

def floorCubeWeightInf (σ : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) : ℝ :=
  sInf (weightedFloorDensity σ '' orthonormalFloorCube b a L)

omit [NeZero d] in
theorem orthonormalFloorCube_nonempty
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (orthonormalFloorCube b a L).Nonempty := by
  refine ⟨b.repr.symm (WithLp.toLp 2 a), ?_⟩
  intro i
  change a i ≤ b.repr (b.repr.symm (WithLp.toLp 2 a)) i ∧ _
  rw [b.repr.apply_symm_apply]
  exact ⟨le_rfl, le_add_of_nonneg_right hL⟩

omit [NeZero d] in
theorem floorCubeWeightInf_attained (σ : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ v ∈ orthonormalFloorCube b a L,
      floorCubeWeightInf σ b a L = weightedFloorDensity σ v ∧
        ∀ u ∈ orthonormalFloorCube b a L, floorCubeWeightInf σ b a L ≤ weightedFloorDensity σ u := by
  obtain ⟨v, hv, hmin⟩ := (isCompact_orthonormalFloorCube b a L).exists_isMinOn
    (orthonormalFloorCube_nonempty b a hL) (weightedFloorDensity_continuous σ).continuousOn
  have hg : IsLeast (weightedFloorDensity σ '' orthonormalFloorCube b a L) (weightedFloorDensity σ v) := by
    refine ⟨Set.mem_image_of_mem _ hv, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hmin hu
  have heq : floorCubeWeightInf σ b a L = weightedFloorDensity σ v := hg.csInf_eq
  exact ⟨v, hv, heq, fun u hu ↦ by rw [heq]; exact hmin hu⟩

omit [NeZero d] in
theorem floorCubeWeightInf_pos (σ : FloorSpace (Fin d) →ᵇ ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 ≤ L) : 0 < floorCubeWeightInf σ b a L := by
  obtain ⟨v, _, heq, _⟩ := floorCubeWeightInf_attained σ b a hL
  rw [heq]
  exact weightedFloorDensity_pos σ v

/-- Slightly shrunken mesh cubes leave positive gaps between their closures. -/
def floorMeshSide (L : ℝ) (n : ℕ) : ℝ := L / (n + 2) * (1 - 1 / (n + 2))

def floorMeshOrigin (a : Fin (d - 1) → ℝ) (L : ℝ) (n : ℕ)
    (k : Fin (d - 1) → Fin (n + 2)) : Fin (d - 1) → ℝ :=
  fun i ↦ a i + (k i : ℝ) * (L / (n + 2))

def floorMeshCube (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) (n : ℕ) (k : Fin (d - 1) → Fin (n + 2)) :
    Set (FloorSpace (Fin d)) := orthonormalFloorCube b (floorMeshOrigin a L n k) (floorMeshSide L n)

omit [NeZero d] in
theorem floorMeshSide_pos {L : ℝ} (hL : 0 < L) (n : ℕ) : 0 < floorMeshSide L n := by
  have hN : (1 : ℝ) < n + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  unfold floorMeshSide
  exact mul_pos (div_pos hL (by positivity)) (sub_pos.mpr ((div_lt_one (by positivity)).mpr hN))

omit [NeZero d] in
theorem floorMeshSide_lt_step {L : ℝ} (hL : 0 < L) (n : ℕ) : floorMeshSide L n < L / (n + 2) := by
  unfold floorMeshSide
  have hstep : 0 < L / (n + 2) := div_pos hL (by positivity)
  have hinv : (0 : ℝ) < 1 / (n + 2) := by positivity
  nlinarith

omit [NeZero d] in
theorem floorMeshCube_subset
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) (n : ℕ)
    (k : Fin (d - 1) → Fin (n + 2)) : floorMeshCube b a L n k ⊆ orthonormalFloorCube b a L := by
  intro x hx i
  have hxi := hx i
  have hstep : 0 ≤ L / (n + 2) := by positivity
  have hk : (k i : ℝ) + 1 ≤ n + 2 := by exact_mod_cast (k i).isLt
  have hk0 : (0 : ℝ) ≤ (k i : ℝ) := by positivity
  have htop : ((k i : ℝ) + 1) * (L / (n + 2)) ≤ L := by
    calc
      _ ≤ (n + 2 : ℝ) * (L / (n + 2)) := mul_le_mul_of_nonneg_right hk hstep
      _ = L := by field_simp
  have hs := (floorMeshSide_lt_step hL n).le
  dsimp [floorMeshCube, orthonormalFloorCube, floorMeshOrigin] at hxi
  constructor <;> nlinarith [mul_nonneg hk0 hstep]

omit [NeZero d] in
theorem floorMeshCube_pairwise_disjoint
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    Pairwise (fun k l : Fin (d - 1) → Fin (n + 2) ↦
      Disjoint (floorMeshCube b a L n k) (floorMeshCube b a L n l)) := by
  intro k l hkl
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx := hx i
  have hy := hy i
  have hstep : 0 < L / (n + 2) := by positivity
  have hs := floorMeshSide_lt_step hL n
  dsimp [floorMeshCube, orthonormalFloorCube, floorMeshOrigin] at hx hy
  rcases lt_or_gt_of_ne hi with hi | hi
  · have hij : (k i : ℝ) + 1 ≤ (l i : ℝ) := by exact_mod_cast hi
    nlinarith [mul_le_mul_of_nonneg_right hij hstep.le]
  · have hij : (l i : ℝ) + 1 ≤ (k i : ℝ) := by exact_mod_cast hi
    nlinarith [mul_le_mul_of_nonneg_right hij hstep.le]

omit [NeZero d] in
theorem orthonormalFloorCube_dist_le
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} {x y : FloorSpace (Fin d)}
    (hx : x ∈ orthonormalFloorCube b a L) (hy : y ∈ orthonormalFloorCube b a L) :
    dist x y ≤ (d - 1 : ℕ) * L := by
  rw [dist_eq_norm]
  calc
    ‖x - y‖ = ‖∑ i, b.repr (x - y) i • b i‖ := congrArg norm (b.sum_repr (x - y)).symm
    _ ≤ ∑ i, ‖b.repr (x - y) i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (d - 1), L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs]
      change |b.repr (x - y) i| ≤ L
      rw [map_sub]
      change |b.repr x i - b.repr y i| ≤ L
      exact abs_le.mpr ⟨by linarith [(hx i).1, (hy i).2], by linarith [(hx i).2, (hy i).1]⟩
    _ = _ := by simp

def floorMeshUnion
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) (n : ℕ) : Set (FloorSpace (Fin d)) :=
  ⋃ k : Fin (d - 1) → Fin (n + 2), floorMeshCube b a L n k

omit [NeZero d] in
theorem measurableSet_floorMeshUnion
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) (n : ℕ) : MeasurableSet (floorMeshUnion b a L n) :=
  MeasurableSet.iUnion (fun k ↦ (isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k)
    (floorMeshSide L n)).measurableSet)

omit [NeZero d] in
theorem floorMeshUnion_subset
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    floorMeshUnion b a L n ⊆ orthonormalFloorCube b a L :=
  Set.iUnion_subset (floorMeshCube_subset b a hL n)

omit [NeZero d] in
theorem volumeReal_floorMeshUnion
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    (volume : Measure (FloorSpace (Fin d))).real (floorMeshUnion b a L n) =
      (L * (1 - 1 / (n + 2))) ^ (d - 1) := by
  rw [floorMeshUnion, measureReal_iUnion_fintype (floorMeshCube_pairwise_disjoint b a hL n)
    (fun k ↦ (isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k)
      (floorMeshSide L n)).measurableSet)
    (fun k ↦ (isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k)
      (floorMeshSide L n)).measure_lt_top.ne)]
  simp only [floorMeshCube, measureReal_def, volume_orthonormalFloorCube,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (floorMeshSide_pos hL n).le,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [← mul_pow]
  congr 1
  unfold floorMeshSide
  field_simp

omit [NeZero d] in
theorem tendsto_floorMeshSide (L : ℝ) : Tendsto (floorMeshSide L) atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
  have hstep : Tendsto (fun n : ℕ ↦ L / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_one_div] using hInv.const_mul L
  simpa only [mul_zero, sub_zero, zero_mul, floorMeshSide] using
    hstep.mul (tendsto_const_nhds.sub hInv)

omit [NeZero d] in
theorem tendsto_volumeReal_floorMeshUnion
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n ↦ (volume : Measure (FloorSpace (Fin d))).real (floorMeshUnion b a L n))
      atTop (𝓝 (L ^ (d - 1))) := by
  simp_rw [volumeReal_floorMeshUnion b a hL]
  have hInv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
  simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hInv).const_mul L).pow (d - 1)

omit [NeZero d] in
theorem volumeReal_orthonormalFloorCube
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (volume : Measure (FloorSpace (Fin d))).real (orthonormalFloorCube b a L) = L ^ (d - 1) := by
  rw [measureReal_def, volume_orthonormalFloorCube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL]

def floorMeshLowerSum (σ : FloorSpace (Fin d) →ᵇ ℝ) (p : ℝ)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) (L : ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin (d - 1) → Fin (n + 2), floorMeshSide L n ^ (d - 1) *
    floorCubeWeightInf σ b (floorMeshOrigin a L n k) (floorMeshSide L n) ^ p

theorem floorMeshLowerSum_le_integral (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    floorMeshLowerSum σ p b a L n ≤ ∫ u in floorMeshUnion b a L n, weightedFloorDensity σ u ^ p := by
  rw [floorMeshUnion, integral_iUnion_fintype (s := fun k ↦ floorMeshCube b a L n k)
    (fun k ↦ (isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k)
      (floorMeshSide L n)).measurableSet)
    (floorMeshCube_pairwise_disjoint b a hL n)
    (fun _ ↦ (weightedFloorDensity_rpow_integrable σ hp).integrableOn)]
  unfold floorMeshLowerSum
  apply Finset.sum_le_sum
  intro k _
  have hc := isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k) (floorMeshSide L n)
  rw [← volumeReal_orthonormalFloorCube b _ (floorMeshSide_pos hL n).le]
  rw [mul_comm]
  apply setIntegral_ge_of_const_le hc.measurableSet hc.measure_lt_top.ne _
    (weightedFloorDensity_rpow_integrable σ hp).integrableOn
  intro u hu
  obtain ⟨_, _, _, hmin⟩ := floorCubeWeightInf_attained σ b
    (floorMeshOrigin a L n k) (floorMeshSide_pos hL n).le
  exact Real.rpow_le_rpow (floorCubeWeightInf_pos σ b _ (floorMeshSide_pos hL n).le).le (hmin u hu) hp.le

/-- On a fixed compact cube, the actual finite lower sums approach its integral. -/
theorem exists_floorMeshLowerSum_close (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    (a : Fin (d - 1) → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 < η) :
    ∃ n : ℕ, (∫ u in orthonormalFloorCube b a L, weightedFloorDensity σ u ^ p) - η <
      floorMeshLowerSum σ p b a L n := by
  let F : FloorSpace (Fin d) → ℝ := fun u ↦ weightedFloorDensity σ u ^ p
  let K := orthonormalFloorCube b a L
  let V := L ^ (d - 1)
  have hV : 0 ≤ V := pow_nonneg hL.le _
  have hF : Continuous F := weightedFloorDensity_rpow_continuous σ hp
  have hi : Integrable F := weightedFloorDensity_rpow_integrable σ hp
  have hK : IsCompact K := isCompact_orthonormalFloorCube b a L
  have hKV : (volume : Measure (FloorSpace (Fin d))).real K = V :=
    volumeReal_orthonormalFloorCube b a hL.le
  obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn (orthonormalFloorCube_nonempty b a hL.le) hF.continuousOn
  let M := F v
  let α := η / (2 * (V + 1))
  have hα : 0 < α := div_pos hη (by positivity)
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hF.continuousOn) α hα
  have hmesh : Tendsto (fun n ↦ (d - 1 : ℕ) * floorMeshSide L n) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_floorMeshSide L).const_mul ((d - 1 : ℕ) : ℝ)
  have hgap : Tendsto (fun n ↦ M * (V - (volume : Measure (FloorSpace (Fin d))).real
      (floorMeshUnion b a L n))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [V, sub_self, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ V) atTop (𝓝 V)).sub
        (tendsto_volumeReal_floorMeshUnion b a hL)).const_mul M
  obtain ⟨n, hnmesh, hngap⟩ := ((hmesh.eventually_lt_const hδ).and
    (hgap.eventually_lt_const (half_pos hη))).exists
  let U := floorMeshUnion b a L n
  have hU : MeasurableSet U := measurableSet_floorMeshUnion b a L n
  have hUK : U ⊆ K := floorMeshUnion_subset b a hL n
  have hUV : (volume : Measure (FloorSpace (Fin d))).real U ≤ V := by
    rw [← hKV]
    exact measureReal_mono hUK hK.measure_lt_top.ne
  have hsplit : (∫ u in U, F u) + ∫ u in K \ U, F u = ∫ u in K, F u := by
    have h := integral_inter_add_diff hU hi.integrableOn (s := K)
    rwa [Set.inter_eq_right.mpr hUK] at h
  have hdiff : (∫ u in K \ U, F u) ≤ M *
      (V - (volume : Measure (FloorSpace (Fin d))).real U) := by
    have hb := setIntegral_mono_on hi.integrableOn
      (integrableOn_const (measure_ne_top_of_subset Set.diff_subset hK.measure_lt_top.ne))
      (hK.measurableSet.diff hU) (fun u hu ↦ hmax hu.1)
    simpa only [setIntegral_const, smul_eq_mul, measureReal_diff hUK hU hK.measure_lt_top.ne,
      hKV, mul_comm] using hb
  have hupper : (∫ u in U, F u) ≤ floorMeshLowerSum σ p b a L n +
      α * (volume : Measure (FloorSpace (Fin d))).real U := by
    rw [show U = ⋃ k, floorMeshCube b a L n k from rfl,
      integral_iUnion_fintype (s := fun k ↦ floorMeshCube b a L n k)
        (fun k ↦ (isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k)
          (floorMeshSide L n)).measurableSet)
        (floorMeshCube_pairwise_disjoint b a hL n) (fun _ ↦ hi.integrableOn)]
    have hcub (k : Fin (d - 1) → Fin (n + 2)) :
        (∫ u in floorMeshCube b a L n k, F u) ≤
          floorMeshSide L n ^ (d - 1) *
            (floorCubeWeightInf σ b (floorMeshOrigin a L n k) (floorMeshSide L n) ^ p + α) := by
      have hc := isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k) (floorMeshSide L n)
      obtain ⟨w, hw, hmin, _⟩ := floorCubeWeightInf_attained σ b
        (floorMeshOrigin a L n k) (floorMeshSide_pos hL n).le
      have hb := setIntegral_mono_on (g := fun _ ↦
        floorCubeWeightInf σ b (floorMeshOrigin a L n k) (floorMeshSide L n) ^ p + α)
        hi.integrableOn (integrableOn_const hc.measure_lt_top.ne)
        hc.measurableSet (fun u hu ↦ ?_)
      · simpa only [setIntegral_const, smul_eq_mul,
          volumeReal_orthonormalFloorCube b _ (floorMeshSide_pos hL n).le] using hb
      · have hclose := huc u (floorMeshCube_subset b a hL n k hu) w
          (floorMeshCube_subset b a hL n k hw)
          ((orthonormalFloorCube_dist_le b _ hu hw).trans_lt hnmesh)
        rw [Real.dist_eq] at hclose
        have habs := (abs_lt.mp hclose).2
        dsimp [F] at habs ⊢
        rw [hmin]
        linarith
    calc
      _ ≤ ∑ k, floorMeshSide L n ^ (d - 1) *
          (floorCubeWeightInf σ b (floorMeshOrigin a L n k) (floorMeshSide L n) ^ p + α) :=
        Finset.sum_le_sum (fun k _ ↦ hcub k)
      _ = floorMeshLowerSum σ p b a L n + α *
          (volume : Measure (FloorSpace (Fin d))).real U := by
        rw [show U = ⋃ k, floorMeshCube b a L n k from rfl,
          measureReal_iUnion_fintype (f := fun k ↦ floorMeshCube b a L n k)
            (floorMeshCube_pairwise_disjoint b a hL n)
            (fun k ↦ (isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k)
              (floorMeshSide L n)).measurableSet)
            (fun k ↦ (isCompact_orthonormalFloorCube b (floorMeshOrigin a L n k)
              (floorMeshSide L n)).measure_lt_top.ne)]
        simp only [floorMeshLowerSum, floorMeshCube,
          volumeReal_orthonormalFloorCube b _ (floorMeshSide_pos hL n).le,
          mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  refine ⟨n, ?_⟩
  have hαV : α * V < η / 2 := by
    have heq : α * (V + 1) = η / 2 := by dsimp [α]; field_simp
    nlinarith
  have hαUV : α * (volume : Measure (FloorSpace (Fin d))).real U ≤ α * V :=
    mul_le_mul_of_nonneg_left hUV hα.le
  change (∫ u in K, F u) - η < _
  dsimp [U, M] at hngap
  linarith

def floorExhaustionCube
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d))) (n : ℕ) :
    Set (FloorSpace (Fin d)) :=
  orthonormalFloorCube b (fun _ ↦ -((n : ℝ) + 1)) (2 * ((n : ℝ) + 1))

omit [NeZero d] in
theorem floorExhaustionCube_monotone
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d))) :
    Monotone (floorExhaustionCube b) := by
  intro n m hnm x hx i
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hxi := hx i
  dsimp [floorExhaustionCube, orthonormalFloorCube] at hxi ⊢
  constructor <;> linarith [hxi.1, hxi.2]

omit [NeZero d] in
theorem floorExhaustionCube_covers
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d))) :
    (⋃ n : ℕ, floorExhaustionCube b n) = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  intro i
  have hc : |b.repr x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs, b.repr.norm_map] using PiLp.norm_apply_le (b.repr x) i
  have hbounds := abs_le.mp hc
  dsimp [floorExhaustionCube, orthonormalFloorCube]
  constructor <;> linarith [hbounds.1, hbounds.2]

theorem tendsto_integral_floorExhaustionCube (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d))) :
    Tendsto (fun n : ℕ ↦ ∫ u in floorExhaustionCube b n, weightedFloorDensity σ u ^ p)
      atTop (𝓝 (∫ u, weightedFloorDensity σ u ^ p)) := by
  have h := tendsto_setIntegral_of_monotone (s := floorExhaustionCube b)
    (fun n : ℕ ↦ (isCompact_orthonormalFloorCube b (fun _ ↦ -((n : ℝ) + 1))
      (2 * ((n : ℝ) + 1))).measurableSet)
    (floorExhaustionCube_monotone b) (weightedFloorDensity_rpow_integrable σ hp).integrableOn
  simpa only [floorExhaustionCube_covers b, setIntegral_univ] using h

/-- Every desired accuracy is realized by finitely many actual closed cubes.
Their closures are disjoint, and the weights are the actual positive cube infima. -/
theorem exists_floorCube_lower_approximation (σ : FloorSpace (Fin d) →ᵇ ℝ)
    {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin (d - 1)) ℝ (FloorSpace (Fin d)))
    {η : ℝ} (hη : 0 < η) :
    ∃ q : ℕ, 0 < q ∧ ∃ a : Fin q → Fin (d - 1) → ℝ, ∃ L : ℝ, 0 < L ∧
      Pairwise (fun i j ↦ Disjoint (orthonormalFloorCube b (a i) L)
        (orthonormalFloorCube b (a j) L)) ∧
      (∑ i, L ^ (d - 1) * floorCubeWeightInf σ b (a i) L ^ p) ≤
        (∫ u, weightedFloorDensity σ u ^ p) ∧
      (∫ u, weightedFloorDensity σ u ^ p) - η <
        ∑ i, L ^ (d - 1) * floorCubeWeightInf σ b (a i) L ^ p := by
  let I := ∫ u, weightedFloorDensity σ u ^ p
  obtain ⟨R, hR⟩ := ((tendsto_integral_floorExhaustionCube σ hp b).eventually
    (Ioi_mem_nhds (show I - η / 2 < I by dsimp [I]; linarith))).exists
  let a₀ : Fin (d - 1) → ℝ := fun _ ↦ -((R : ℝ) + 1)
  let L₀ : ℝ := 2 * ((R : ℝ) + 1)
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  obtain ⟨n, hn⟩ := exists_floorMeshLowerSum_close σ hp b a₀ hL₀ (half_pos hη)
  let q := Fintype.card (Fin (d - 1) → Fin (n + 2))
  let e : Fin q ≃ (Fin (d - 1) → Fin (n + 2)) := (Fintype.equivFin _).symm
  let a : Fin q → Fin (d - 1) → ℝ := fun i ↦ floorMeshOrigin a₀ L₀ n (e i)
  let L := floorMeshSide L₀ n
  have hq : 0 < q := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ ↦ ⟨0, by omega⟩⟩
  have hsum : (∑ i, L ^ (d - 1) * floorCubeWeightInf σ b (a i) L ^ p) =
      floorMeshLowerSum σ p b a₀ L₀ n := by
    exact e.sum_comp (fun k ↦ floorMeshSide L₀ n ^ (d - 1) *
      floorCubeWeightInf σ b (floorMeshOrigin a₀ L₀ n k) (floorMeshSide L₀ n) ^ p)
  refine ⟨q, hq, a, L, floorMeshSide_pos hL₀ n, ?_, ?_, ?_⟩
  · intro i j hij
    exact floorMeshCube_pairwise_disjoint b a₀ hL₀ n (e.injective.ne hij)
  · rw [hsum]
    exact (floorMeshLowerSum_le_integral σ hp b a₀ hL₀ n).trans
      (setIntegral_le_integral (weightedFloorDensity_rpow_integrable σ hp)
        (Eventually.of_forall (fun u ↦ Real.rpow_nonneg (weightedFloorDensity_pos σ u).le p)))
  · rw [hsum]
    change I - η < _
    change I - η / 2 < ∫ u in orthonormalFloorCube b a₀ L₀, weightedFloorDensity σ u ^ p at hR
    linarith

end Antichain
