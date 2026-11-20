import Antichain.CubeTestFloorError
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! The manuscript's Stone--Weierstrass Lipschitz-density step. -/
noncomputable section
namespace Antichain
open Set
open scoped Topology BoundedContinuousFunction NNReal

theorem compact_lipschitz_density_stoneWeierstrass
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : C(X, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g : C(X, ℝ), ∃ K : ℝ≥0, LipschitzWith K g ∧
      ∀ x, |f x - g x| < epsilon := by
  let L : Set C(X, ℝ) := {g | ∃ K : ℝ≥0, LipschitzWith K g}
  have h0 : L.Nonempty := ⟨0, 0, LipschitzWith.const 0⟩
  have hinf : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L := by
    intro f hf g hg
    obtain ⟨K, hK⟩ := hf
    obtain ⟨J, hJ⟩ := hg
    exact ⟨max K J, hK.min hJ⟩
  have hsup : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L := by
    intro f hf g hg
    obtain ⟨K, hK⟩ := hf
    obtain ⟨J, hJ⟩ := hg
    exact ⟨max K J, hK.max hJ⟩
  have hsep : L.SeparatesPointsStrongly := by
    intro v x y
    by_cases hxy : x = y
    · subst y
      exact ⟨ContinuousMap.const X (v x), ⟨0, LipschitzWith.const _⟩, rfl, rfl⟩
    · let a : ℝ := (v y - v x) / dist x y
      let g : C(X, ℝ) := ⟨fun z => a * dist x z + v x, by fun_prop⟩
      have hLip : LipschitzWith ‖a‖₊ g := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        change |a * dist x z + v x - (a * dist x w + v x)| ≤ _
        rw [show a * dist x z + v x - (a * dist x w + v x) =
          a * (dist x z - dist x w) by ring, abs_mul]
        have h := (LipschitzWith.dist_right x).dist_le_mul z w
        simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
        simpa only [coe_nnnorm, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left h (abs_nonneg a)
      refine ⟨g, ⟨_, hLip⟩, ?_, ?_⟩
      · simp [g]
      · dsimp [g, a]
        rw [div_mul_cancel₀ _ (dist_ne_zero.mpr hxy)]
        ring
  have hclosure := ContinuousMap.sublattice_closure_eq_top L h0 hinf hsup hsep
  have hf : f ∈ closure L := by rw [hclosure]; trivial
  obtain ⟨g, hg, hnear⟩ := Metric.mem_closure_iff.mp hf epsilon hepsilon
  obtain ⟨K, hK⟩ := hg
  refine ⟨g, K, hK, ?_⟩
  intro x
  have h := (ContinuousMap.dist_apply_le_dist x).trans_lt hnear
  simpa only [Real.dist_eq] using h

/-- Stone--Weierstrass on the actual compact cube, extended to the ambient
space by the one-Lipschitz coordinate clamp. -/
theorem cube_lipschitz_approximation_stoneWeierstrass (d : ℕ)
    (g : CubePoint d →ᵇ ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ f : CubePoint d →ᵇ ℝ, ∃ K : ℝ≥0, LipschitzWith K f ∧
      ∀ x ∈ cubePointSet d, |g x - f x| < epsilon := by
  let C := {x : CubePoint d // x ∈ cubePointSet d}
  letI : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_cubePointSet (d := d))
  let gc : C(C, ℝ) := ⟨fun x => g x.val, g.continuous.comp continuous_subtype_val⟩
  obtain ⟨h, K, hK, happ⟩ := compact_lipschitz_density_stoneWeierstrass gc hepsilon
  let clamp : CubePoint d → C := fun x => ⟨fun i => max 0 (min 1 (x i)),
    fun i _ => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
  have hclamp : LipschitzWith 1 clamp := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (fun i : Fin d => max 0 (min 1 (x i)))
      (fun i : Fin d => max 0 (min 1 (y i))) ≤ (1 : ℝ≥0) * dist x y
    rw [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    simpa only [NNReal.coe_one, one_mul] using
      (((LipschitzWith.eval i).const_min 1).const_max 0).dist_le_mul x y
  let f : CubePoint d →ᵇ ℝ :=
    (BoundedContinuousFunction.mkOfCompact h).compContinuous ⟨clamp, hclamp.continuous⟩
  refine ⟨f, K, ?_, ?_⟩
  · simpa only [mul_one] using hK.comp hclamp
  · intro x hx
    have hfix : clamp x = (⟨x, hx⟩ : C) := by
      apply Subtype.ext
      funext i
      have hi := hx i (mem_univ i)
      simp only [clamp, min_eq_right hi.2, max_eq_right hi.1]
    change |g x - h (clamp x)| < epsilon
    rw [hfix]
    exact happ ⟨x, hx⟩

end Antichain
