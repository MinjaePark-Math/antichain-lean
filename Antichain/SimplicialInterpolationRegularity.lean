import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
import Antichain.SimplicialGridWeights

/-! Regularity of finite simplicial interpolation: finite extrema preserve a
common Lipschitz constant, and bounded hat sums are bounded Lipschitz maps. -/
noncomputable section
namespace Antichain
open Set Finset
open scoped NNReal BoundedContinuousFunction

theorem lipschitzWith_real_sub {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    LipschitzWith (K + L) (fun x => f x - g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heq : (f x - g x) - (f y - g y) = (f x - f y) - (g x - g y) := by ring
  rw [Real.dist_eq, heq]
  exact (abs_sub _ _).trans (by
    simpa only [NNReal.coe_add, add_mul] using
      add_le_add (hf.dist_le_mul x y) (hg.dist_le_mul x y))

theorem lipschitzWith_const_sub_coordinate {ι : Type*} [Fintype ι]
    (i : ι) (a : ℝ) : LipschitzWith 1 (fun z : ι → ℝ => a - z i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heq : a - x i - (a - y i) = -(x i - y i) := by ring
  rw [Real.dist_eq, heq, abs_neg, NNReal.coe_one, one_mul]
  exact dist_le_pi_dist x y i

theorem lipschitzWith_grid_scale {ι : Type*} [Fintype ι] (N : ℕ) :
    LipschitzWith (N : ℝ≥0) (fun z : ι → ℝ => fun i => (N : ℝ) * z i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ (N : ℝ≥0) * dist x y)).mpr
  intro i
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (Nat.cast_nonneg N)

theorem lipschitzWith_finset_sup' {X I : Type*} [PseudoMetricSpace X]
    (S : Finset I) (hS : S.Nonempty) (f : I → X → ℝ) {K : ℝ≥0}
    (hf : ∀ i ∈ S, LipschitzWith K (f i)) :
    LipschitzWith K (fun x => S.sup' hS (fun i => f i x)) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  apply Finset.sup'_le
  intro i hi
  exact ((hf i hi).le_add_mul x y).trans
    (add_le_add_right (Finset.le_sup' (fun i => f i y) hi) _)

theorem lipschitzWith_finset_inf' {X I : Type*} [PseudoMetricSpace X]
    (S : Finset I) (hS : S.Nonempty) (f : I → X → ℝ) {K : ℝ≥0}
    (hf : ∀ i ∈ S, LipschitzWith K (f i)) :
    LipschitzWith K (fun x => S.inf' hS (fun i => f i x)) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  rw [← sub_le_iff_le_add]
  apply Finset.le_inf'
  intro i hi
  rw [sub_le_iff_le_add]
  exact (Finset.inf'_le (fun i => f i x) hi).trans ((hf i hi).le_add_mul x y)

theorem lipschitzWith_weighted_fintype_sum {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (w : I → ℝ) (f : I → X → ℝ) (K : I → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i)) :
    LipschitzWith (∑ i, ‖w i‖₊ * K i) (fun x => ∑ i, w i * f i x) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ i, |w i * (f i x - f i y)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * ((K i : ℝ) * dist x y) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hf i).dist_le_mul x y) (abs_nonneg _)
    _ = _ := by
      simp only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      ring

theorem abs_weighted_hat_sum_le {X I : Type*} [Fintype I]
    (w : I → ℝ) (f : I → X → ℝ) (hf : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) (x : X) :
    |∑ i, w i * f i x| ≤ ∑ i, |w i| := by
  classical
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  rw [abs_mul, abs_of_nonneg (hf i x).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (hf i x).2

def weightedHatBCF {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (w : I → ℝ) (f : I → X → ℝ) (K : I → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (hb : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => ∑ i, w i * f i x, (lipschitzWith_weighted_fintype_sum w f K hf).continuous⟩
    (2 * ∑ i, |w i|) (fun x y => by
      rw [Real.dist_eq]
      apply (abs_sub _ _).trans
      change |∑ i, w i * f i x| + |∑ i, w i * f i y| ≤ 2 * ∑ i, |w i|
      linarith [abs_weighted_hat_sum_le w f hb x, abs_weighted_hat_sum_le w f hb y])

@[simp] theorem weightedHatBCF_apply {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (w : I → ℝ) (f : I → X → ℝ) (K : I → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (hb : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) (x : X) :
    weightedHatBCF w f K hf hb x = ∑ i, w i * f i x := rfl

variable {ι : Type*} [Fintype ι] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

theorem simplicialRoundingLower_lipschitz {N : ℕ} (v : SimplicialGridVertex ι N) :
    LipschitzWith 1 (fun z : ι → ℝ => simplicialRoundingLower z v) := by
  classical
  have H : LipschitzWith 1 (fun z : ι → ℝ =>
      (univ : Finset ι).sup' univ_nonempty (fun i => (v i : ℝ) - z i)) :=
    lipschitzWith_finset_sup' (X := ι → ℝ) (I := ι) (K := 1) univ univ_nonempty
    (fun (i : ι) (z : ι → ℝ) => (v i : ℝ) - z i)
    (fun i _ => lipschitzWith_const_sub_coordinate (ι := ι) i (v i))
  exact H.const_max 0

theorem simplicialRoundingUpper_lipschitz {N : ℕ} (v : SimplicialGridVertex ι N) :
    LipschitzWith 1 (fun z : ι → ℝ => simplicialRoundingUpper z v) := by
  classical
  have H : LipschitzWith 1 (fun z : ι → ℝ =>
      (univ : Finset ι).inf' univ_nonempty (fun i => (v i : ℝ) + 1 - z i)) :=
    lipschitzWith_finset_inf' (X := ι → ℝ) (I := ι) (K := 1) univ univ_nonempty
    (fun (i : ι) (z : ι → ℝ) => (v i : ℝ) + 1 - z i)
    (fun i _ => lipschitzWith_const_sub_coordinate (ι := ι) i ((v i : ℝ) + 1))
  exact H.const_min 1

theorem simplicialGridHat_lipschitz {N : ℕ} (v : SimplicialGridVertex ι N) :
    LipschitzWith 2 (fun z : ι → ℝ => simplicialGridHat z v) := by
  have h := (lipschitzWith_real_sub (simplicialRoundingUpper_lipschitz v)
    (simplicialRoundingLower_lipschitz v)).const_max 0
  simpa only [simplicialGridHat, one_add_one_eq_two] using h

theorem scaledSimplicialGridHat_lipschitz (N : ℕ) (v : SimplicialGridVertex ι N) :
    LipschitzWith (2 * (N : ℝ≥0)) (fun x : ι → ℝ => scaledSimplicialGridHat N x v) :=
  (simplicialGridHat_lipschitz v).comp (lipschitzWith_grid_scale N)

def simplicialInterpolantBCF (N : ℕ) (g : (ι → ℝ) →ᵇ ℝ) : (ι → ℝ) →ᵇ ℝ := by
  classical
  exact weightedHatBCF (fun v : SimplicialGridVertex ι N => g (simplicialGridPoint v))
    (fun v x => scaledSimplicialGridHat N x v) (fun _ => 2 * (N : ℝ≥0))
    (scaledSimplicialGridHat_lipschitz N)
    (fun v x => ⟨simplicialGridHat_nonneg _ _, simplicialGridHat_le_one _ _⟩)

@[simp] theorem simplicialInterpolantBCF_apply (N : ℕ) (g : (ι → ℝ) →ᵇ ℝ)
    (x : ι → ℝ) : simplicialInterpolantBCF N g x =
      ∑ v : SimplicialGridVertex ι N, g (simplicialGridPoint v) * scaledSimplicialGridHat N x v := by
  classical
  rfl

theorem simplicialInterpolantBCF_lipschitz (N : ℕ) (g : (ι → ℝ) →ᵇ ℝ) :
    LipschitzWith
      (∑ v : SimplicialGridVertex ι N, ‖g (simplicialGridPoint v)‖₊ * (2 * (N : ℝ≥0)))
      (simplicialInterpolantBCF N g) := by
  classical
  exact lipschitzWith_weighted_fintype_sum
    (fun v : SimplicialGridVertex ι N => g (simplicialGridPoint v))
    (fun v x => scaledSimplicialGridHat N x v) (fun _ => 2 * (N : ℝ≥0))
    (scaledSimplicialGridHat_lipschitz N)

theorem simplicialInterpolantBCF_exists_lipschitz (N : ℕ) (g : (ι → ℝ) →ᵇ ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (simplicialInterpolantBCF N g) :=
  ⟨_, simplicialInterpolantBCF_lipschitz N g⟩

end Antichain
