import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Elementary exact identities used in Sections 1 and 3 of the paper.
The Gaussian distribution and its quantile function are not constructed here.
-/

namespace Antichain

/-- The paper's strict order: every coordinate is strictly smaller. -/
def StrictBelow {ι : Type*} (x y : ι → ℝ) : Prop := ∀ i, x i < y i

/-- A labelled family has no strictly coordinatewise comparable distinct pair. -/
def IsAntichain {κ ι : Type*} (x : κ → ι → ℝ) : Prop :=
  ∀ j k, j ≠ k → ¬ StrictBelow (x j) (x k)

/-- Any strictly increasing coordinate change preserves and reflects the strict order. -/
theorem strictBelow_coordinatewise_iff {ι : Type*} {Q : ℝ → ℝ}
    (hQ : StrictMono Q) (x y : ι → ℝ) :
    StrictBelow (fun i ↦ Q (x i)) (fun i ↦ Q (y i)) ↔ StrictBelow x y := by
  simp only [StrictBelow, hQ.lt_iff_lt]

/-- In particular, an increasing quantile change preserves the antichain event,
once strict monotonicity on the relevant domain is supplied. -/
theorem isAntichain_coordinatewise_iff {κ ι : Type*} {Q : ℝ → ℝ}
    (hQ : StrictMono Q) (x : κ → ι → ℝ) :
    IsAntichain (fun j i ↦ Q (x j i)) ↔ IsAntichain x := by
  simp only [IsAntichain, strictBelow_coordinatewise_iff hQ]

/-- The domain-restricted version suitable for a quantile on the open unit interval. -/
theorem strictBelow_coordinatewise_iff_on {ι : Type*} {Q : ℝ → ℝ} {S : Set ℝ}
    (hQ : StrictMonoOn Q S) (x y : ι → ℝ) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) :
    StrictBelow (fun i ↦ Q (x i)) (fun i ↦ Q (y i)) ↔ StrictBelow x y := by
  constructor
  · intro h i
    exact (hQ.lt_iff_lt (hx i) (hy i)).mp (h i)
  · intro h i
    exact (hQ.lt_iff_lt (hx i) (hy i)).mpr (h i)

theorem isAntichain_coordinatewise_iff_on {κ ι : Type*} {Q : ℝ → ℝ} {S : Set ℝ}
    (hQ : StrictMonoOn Q S) (x : κ → ι → ℝ) (hx : ∀ j i, x j i ∈ S) :
    IsAntichain (fun j i ↦ Q (x j i)) ↔ IsAntichain x := by
  unfold IsAntichain
  simp only [strictBelow_coordinatewise_iff_on hQ _ _ (hx _) (hx _)]

/-- Translating a configuration leaves every strict coordinate comparison unchanged. -/
theorem strictBelow_translate_iff {ι : Type*} (x y m : ι → ℝ) :
    StrictBelow (fun i ↦ m i + x i) (fun i ↦ m i + y i) ↔ StrictBelow x y := by
  simp only [StrictBelow, add_lt_add_iff_left]

theorem isAntichain_translate_iff {κ ι : Type*} (x : κ → ι → ℝ) (m : ι → ℝ) :
    IsAntichain (fun j i ↦ m i + x j i) ↔ IsAntichain x := by
  simp only [IsAntichain, strictBelow_translate_iff]

/-- The scalar centering identity, including its exact cross-term cancellation. -/
theorem sum_sq_add_of_sum_zero {κ : Type*} [Fintype κ]
    (u : κ → ℝ) (m : ℝ) (hu : ∑ j, u j = 0) :
    (∑ j, (m + u j) ^ 2) = (Fintype.card κ : ℝ) * m ^ 2 + ∑ j, (u j) ^ 2 := by
  calc
    (∑ j, (m + u j) ^ 2) = ∑ j, (m ^ 2 + 2 * m * u j + (u j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (Fintype.card κ : ℝ) * m ^ 2 + 2 * m * (∑ j, u j) + ∑ j, (u j) ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ = _ := by rw [hu]; ring

/-- Euclidean sum-of-coordinate-squares form of the Gaussian energy split.
This avoids introducing a normed-space representation for a finite coordinate array. -/
theorem gaussian_energy_split {κ ι : Type*} [Fintype κ] [Fintype ι]
    (u : κ → ι → ℝ) (m : ι → ℝ) (hu : ∀ i, ∑ j, u j i = 0) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, (m i + u j i) ^ 2) =
      (Fintype.card κ : ℝ) / 2 * (∑ i, (m i) ^ 2) +
        (1 / 2 : ℝ) * (∑ j, ∑ i, (u j i) ^ 2) := by
  have h : (∑ j, ∑ i, (m i + u j i) ^ 2) =
      (Fintype.card κ : ℝ) * (∑ i, (m i) ^ 2) + ∑ j, ∑ i, (u j i) ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [sum_sq_add_of_sum_zero (fun j ↦ u j _) _ (hu _)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  rw [h]
  ring

/-- Subtracting the actual average produces a centered configuration. -/
theorem sum_sub_mean_eq_zero {κ : Type*} [Fintype κ] [Nonempty κ]
    (s : κ → ℝ) :
    (∑ j, (s j - (∑ k, s k) / (Fintype.card κ : ℝ))) = 0 := by
  have hc : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- The energy identity with the barycenter constructed from the input points. -/
theorem gaussian_energy_barycenter {κ ι : Type*}
    [Fintype κ] [Nonempty κ] [Fintype ι] (s : κ → ι → ℝ) :
    let m : ι → ℝ := fun i ↦ (∑ j, s j i) / (Fintype.card κ : ℝ)
    (1 / 2 : ℝ) * (∑ j, ∑ i, (s j i) ^ 2) =
      (Fintype.card κ : ℝ) / 2 * (∑ i, (m i) ^ 2) +
        (1 / 2 : ℝ) * (∑ j, ∑ i, (s j i - m i) ^ 2) := by
  intro m
  have h := gaussian_energy_split (fun j i ↦ s j i - m i) m
    (fun i ↦ sum_sub_mean_eq_zero (fun j ↦ s j i))
  simpa only [add_sub_cancel] using h

end Antichain
