import Antichain.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
Exact finite-order algebra behind the weak-Bruhat-interval application.
No probabilistic or asymptotic claims are made in this module.
-/

namespace Antichain

/-- Inversions of an injective real-valued ranking of a linearly ordered finite set. -/
def Inversions {α : Type*} [LinearOrder α] (π : α → ℝ) : Set (α × α) :=
  {p | p.1 < p.2 ∧ π p.2 < π p.1}

/-- The increasing pairs become exactly the inversions after reversing the values. -/
theorem inversion_reflect_iff {α : Type*} [LinearOrder α]
    (π : α → ℝ) (c : ℝ) (k l : α) :
    (k, l) ∈ Inversions (fun r ↦ c - π r) ↔ k < l ∧ π k < π l := by
  simp only [Inversions, Set.mem_setOf_eq]
  constructor <;> rintro ⟨hkl, hπ⟩ <;> exact ⟨hkl, by linarith⟩

/-- Avoiding the increasing three-dimensional two-point pattern is equivalent
to inclusion of the inversion sets of the reflected third and second rankings.
Injectivity discharges the possibility of tied ranks. -/
theorem avoidance_iff_inversion_inclusion {α : Type*} [LinearOrder α]
    (π₂ π₃ : α → ℝ) (h₂ : Function.Injective π₂) (c : ℝ) :
    (∀ k l, k < l → ¬ (π₂ k < π₂ l ∧ π₃ k < π₃ l)) ↔
      Inversions (fun r ↦ c - π₃ r) ⊆ Inversions π₂ := by
  constructor
  · intro h p hp
    obtain ⟨k, l⟩ := p
    obtain ⟨hkl, h₃⟩ := (inversion_reflect_iff π₃ c k l).mp hp
    have hne : π₂ k ≠ π₂ l := fun heq ↦ (ne_of_lt hkl) (h₂ heq)
    have hnot : ¬ π₂ k < π₂ l := fun h₂lt ↦ h k l hkl ⟨h₂lt, h₃⟩
    exact ⟨hkl, lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)⟩
  · intro h k l hkl hboth
    have hinv := h ((inversion_reflect_iff π₃ c k l).mpr ⟨hkl, hboth.2⟩)
    exact (not_lt_of_gt hinv.2) hboth.1

/-- Reflection is an involution, so the displayed interval map has the claimed inverse. -/
theorem reflect_reflect (c x : ℝ) : c - (c - x) = x := by ring

/-- The rank point cloud with its first ranking fixed to the identity. -/
def rankTriple {n : ℕ} (π₂ π₃ : Fin n → ℝ) : Fin n → Fin 3 → ℝ :=
  fun k ↦ ![(k.val : ℝ), π₂ k, π₃ k]

/-- The strict antichain definition is exactly the two-point pattern-avoidance
condition when the points are sorted by their first coordinate. -/
theorem rankTriple_antichain_iff_avoidance {n : ℕ} (π₂ π₃ : Fin n → ℝ) :
    IsAntichain (rankTriple π₂ π₃) ↔
      (∀ k l, k < l → ¬ (π₂ k < π₂ l ∧ π₃ k < π₃ l)) := by
  constructor
  · intro h k l hkl hboth
    apply h k l (ne_of_lt hkl)
    intro i
    fin_cases i
    · change (k.val : ℝ) < (l.val : ℝ)
      exact_mod_cast hkl
    · exact hboth.1
    · exact hboth.2
  · intro h j k _ hbelow
    have hzero := hbelow 0
    change (j.val : ℝ) < (k.val : ℝ) at hzero
    have hjk : j < k := by exact_mod_cast hzero
    exact h j k hjk ⟨hbelow 1, hbelow 2⟩

/-- The complete deterministic order equivalence used by the interval map. -/
theorem rankTriple_antichain_iff_interval {n : ℕ}
    (π₂ π₃ : Fin n → ℝ) (h₂ : Function.Injective π₂) (c : ℝ) :
    IsAntichain (rankTriple π₂ π₃) ↔
      Inversions (fun r ↦ c - π₃ r) ⊆ Inversions π₂ :=
  (rankTriple_antichain_iff_avoidance π₂ π₃).trans
    (avoidance_iff_inversion_inclusion π₂ π₃ h₂ c)

/-- The finite algebra used with Stirling's formula in the counting application.
The input remainders remain explicit; their little-o estimates are not assumed hidden. -/
theorem counting_remainder_identity (d n L β r s : ℝ)
    (hL : L = n * Real.log n - n + s) :
    (d - 1) * L + (-n / (d - 1) * Real.log n + β * n + r) -
      (d - 1 - 1 / (d - 1)) * L =
        n * (β - 1 / (d - 1)) + r + s / (d - 1) := by
  rw [hL]
  ring

end Antichain
