import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Passing a uniform, summable majorant through countably many upper rates. -/

namespace Antichain

open Filter Finset
open scoped Topology

/-- A finite-head/summable-tail proof of the countable upper-rate step. The
index filter is arbitrary; no unjustified interchange of infinite limsups occurs. -/
theorem eventually_tsum_le_of_summable_majorant
    {ι T : Type*} {L : Filter T} (F : T → ι → ℝ) (g : ι → ℝ) {C K : ℝ}
    (hg : Summable g) (hg0 : ∀ i, 0 ≤ g i) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF0 : ∀ t i, 0 ≤ F t i) (hF : ∀ t i, F t i ≤ C * g i)
    (hrate : ∀ i, ∀ e : ℝ, 0 < e → ∀ᶠ t in L, F t i ≤ K * g i + e)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in L, (∑' i, F t i) ≤ K * (∑' i, g i) + δ := by
  classical
  have hsum : ∀ t, Summable (F t) := fun t =>
    Summable.of_nonneg_of_le (hF0 t) (hF t) (hg.mul_left C)
  let e : ℝ := δ / (2 * (C + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have hev : ∀ᶠ s : Finset ι in atTop, (∑' i, g i) - e < ∑ i ∈ s, g i :=
    hg.hasSum.eventually (Ioi_mem_nhds (sub_lt_self (∑' i, g i) he))
  obtain ⟨s, hs⟩ := hev.exists
  have htailg : (∑' i : {i // i ∉ s}, g i.val) < e := by
    have heq := hg.sum_add_tsum_subtype_compl s
    linarith
  let b : ℝ := δ / (2 * ((s.card : ℝ) + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  have hhead : ∀ᶠ t in L, ∀ i ∈ s, F t i ≤ K * g i + b :=
    (eventually_all_finset s).mpr (fun i _ => hrate i b hb)
  filter_upwards [hhead] with t ht
  have htails : (∑' i : {i // i ∉ s}, F t i.val) ≤
      C * (∑' i : {i // i ∉ s}, g i.val) := by
    have hgs : Summable (fun i : {i // i ∉ s} => g i.val) := hg.subtype {i | i ∉ s}
    rw [← hgs.tsum_mul_left C]
    exact ((hsum t).subtype {i | i ∉ s}).tsum_le_tsum
      (fun i => hF t i.val) ((hg.subtype {i | i ∉ s}).mul_left C)
  have hsumg : (∑ i ∈ s, g i) ≤ ∑' i, g i :=
    hg.sum_le_tsum s (fun i _ => hg0 i)
  have hbe : (s.card : ℝ) * b ≤ δ / 2 := by
    have hden : 0 < (s.card : ℝ) + 1 := by positivity
    have hratio : (s.card : ℝ) / (s.card + 1) ≤ 1 :=
      (div_le_one hden).mpr (by linarith)
    dsimp [b]
    calc
      _ = δ / 2 * ((s.card : ℝ) / (s.card + 1)) := by field_simp
      _ ≤ δ / 2 := mul_le_of_le_one_right (by positivity) hratio
  have hCe : C * e ≤ δ / 2 := by
    dsimp [e]
    have hden : 0 < C + 1 := by positivity
    have hratio : C / (C + 1) ≤ 1 := (div_le_one hden).mpr (by linarith)
    calc
      _ = δ / 2 * (C / (C + 1)) := by field_simp
      _ ≤ δ / 2 := mul_le_of_le_one_right (by positivity) hratio
  calc
    (∑' i, F t i) = (∑ i ∈ s, F t i) + ∑' i : {i // i ∉ s}, F t i.val :=
      ((hsum t).sum_add_tsum_subtype_compl s).symm
    _ ≤ (∑ i ∈ s, (K * g i + b)) + C * (∑' i : {i // i ∉ s}, g i.val) :=
      add_le_add (Finset.sum_le_sum ht) htails
    _ = K * (∑ i ∈ s, g i) + (s.card : ℝ) * b +
        C * (∑' i : {i // i ∉ s}, g i.val) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * (∑' i, g i) + δ := by
      have hh := mul_le_mul_of_nonneg_left hsumg hK
      have htail := mul_le_mul_of_nonneg_left htailg.le hC
      linarith

end Antichain
