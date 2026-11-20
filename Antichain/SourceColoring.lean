import Antichain.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Lean.Elab.Tactic.Omega

/-! Longest-chain coloring of the actual finite rank point set. -/

noncomputable section

namespace Antichain

open Finset Set

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ]

def PointChain (x : κ → ι → ℝ) (s : Finset κ) : Prop :=
  ∀ j ∈ s, ∀ k ∈ s, j ≠ k → StrictBelow (x j) (x k) ∨ StrictBelow (x k) (x j)

def PointChainEndsAt (x : κ → ι → ℝ) (s : Finset κ) (j : κ) : Prop :=
  PointChain x s ∧ j ∈ s ∧ ∀ a ∈ s, a = j ∨ StrictBelow (x a) (x j)

def endingPointChains (x : κ → ι → ℝ) (j : κ) : Finset (Finset κ) := by
  classical
  exact Finset.univ.powerset.filter (fun s ↦ PointChainEndsAt x s j)

def longestEndingChain (x : κ → ι → ℝ) (j : κ) : ℕ :=
  (endingPointChains x j).sup Finset.card

omit [DecidableEq κ] in
theorem mem_endingPointChains (x : κ → ι → ℝ) (j : κ) (s : Finset κ) :
    s ∈ endingPointChains x j ↔ PointChainEndsAt x s j := by
  classical
  simp [endingPointChains]

omit [Fintype κ] [DecidableEq κ] in
theorem singleton_pointChainEndsAt (x : κ → ι → ℝ) (j : κ) :
    PointChainEndsAt x {j} j := by
  classical
  refine ⟨?_, by simp, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    exact False.elim (hab (ha.trans hb.symm))
  · intro a ha
    exact Or.inl (Finset.mem_singleton.mp ha)

omit [DecidableEq κ] in
theorem longestEndingChain_pos (x : κ → ι → ℝ) (j : κ) :
    0 < longestEndingChain x j := by
  have h := Finset.le_sup (s := endingPointChains x j) (f := Finset.card)
    ((mem_endingPointChains x j {j}).mpr (singleton_pointChainEndsAt x j))
  simpa only [Finset.card_singleton] using (show 0 < 1 by decide).trans_le h

omit [DecidableEq κ] in
theorem longestEndingChain_attained (x : κ → ι → ℝ) (j : κ) :
    ∃ s, PointChainEndsAt x s j ∧ s.card = longestEndingChain x j := by
  have hne : (endingPointChains x j).Nonempty :=
    ⟨{j}, (mem_endingPointChains x j {j}).mpr (singleton_pointChainEndsAt x j)⟩
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup (endingPointChains x j) hne Finset.card
  exact ⟨s, (mem_endingPointChains x j s).mp hs, heq.symm⟩

omit [Fintype κ] [DecidableEq κ] in
theorem pointChain_subset (x : κ → ι → ℝ) {s t : Finset κ}
    (h : PointChain x s) (ht : t ⊆ s) : PointChain x t := by
  exact fun a ha b hb hab ↦ h a (ht ha) b (ht hb) hab

variable [Nonempty ι]

theorem strictBelow_irrefl_source (u : ι → ℝ) : ¬ StrictBelow u u := by
  intro h
  exact lt_irrefl _ (h (Classical.choice ‹Nonempty ι›))

omit [Nonempty ι] in
theorem strictBelow_trans_source {u v w : ι → ℝ} (huv : StrictBelow u v)
    (hvw : StrictBelow v w) : StrictBelow u w := fun i ↦ (huv i).trans (hvw i)

omit [Fintype κ] in
theorem pointChainEndsAt_insert (x : κ → ι → ℝ) {s : Finset κ} {j k : κ}
    (hs : PointChainEndsAt x s j) (hjk : StrictBelow (x j) (x k)) :
    PointChainEndsAt x (insert k s) k ∧ k ∉ s := by
  classical
  have hbefore (a : κ) (ha : a ∈ s) : StrictBelow (x a) (x k) := by
    rcases hs.2.2 a ha with rfl | haj
    · exact hjk
    · exact strictBelow_trans_source haj hjk
  have hk : k ∉ s := fun h ↦ strictBelow_irrefl_source _ (hbefore k h)
  refine ⟨⟨?_, by simp, ?_⟩, hk⟩
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hak | has
    · subst a
      rcases Finset.mem_insert.mp hb with hbk | hbs
      · exact False.elim (hab hbk.symm)
      · exact Or.inr (hbefore b hbs)
    · rcases Finset.mem_insert.mp hb with hbk | hbs
      · subst b
        exact Or.inl (hbefore a has)
      · exact hs.1 a has b hbs hab
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr (hbefore a ha)

theorem longestEndingChain_strict_mono (x : κ → ι → ℝ) {j k : κ}
    (hjk : StrictBelow (x j) (x k)) : longestEndingChain x j < longestEndingChain x k := by
  obtain ⟨s, hs, hcard⟩ := longestEndingChain_attained x j
  obtain ⟨hext, hk⟩ := pointChainEndsAt_insert x hs hjk
  have h := Finset.le_sup (s := endingPointChains x k) (f := Finset.card)
    ((mem_endingPointChains x k (insert k s)).mpr hext)
  rw [Finset.card_insert_of_notMem hk, hcard] at h
  exact h

omit [Nonempty ι] [DecidableEq κ] in
theorem longestEndingChain_le_of_no_chain (x : κ → ι → ℝ) (K : ℕ)
    (hK : ¬ ∃ s : Finset κ, s.card = K + 1 ∧ PointChain x s) (j : κ) :
    longestEndingChain x j ≤ K := by
  obtain ⟨s, hs, hcard⟩ := longestEndingChain_attained x j
  by_contra hnot
  have hle : K + 1 ≤ s.card := by omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hle
  exact hK ⟨t, htcard, pointChain_subset x hs.1 hts⟩

/-- The color is exactly longest-chain-ending length minus one, encoded in `Fin K`. -/
theorem longest_chain_antichain_coloring (x : κ → ι → ℝ) (K : ℕ)
    (hK : ¬ ∃ s : Finset κ, s.card = K + 1 ∧ PointChain x s) :
    ∃ color : κ → Fin K,
      (∀ j, (color j).val + 1 = longestEndingChain x j) ∧
      ∀ j k, j ≠ k → color j = color k → ¬ StrictBelow (x j) (x k) := by
  let color : κ → Fin K := fun j ↦ ⟨longestEndingChain x j - 1, by
    have hpos := longestEndingChain_pos x j
    have hle := longestEndingChain_le_of_no_chain x K hK j
    omega⟩
  refine ⟨color, ?_, ?_⟩
  · intro j
    dsimp [color]
    have hpos := longestEndingChain_pos x j
    omega
  · intro j k _ hcolor hcomp
    have hval := congrArg Fin.val hcolor
    have hjpos := longestEndingChain_pos x j
    have hkpos := longestEndingChain_pos x k
    have hlt := longestEndingChain_strict_mono x hcomp
    dsimp [color] at hval
    omega

def finiteRankCoordinates (n m : ℕ) (pi : Fin m → Equiv.Perm (Fin n)) :
    Fin n → Fin (m + 1) → ℝ :=
  fun j i ↦ (((Fin.cons (Equiv.refl (Fin n)) pi : Fin (m + 1) → Equiv.Perm (Fin n)) i) j).val

theorem finiteRankCoordinates_strictBelow_iff {n m : ℕ}
    (pi : Fin m → Equiv.Perm (Fin n)) (j k : Fin n) :
    StrictBelow (finiteRankCoordinates n m pi j) (finiteRankCoordinates n m pi k) ↔
      j < k ∧ ∀ i, pi i j < pi i k := by
  constructor
  · intro h
    refine ⟨?_, fun i ↦ ?_⟩
    · have h0 := h 0
      change (j.val : ℝ) < k.val at h0
      exact_mod_cast h0
    · have hi := h i.succ
      change ((pi i j).val : ℝ) < (pi i k).val at hi
      exact_mod_cast hi
  · rintro ⟨hjk, hp⟩ i
    refine Fin.cases ?_ (fun l ↦ ?_) i
    · change (j.val : ℝ) < k.val
      exact_mod_cast hjk
    · change ((pi l j).val : ℝ) < (pi l k).val
      exact_mod_cast hp l

def ContainsIncreasingRankPattern {n m : ℕ}
    (pi : Fin m → Equiv.Perm (Fin n)) (q : ℕ) : Prop :=
  ∃ e : Fin q ↪o Fin n, ∀ i : Fin m, StrictMono (fun r ↦ pi i (e r))

theorem increasing_rank_pattern_iff_chain {n m q : ℕ}
    (pi : Fin m → Equiv.Perm (Fin n)) :
    ContainsIncreasingRankPattern pi q ↔
      ∃ s : Finset (Fin n), s.card = q ∧ PointChain (finiteRankCoordinates n m pi) s := by
  classical
  constructor
  · rintro ⟨e, he⟩
    refine ⟨Finset.univ.map e.toEmbedding, by simp, ?_⟩
    intro a ha b hb hab
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨s, _, rfl⟩ := Finset.mem_map.mp hb
    have hrs : r ≠ s := fun h ↦ hab (h ▸ rfl)
    rcases lt_or_gt_of_ne hrs with hlt | hgt
    · exact Or.inl ((finiteRankCoordinates_strictBelow_iff pi _ _).mpr
        ⟨e.strictMono hlt, fun i ↦ he i hlt⟩)
    · exact Or.inr ((finiteRankCoordinates_strictBelow_iff pi _ _).mpr
        ⟨e.strictMono hgt, fun i ↦ he i hgt⟩)
  · rintro ⟨s, hcard, hs⟩
    let e : Fin q ↪o Fin n := s.orderEmbOfFin hcard
    refine ⟨e, ?_⟩
    intro i a b hab
    have hea : e a ∈ s := s.orderEmbOfFin_mem hcard a
    have heb : e b ∈ s := s.orderEmbOfFin_mem hcard b
    have heab := e.strictMono hab
    rcases hs (e a) hea (e b) heb heab.ne with hc | hc
    · exact ((finiteRankCoordinates_strictBelow_iff pi _ _).mp hc).2 i
    · have hrev := ((finiteRankCoordinates_strictBelow_iff pi _ _).mp hc).1
      exact False.elim (lt_asymm heab hrev)

/-- The finite combinatorial statement before the bounded-chain conjecture.
The conjectural counting and limiting-measure conclusions are not assumed or claimed. -/
theorem bounded_chain_coloring_source {n m K : ℕ}
    (pi : Fin m → Equiv.Perm (Fin n))
    (hK : ¬ ContainsIncreasingRankPattern pi (K + 1)) :
    (¬ ∃ s : Finset (Fin n), s.card = K + 1 ∧ PointChain (finiteRankCoordinates n m pi) s) ∧
      ∃ color : Fin n → Fin K,
        (∀ j, (color j).val + 1 = longestEndingChain (finiteRankCoordinates n m pi) j) ∧
        ∀ j k, j ≠ k → color j = color k →
          ¬ StrictBelow (finiteRankCoordinates n m pi j) (finiteRankCoordinates n m pi k) := by
  have hchain := mt (increasing_rank_pattern_iff_chain pi).mpr hK
  exact ⟨hchain, longest_chain_antichain_coloring _ K hchain⟩

end Antichain
