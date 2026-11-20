import Antichain.PinnedVolumeUpper
import Antichain.PinnedVolumeLower

/-!
The actual local entropy constant. Both geometric bounds are proved before
the real-valued limsup is introduced, ruling out an unbounded/junk limsup.
-/

noncomputable section

namespace Antichain

open Filter Set
open scoped Topology

/-- Complete boundedness conclusion of the paper's one-tile local-rate lemma. -/
theorem localGammaSequence_bounded {d : ℕ} (hd : 2 ≤ d) :
    BddAbove (Set.range (localGammaSequence d)) ∧
      BddBelow (Set.range (localGammaSequence d)) :=
  ⟨localGammaSequence_bddAbove hd, localGammaSequence_bddBelow hd⟩

theorem localGammaSequence_isBoundedUnder_le {d : ℕ} (hd : 2 ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (localGammaSequence d) :=
  (localGammaSequence_bddAbove hd).isBoundedUnder_of_range

theorem localGammaSequence_isBoundedUnder_ge {d : ℕ} (hd : 2 ≤ d) :
    IsBoundedUnder (· ≥ ·) atTop (localGammaSequence d) :=
  (localGammaSequence_bddBelow hd).isBoundedUnder_of_range

/-- The actual finite constant gamma_d, introduced only after the full
boundedness theorem and restricted to the paper's dimensions d >= 2. -/
def localGammaConstant (d : ℕ) (_hd : 2 ≤ d) : ℝ :=
  Filter.limsup (localGammaSequence d) atTop

theorem localGammaConstant_eq_limsup (d : ℕ) (hd : 2 ≤ d) :
    localGammaConstant d hd = Filter.limsup (localGammaSequence d) atTop := rfl

/-- Finite real lower and upper bounds control both the actual sequence and
its actual limsup, rather than merely asserting that a real expression exists. -/
theorem localGammaConstant_bounded (d : ℕ) (hd : 2 ≤ d) :
    ∃ L U : ℝ, (∀ r, L ≤ localGammaSequence d r ∧ localGammaSequence d r ≤ U) ∧
      L ≤ localGammaConstant d hd ∧ localGammaConstant d hd ≤ U := by
  obtain ⟨U, hU⟩ := localGammaSequence_bddAbove hd
  obtain ⟨L, hL⟩ := localGammaSequence_bddBelow hd
  refine ⟨L, U, (fun r => ⟨hL (mem_range_self r), hU (mem_range_self r)⟩), ?_, ?_⟩
  · apply Filter.le_limsup_of_le (localGammaSequence_isBoundedUnder_le hd)
    intro b hb
    obtain ⟨r, hr⟩ := hb.exists
    exact (hL (mem_range_self r)).trans hr
  · exact Filter.limsup_le_of_le
      (localGammaSequence_isBoundedUnder_ge hd).isCobounded_flip
      (Filter.Eventually.of_forall (fun r => hU (mem_range_self r)))

end Antichain
