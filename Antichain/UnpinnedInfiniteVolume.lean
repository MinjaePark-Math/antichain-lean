import Antichain.BoundaryMatching
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The infinite unpinned volume stated before the pinned-volume definition. -/

noncomputable section

namespace Antichain

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {d : ℕ} [NeZero d]

theorem floor_sample_injective_ae (hd : 2 ≤ d) (n : ℕ) :
    ∀ᵐ f : Fin n → FloorSpace (Fin d) ∂volume, Function.Injective f := by
  classical
  letI : SecondCountableTopology (FloorSpace (Fin d)) := inferInstance
  letI : BorelSpace (FloorSpace (Fin d)) := inferInstance
  haveI : Nontrivial (FloorSpace (Fin d)) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by rw [finrank_floorSpace, Fintype.card_fin]; omega)
  have hp (j k : Fin n) (hjk : j ≠ k) :
      ∀ᵐ f : Fin n → FloorSpace (Fin d) ∂volume, f j ≠ f k := by
    let L : (Fin n → FloorSpace (Fin d)) →ₗ[ℝ] FloorSpace (Fin d) :=
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => FloorSpace (Fin d)) j) -
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => FloorSpace (Fin d)) k)
    have hker : LinearMap.ker L ≠ ⊤ := by
      obtain ⟨u, hu⟩ := exists_ne (0 : FloorSpace (Fin d))
      intro heq
      have hmem : Pi.single j u ∈ LinearMap.ker L := by rw [heq]; trivial
      have hh : u = 0 := by simpa [L, LinearMap.mem_ker, hjk.symm] using hmem
      exact hu hh
    have hz := Measure.addHaar_submodule (volume : Measure (Fin n → FloorSpace (Fin d)))
      (LinearMap.ker L) hker
    rw [ae_iff]
    have heq : (LinearMap.ker L : Set (Fin n → FloorSpace (Fin d))) = {f | f j = f k} := by
      ext f
      change f j - f k = 0 ↔ f j = f k
      exact sub_eq_zero
    simpa only [not_not, heq] using hz
  have hall := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k =>
    ae_all_iff.mpr (fun hjk : j ≠ k => hp j k hjk)))
  filter_upwards [hall] with f hf
  intro j k heq
  by_contra hjk
  exact hf j k hjk heq

theorem pinnedHeightFiber_pos_of_injective (hd : 2 ≤ d) (r : ℕ)
    (f : Fin (r + 1) → FloorSpace (Fin d)) (hf : Function.Injective f) :
    0 < (volume : Measure (Fin r → ℝ)) (pinnedHeightFiber f) := by
  classical
  let G : Set (Fin r → ℝ) := {h | ∀ j k : Fin (r + 1), j ≠ k →
    (Fin.cons (0 : ℝ) h : Fin (r + 1) → ℝ) j -
      (Fin.cons (0 : ℝ) h : Fin (r + 1) → ℝ) k < nativeFloorCost (f j) (f k)}
  have hG : IsOpen G := by
    simp only [G, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro hjk
    apply isOpen_lt _ continuous_const
    have hc : Continuous (fun h : Fin r → ℝ => (f, h) : (Fin r → ℝ) → PinnedConfiguration (Fin d) r) :=
      continuous_const.prodMk continuous_id
    exact ((continuous_pinnedHeights_apply (ι := Fin d) j).comp hc).sub
      ((continuous_pinnedHeights_apply (ι := Fin d) k).comp hc)
  have hzero : (0 : Fin r → ℝ) ∈ G := by
    intro j k hjk
    have hcost := norm_div_sqrt_le_nativeFloorCost hd (f j) (f k)
    have hpos : 0 < ‖f j - f k‖ / Real.sqrt ((d : ℝ) - 1) := by
      apply div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hjk (hf h))))
      apply Real.sqrt_pos.mpr
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hz : (Fin.cons (0 : ℝ) (0 : Fin r → ℝ) : Fin (r + 1) → ℝ) = 0 := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    change (Fin.cons (0 : ℝ) (0 : Fin r → ℝ) : Fin (r + 1) → ℝ) j -
      (Fin.cons (0 : ℝ) (0 : Fin r → ℝ) : Fin (r + 1) → ℝ) k < _
    simpa only [hz, Pi.zero_apply, sub_zero] using hpos.trans_le hcost
  have hsub : G ⊆ pinnedHeightFiber f := by
    intro h hh
    have hbridge : h ∈ pinnedHeightFiber f ↔ (f, Fin.cons 0 h) ∈ flooredAntichainEvent (r + 1) d := by
      change IsAntichain (pinnedPointCloud (f, h)) ↔
        IsAntichain (flooredPointCloud (r + 1) (f, Fin.cons 0 h))
      have heq : pinnedPointCloud (f, h) = flooredPointCloud (r + 1) (f, Fin.cons 0 h) := by
        funext j i
        simp only [pinnedPointCloud, pinnedHeights, flooredPointCloud, Fintype.card_fin]
      rw [heq]
    apply hbridge.mpr
    apply (flooredAntichainEvent_iff_native_constraints (r + 1) (f, Fin.cons 0 h)).mpr
    intro j k
    by_cases hjk : j = k
    · subst k
      simp only [sub_self]
      exact nativeFloorCost_nonneg _ _
    · exact (hh j k hjk).le
  exact (hG.measure_pos volume ⟨0, hzero⟩).trans_le (measure_mono hsub)

theorem antichainHeightFiber_infinite_of_injective (hd : 2 ≤ d) (r : ℕ)
    (f : Fin (r + 1) → FloorSpace (Fin d)) (hf : Function.Injective f) :
    (volume : Measure (Fin (r + 1) → ℝ)) (antichainHeightFiber f) = ∞ := by
  have h := antichainHeightFiber_lintegral f (fun _ => 1) measurable_const
  have hp := pinnedHeightFiber_pos_of_injective hd r f hf
  simpa only [lintegral_one, lintegral_const, Real.volume_univ, Measure.restrict_apply_univ,
    ENNReal.top_mul hp.ne'] using h

/-- Literal unpinned configurations with r+1 positive sample count. -/
def unpinnedAntichainSet (B : Set (FloorSpace (Fin d))) (r : ℕ) :
    Set ((Fin (r + 1) → FloorSpace (Fin d)) × (Fin (r + 1) → ℝ)) :=
  {p | (∀ j, p.1 j ∈ B) ∧ IsAntichain (fullHeightPointCloud p.1 p.2)}

theorem unpinned_antichain_volume_infinite_source (hd : 2 ≤ d)
    {B : Set (FloorSpace (Fin d))} (hB : MeasurableSet B) (hBpos : 0 < volume B)
    (r : ℕ) : volume (unpinnedAntichainSet B r) = ∞ := by
  have hm : MeasurableSet (unpinnedAntichainSet B r) := by
    change MeasurableSet ({p : (Fin (r + 1) → FloorSpace (Fin d)) × (Fin (r + 1) → ℝ) |
      ∀ j, p.1 j ∈ B} ∩ {p | IsAntichain (fullHeightPointCloud p.1 p.2)})
    apply MeasurableSet.inter
    · simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun j => hB.preimage
        ((measurable_pi_apply j).comp measurable_fst)
    · apply measurableSet_isAntichain (fun p :
        (Fin (r + 1) → FloorSpace (Fin d)) × (Fin (r + 1) → ℝ) => fullHeightPointCloud p.1 p.2)
      intro j i
      unfold fullHeightPointCloud
      have hc : Continuous (fun p : (Fin (r + 1) → FloorSpace (Fin d)) × (Fin (r + 1) → ℝ) =>
          (p.1 j).val i) := (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp
        (continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst))
      exact (hc.add (((continuous_apply j).comp continuous_snd).div_const _)).measurable
  let D : Set (Fin (r + 1) → FloorSpace (Fin d)) := univ.pi (fun _ => B)
  have hD : MeasurableSet D := MeasurableSet.univ_pi fun _ => hB
  have hmass : 0 < (volume : Measure (Fin (r + 1) → FloorSpace (Fin d))) D := by
    change 0 < (Measure.pi (fun _ : Fin (r + 1) => (volume : Measure (FloorSpace (Fin d)))))
      (univ.pi (fun _ => B))
    rw [Measure.pi_pi]
    exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => hBpos.ne')
  change ((volume : Measure (Fin (r + 1) → FloorSpace (Fin d))).prod
    (volume : Measure (Fin (r + 1) → ℝ))) (unpinnedAntichainSet B r) = ∞
  rw [Measure.prod_apply hm]
  have heq : (fun f : Fin (r + 1) → FloorSpace (Fin d) =>
      (volume : Measure (Fin (r + 1) → ℝ)) (Prod.mk f ⁻¹' unpinnedAntichainSet B r)) =
      D.indicator (fun f => (volume : Measure (Fin (r + 1) → ℝ)) (antichainHeightFiber f)) := by
    funext f
    by_cases hf : f ∈ D
    · rw [Set.indicator_of_mem hf]
      congr 1
      ext h
      simpa only [unpinnedAntichainSet, antichainHeightFiber, mem_setOf_eq,
        mem_preimage, D, mem_univ_pi] using and_iff_right hf
    · rw [Set.indicator_of_notMem hf]
      have he : Prod.mk f ⁻¹' unpinnedAntichainSet B r = ∅ := by
        ext h
        simp only [mem_preimage, unpinnedAntichainSet, mem_setOf_eq,
          mem_empty_iff_false, iff_false, not_and]
        exact fun hb _ => hf (by simpa only [D, mem_univ_pi] using hb)
      rw [he, measure_empty]
  rw [heq, lintegral_indicator hD]
  have hae : ∀ᵐ f : Fin (r + 1) → FloorSpace (Fin d) ∂volume.restrict D,
      (volume : Measure (Fin (r + 1) → ℝ)) (antichainHeightFiber f) = ∞ :=
    (ae_restrict_of_ae (floor_sample_injective_ae hd (r + 1))).mono
      fun f hf => antichainHeightFiber_infinite_of_injective hd r f hf
  rw [lintegral_congr_ae hae, lintegral_const, Measure.restrict_apply_univ,
    ENNReal.top_mul hmass.ne']

end Antichain
