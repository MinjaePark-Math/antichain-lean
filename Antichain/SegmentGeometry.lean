import Antichain.AlcoveTiling
import Antichain.BoundaryMatching

/-! Exact affine segment geometry shared by both gluing proofs. -/

noncomputable section

namespace Antichain

open Set Filter Metric
open scoped Topology Pointwise

variable {d : ℕ} [NeZero d]

def floorSegment (u v : FloorSpace (Fin d)) (t : ℝ) : FloorSpace (Fin d) :=
  (1 - t) • u + t • v

omit [NeZero d] in
theorem floorSegment_continuous (u v : FloorSpace (Fin d)) : Continuous (floorSegment u v) := by
  unfold floorSegment
  fun_prop

theorem floorSegment_directed_cost (u v : FloorSpace (Fin d)) (s t : ℝ) (hst : s ≤ t) :
    nativeFloorCost (floorSegment u v s) (floorSegment u v t) =
      (t - s) * nativeFloorCost u v := by
  have heq : (fun i => (floorSegment u v s).val i - (floorSegment u v t).val i) =
      (fun i => (t - s) * (u.val i - v.val i)) := by
    funext i
    simp only [floorSegment, Submodule.coe_add, Submodule.coe_smul, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  unfold nativeFloorCost
  rw [heq, heightGauge_smul _ _ (sub_nonneg.mpr hst)]

end Antichain
