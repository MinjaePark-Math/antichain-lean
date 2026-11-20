import Mathlib.MeasureTheory.Constructions.Pi

/-! Genuine transposition of finite arrays of independent identically distributed marks. -/

namespace Antichain

open MeasureTheory Set

variable {I J E : Type*} [Fintype I] [Fintype J] [MeasurableSpace E]

theorem measurePreserving_iid_uncurry (mu : Measure E) [SigmaFinite mu] :
    MeasurePreserving (MeasurableEquiv.curry I J E).symm
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => mu)))
      (Measure.pi (fun _ : I × J => mu)) := by
  refine ⟨(MeasurableEquiv.curry I J E).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have hp : (MeasurableEquiv.curry I J E).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i => univ.pi (fun j => s (i, j))) := by
    ext f
    simp [Set.mem_pi, MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hp, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem measurePreserving_iid_transpose (mu : Measure E) [SigmaFinite mu] :
    MeasurePreserving (fun f : I → J → E => fun j i => f i j)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => mu)))
      (Measure.pi (fun _ : J => Measure.pi (fun _ : I => mu))) := by
  have h := (measurePreserving_iid_uncurry (I := J) (J := I) mu).symm.comp
    ((measurePreserving_piCongrLeft (fun _ : J × I => mu) (Equiv.prodComm I J)).comp
      (measurePreserving_iid_uncurry (I := I) (J := J) mu))
  convert h using 1

end Antichain
