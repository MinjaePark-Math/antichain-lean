import Antichain.RankBoxes
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! The genuine iid sampler of the literal rank-box permuton: independent
uniform source labels, with independent uniform points inside their boxes. -/

noncomputable section

namespace Antichain

open MeasureTheory Set
open scoped ENNReal

def rankBoxLabelPointSampler (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n))
    (z : Fin n × CubePoint d) : CubePoint d := rankBoxPoint n d r z.1 z.2

theorem rankBoxLabelPointSampler_measurable (n d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) :
    Measurable (rankBoxLabelPointSampler n d r) :=
  measurable_from_prod_countable_right fun j => (rankBoxPoint_continuous n d r j).measurable

theorem rankBoxLabelPointSampler_law (n d : ℕ) [NeZero n]
    (r : Fin d → Equiv.Perm (Fin n)) :
    (((PMF.uniformOfFintype (Fin n)).toMeasure).prod (cubePointLaw d)).map
      (rankBoxLabelPointSampler n d r) = rankBoxMeasure n d r := by
  classical
  ext A hA
  rw [Measure.map_apply (rankBoxLabelPointSampler_measurable n d r) hA,
    Measure.prod_apply (hA.preimage (rankBoxLabelPointSampler_measurable n d r)),
    lintegral_fintype, rankBoxMeasure, if_neg (NeZero.ne n),
    Measure.smul_apply, Measure.sum_apply _ hA]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_fin, smul_eq_mul, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 1
  exact (Measure.map_apply (rankBoxPoint_continuous n d r j).measurable hA).symm

def rankBoxSampleMap (n q d : ℕ) (r : Fin d → Equiv.Perm (Fin n))
    (z : (Fin q → Fin n) × CubeSample q d) : CubeSample q d :=
  fun j => rankBoxPoint n d r (z.1 j) (z.2 j)

theorem rankBoxSampleMap_measurable (n q d : ℕ) (r : Fin d → Equiv.Perm (Fin n)) :
    Measurable (rankBoxSampleMap n q d r) := by
  apply measurable_from_prod_countable_right
  intro f
  apply measurable_pi_lambda
  intro j
  exact (rankBoxPoint_continuous n d r (f j)).measurable.comp (measurable_pi_apply j)

/-- The actual product law, with no pattern/order assumption. -/
theorem rankBoxSampleMap_law (n q d : ℕ) [NeZero n]
    (r : Fin d → Equiv.Perm (Fin n)) :
    ((Measure.pi (fun _ : Fin q => (PMF.uniformOfFintype (Fin n)).toMeasure)).prod
      (cubeSampleLaw q d)).map (rankBoxSampleMap n q d r) =
      Measure.pi (fun _ : Fin q => rankBoxMeasure n d r) := by
  letI := rankBoxMeasure_isProbabilityMeasure n d r
  let μ : Measure (Fin n) := (PMF.uniformOfFintype (Fin n)).toMeasure
  let ν : Measure (CubePoint d) := cubePointLaw d
  have hs := (measurePreserving_arrowProdEquivProdArrow (Fin n) (CubePoint d) (Fin q)
    (fun _ => μ) (fun _ => ν)).symm
  have hp : MeasurePreserving (rankBoxLabelPointSampler n d r) (μ.prod ν)
      (rankBoxMeasure n d r) :=
    ⟨rankBoxLabelPointSampler_measurable n d r, rankBoxLabelPointSampler_law n d r⟩
  have hi := measurePreserving_pi (fun _ : Fin q => μ.prod ν)
    (fun _ : Fin q => rankBoxMeasure n d r) (fun _ => hp)
  exact (hi.comp hs).map_eq

end Antichain
