import Antichain.PoissonRestrictions
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

/-! The literal order-preserving finite-configuration restriction is list
filtering. Nested spatial restrictions therefore compose by intersection. -/

noncomputable section

namespace Antichain

open Set Finset
open scoped Classical

variable {X : Type*}

def configurationList (z : FiniteConfiguration X) : List X := List.ofFn z.2

theorem configurationList_injective : Function.Injective (configurationList (X := X)) := by
  intro z w h
  exact List.equivSigmaTuple.symm.injective h

theorem configurationList_subsequence {n : ℕ} (S : Finset (Fin n)) (x : Fin n → X) :
    configurationList (configurationSubsequence S x) = (S.sort (· ≤ ·)).map x := by
  have horder : List.ofFn (fun j : Fin S.card => ((S.orderIsoOfFin rfl j : S) : Fin n)) =
      S.sort (· ≤ ·) := by
    simp only [Finset.coe_orderIsoOfFin_apply, List.ofFn_eq_map]
    exact Finset.listMap_orderEmbOfFin_finRange S rfl
  change List.ofFn (fun j => x (S.orderIsoOfFin rfl j)) = _
  calc
    _ = (List.ofFn (fun j : Fin S.card => ((S.orderIsoOfFin rfl j : S) : Fin n))).map x := by
      simpa only [Function.comp_def] using
        (List.map_ofFn (fun j : Fin S.card => ((S.orderIsoOfFin rfl j : S) : Fin n)) x).symm
    _ = _ := congrArg (List.map x) horder

theorem configuration_sort_filter {α : Type*} [LinearOrder α]
    (S : Finset α) (p : α → Bool) :
    (S.filter (fun a => p a)).sort (· ≤ ·) = (S.sort (· ≤ ·)).filter p := by
  have hn := (Finset.sort_nodup (· ≤ ·) S).filter p
  have hs := (Finset.sort_sorted (· ≤ ·) S).filter p
  have hh := (List.toFinset_sort (· ≤ ·) hn).mpr hs
  simpa only [List.toFinset_filter, Finset.sort_toFinset] using hh

theorem configurationList_restriction (U : Set X) (z : FiniteConfiguration X) :
    configurationList (configurationRestriction U z) =
      (configurationList z).filter (fun x => decide (x ∈ U)) := by
  classical
  rcases z with ⟨n, x⟩
  unfold configurationRestriction
  rw [configurationList_subsequence]
  unfold configurationRestrictionIndices
  have hfilter : Finset.univ.filter (fun j : Fin n => x j ∈ U) =
      Finset.univ.filter (fun j : Fin n => decide (x j ∈ U)) := by simp
  rw [hfilter, configuration_sort_filter, Fin.sort_univ]
  change ((List.finRange n).filter (fun j => decide (x j ∈ U))).map x =
    (List.ofFn x).filter (fun y => decide (y ∈ U))
  rw [List.ofFn_eq_map, List.filter_map]
  rfl

theorem configurationRestriction_composition (U V : Set X) (z : FiniteConfiguration X) :
    configurationRestriction U (configurationRestriction V z) =
      configurationRestriction (U ∩ V) z := by
  classical
  apply configurationList_injective
  rw [configurationList_restriction, configurationList_restriction,
    configurationList_restriction, List.filter_filter]
  congr 1
  funext x
  simp

end Antichain
