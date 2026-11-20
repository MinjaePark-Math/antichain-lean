import Antichain.SimplicialGridWeights
import Antichain.SimplicialInterpolationRegularity
import Antichain.SimplicialInterpolationApproximation
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Order.Interval.Finset.Fin

/-! Ordered-simplex and barycentric identities for the actual finite grid
interpolant. The rounding weights and their partition of unity are established
in SimplicialGridWeights; regularity is packaged independently. -/

noncomputable section
namespace Antichain
open Set Finset MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

theorem simplicial_exists_descending_permutation {d : ℕ} (u : Fin d → ℝ) :
    ∃ σ : Equiv.Perm (Fin d), Antitone (fun j => u (σ j)) := by
  classical
  let rel : Fin d → Fin d → Prop := fun i j => u j ≤ u i
  letI : IsTotal (Fin d) rel := ⟨fun i j => le_total (u j) (u i)⟩
  letI : IsTrans (Fin d) rel := ⟨fun _ _ _ hij hjk => le_trans hjk hij⟩
  letI : IsRefl (Fin d) rel := ⟨fun _ => le_rfl⟩
  let l := (List.finRange d).mergeSort (fun i j => rel i j)
  have hp : l.Perm (List.finRange d) := List.mergeSort_perm _ _
  have hlen : l.length = d := by simpa using hp.length_eq
  have hnd : l.Nodup := hp.nodup_iff.mpr (List.nodup_finRange d)
  have hall : ∀ i : Fin d, i ∈ l := by intro i; rw [hp.mem_iff]; simp
  let σ : Equiv.Perm (Fin d) :=
    (finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hall)
  have hsorted : List.Sorted rel l := List.sorted_mergeSort' rel _
  refine ⟨σ, ?_⟩
  intro i j hij
  have hh := hsorted.rel_get_of_le
    (show Fin.cast hlen.symm i ≤ Fin.cast hlen.symm j from hij)
  exact hh

theorem exists_simplicialGrid_cell {d N : ℕ} (hN : 0 < N) (z : Fin d → ℝ)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) N) :
    ∃ b : Fin d → Fin N, ∀ i, (b i : ℝ) ≤ z i ∧ z i ≤ (b i : ℝ) + 1 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hchoices : ∀ i, ∃ b : Fin N, (b : ℝ) ≤ z i ∧ z i ≤ (b : ℝ) + 1 := by
    intro i
    by_cases heq : z i = N
    · refine ⟨⟨N - 1, by omega⟩, ?_, ?_⟩ <;>
        simp only [Nat.cast_sub hN, Nat.cast_one] <;> linarith
    · have hlt : z i < N := lt_of_le_of_ne (hz i).2 heq
      have hf : Nat.floor (z i) < N := (Nat.floor_lt' hN.ne').mpr hlt
      exact ⟨⟨Nat.floor (z i), hf⟩, Nat.floor_le (hz i).1, (Nat.lt_floor_add_one _).le⟩
  choose b hb using hchoices
  exact ⟨b, hb⟩

def kuhnGridSimplex {d N : ℕ} (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) :
    Set (Fin d → ℝ) :=
  {z | (∀ i, (b i : ℝ) ≤ z i ∧ z i ≤ (b i : ℝ) + 1) ∧
    Antitone (fun j => z (σ j) - (b (σ j) : ℝ))}

def kuhnGridVertex {d N : ℕ} (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d))
    (j : Fin (d + 1)) : SimplicialGridVertex (Fin d) N :=
  fun i => ⟨(b i).val + if (σ.symm i).val < j.val then 1 else 0, by
    have hb := (b i).isLt
    split_ifs <;> omega⟩

theorem kuhnGridVertex_apply {d N : ℕ} (b : Fin d → Fin N)
    (σ : Equiv.Perm (Fin d)) (j : Fin (d + 1)) (i : Fin d) :
    (kuhnGridVertex b σ j i : ℝ) =
      (b i : ℝ) + if (σ.symm i).val < j.val then 1 else 0 := by
  dsimp [kuhnGridVertex]
  split_ifs <;> push_cast <;> ring

theorem kuhnGridVertex_injective {d N : ℕ} (b : Fin d → Fin N)
    (σ : Equiv.Perm (Fin d)) : Function.Injective (kuhnGridVertex b σ) := by
  intro j k h
  by_contra hne
  wlog hjk : j < k generalizing j k
  · exact this (j := k) (k := j) h.symm (fun hkj => hne hkj.symm)
      (lt_of_le_of_ne (le_of_not_gt hjk) (fun hkj => hne hkj.symm))
  have hdim : j.val < d := by omega
  let i : Fin d := ⟨j.val, hdim⟩
  have hh := congrArg (fun v : SimplicialGridVertex (Fin d) N => (v (σ i) : ℝ)) h
  simp only [kuhnGridVertex_apply, Equiv.symm_apply_apply] at hh
  have hi : ¬i.val < j.val := by simp [i]
  have hik : i.val < k.val := hjk
  simp only [hi, hik, ↓reduceIte] at hh
  linarith

theorem kuhnGridSimplex_cover {d N : ℕ} (hN : 0 < N) (z : Fin d → ℝ)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) N) :
    ∃ b : Fin d → Fin N, ∃ σ : Equiv.Perm (Fin d), z ∈ kuhnGridSimplex b σ := by
  obtain ⟨b, hb⟩ := exists_simplicialGrid_cell hN z hz
  obtain ⟨σ, hσ⟩ := simplicial_exists_descending_permutation (fun i => z i - (b i : ℝ))
  exact ⟨b, σ, hb, hσ⟩

def kuhnLowerAffine {d N : ℕ} (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d))
    (j : Fin (d + 1)) : (Fin d → ℝ) →ᵃ[ℝ] ℝ :=
  if h : j.val = 0 then AffineMap.const ℝ _ 0 else
    let i : Fin d := ⟨j.val - 1, by have := j.isLt; omega⟩
    AffineMap.const ℝ _ (1 + (b (σ i) : ℝ)) - (LinearMap.proj (σ i)).toAffineMap

def kuhnUpperAffine {d N : ℕ} (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d))
    (j : Fin (d + 1)) : (Fin d → ℝ) →ᵃ[ℝ] ℝ :=
  if h : j.val < d then
    AffineMap.const ℝ _ (1 + (b (σ ⟨j.val, h⟩) : ℝ)) -
      (LinearMap.proj (σ ⟨j.val, h⟩)).toAffineMap
  else AffineMap.const ℝ _ 1

def kuhnWeightAffine {d N : ℕ} (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d))
    (j : Fin (d + 1)) : (Fin d → ℝ) →ᵃ[ℝ] ℝ :=
  kuhnUpperAffine b σ j - kuhnLowerAffine b σ j

theorem simplicialRoundingLower_kuhnVertex {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (j : Fin (d + 1)) :
    simplicialRoundingLower z (kuhnGridVertex b σ j) = kuhnLowerAffine b σ j z := by
  classical
  by_cases hj : j.val = 0
  · have hsup : univ.sup' univ_nonempty
        (fun i => (kuhnGridVertex b σ j i : ℝ) - z i) ≤ 0 := by
      apply Finset.sup'_le
      intro i _
      rw [kuhnGridVertex_apply]
      simp only [hj, Nat.not_lt_zero, ↓reduceIte, add_zero]
      linarith [(hz.1 i).1]
    simp only [simplicialRoundingLower, max_eq_left hsup, kuhnLowerAffine, dif_pos hj,
      AffineMap.const_apply]
  · let k : Fin d := ⟨j.val - 1, by have := j.isLt; omega⟩
    rw [kuhnLowerAffine, dif_neg hj]
    change max 0 (univ.sup' univ_nonempty
      (fun i => (kuhnGridVertex b σ j i : ℝ) - z i)) =
        1 + (b (σ k) : ℝ) - z (σ k)
    have hnonneg : 0 ≤ 1 + (b (σ k) : ℝ) - z (σ k) := by linarith [(hz.1 (σ k)).2]
    apply le_antisymm
    · apply max_le hnonneg
      apply Finset.sup'_le
      intro i _
      rw [kuhnGridVertex_apply]
      by_cases hi : (σ.symm i).val < j.val
      · simp only [hi, ↓reduceIte]
        have hidx : σ.symm i ≤ k := by change _ ≤ j.val - 1; omega
        have ho := hz.2 hidx
        simp only [Equiv.apply_symm_apply] at ho
        linarith
      · simp only [hi, ↓reduceIte, add_zero]
        linarith [(hz.1 i).1]
    · have he : 1 + (b (σ k) : ℝ) - z (σ k) =
          (kuhnGridVertex b σ j (σ k) : ℝ) - z (σ k) := by
        rw [kuhnGridVertex_apply]
        simp only [Equiv.symm_apply_apply]
        have hk : k.val < j.val := by dsimp [k]; omega
        simp only [hk, ↓reduceIte]
        ring
      rw [he]
      exact (Finset.le_sup' (fun i => (kuhnGridVertex b σ j i : ℝ) - z i)
        (mem_univ (σ k))).trans (le_max_right (0 : ℝ) _)

theorem simplicialRoundingUpper_kuhnVertex {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (j : Fin (d + 1)) :
    simplicialRoundingUpper z (kuhnGridVertex b σ j) = kuhnUpperAffine b σ j z := by
  classical
  by_cases hj : j.val < d
  · let k : Fin d := ⟨j.val, hj⟩
    rw [kuhnUpperAffine, dif_pos hj]
    change min 1 (univ.inf' univ_nonempty
      (fun i => (kuhnGridVertex b σ j i : ℝ) + 1 - z i)) =
        1 + (b (σ k) : ℝ) - z (σ k)
    have hleone : 1 + (b (σ k) : ℝ) - z (σ k) ≤ 1 := by linarith [(hz.1 (σ k)).1]
    apply le_antisymm
    · have he : (kuhnGridVertex b σ j (σ k) : ℝ) + 1 - z (σ k) =
          1 + (b (σ k) : ℝ) - z (σ k) := by
        rw [kuhnGridVertex_apply]
        simp only [Equiv.symm_apply_apply]
        have hk : ¬k.val < j.val := by simp [k]
        simp only [hk, ↓reduceIte, add_zero]
        ring
      exact (min_le_right _ _).trans ((Finset.inf'_le _ (mem_univ (σ k))).trans_eq he)
    · apply le_min hleone
      apply Finset.le_inf'
      intro i _
      rw [kuhnGridVertex_apply]
      by_cases hi : (σ.symm i).val < j.val
      · simp only [hi, ↓reduceIte]
        linarith [(hz.1 i).2]
      · simp only [hi, ↓reduceIte, add_zero]
        have hidx : k ≤ σ.symm i := by change j.val ≤ _; omega
        have ho := hz.2 hidx
        simp only [Equiv.apply_symm_apply] at ho
        linarith
  · have hjd : j.val = d := by have := j.isLt; omega
    have hinf : 1 ≤ univ.inf' univ_nonempty
        (fun i => (kuhnGridVertex b σ j i : ℝ) + 1 - z i) := by
      apply Finset.le_inf'
      intro i _
      rw [kuhnGridVertex_apply]
      have hi : (σ.symm i).val < j.val := by rw [hjd]; exact (σ.symm i).isLt
      simp only [hi, ↓reduceIte]
      linarith [(hz.1 i).2]
    simp only [simplicialRoundingUpper, min_eq_left hinf, kuhnUpperAffine, dif_neg hj,
      AffineMap.const_apply]

theorem simplicial_antitone_predicate_cut {d : ℕ} (P : Fin d → Prop)
    (hP : ∀ i j : Fin d, i ≤ j → P j → P i) :
    ∃ r : Fin (d + 1), ∀ i : Fin d, P i ↔ i.val < r.val := by
  classical
  let S : Finset (Fin d) := univ.filter P
  have hcard : S.card ≤ d := by simpa using S.card_le_univ
  refine ⟨⟨S.card, by omega⟩, fun i => ?_⟩
  constructor
  · intro hi
    have hsub : (Iic i : Finset (Fin d)) ⊆ S := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _, hP j i (mem_Iic.mp hj) hi⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    change i.val < S.card
    omega
  · intro hi
    by_contra hnot
    have hsub : S ⊆ (Iio i : Finset (Fin d)) := by
      intro j hj
      have hPj := (mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact hnot (hP i j (le_of_not_gt hji) hPj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    change i.val < S.card at hi
    omega

theorem simplicialGridHat_pos_exists_kuhnVertex {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (v : SimplicialGridVertex (Fin d) N)
    (hv : 0 < simplicialGridHat z v) :
    ∃ j : Fin (d + 1), v = kuhnGridVertex b σ j := by
  have hLU : simplicialRoundingLower z v < simplicialRoundingUpper z v := by
    have h := (lt_max_iff.mp hv).resolve_left (lt_irrefl 0)
    linarith
  have ht : simplicialRoundingLower z v ∈ simplicialRoundingFiber z v := by
    rw [simplicialRoundingFiber_eq_Ico]
    exact ⟨le_rfl, hLU⟩
  have hchoices (i : Fin d) : (v i).val = (b i).val ∨ (v i).val = (b i).val + 1 := by
    have hloR : ((b i).val : ℝ) < (v i).val + 1 := by
      linarith [(hz.1 i).1, (ht.2 i).2, ht.1.1]
    have hhiR : ((v i).val : ℝ) < (b i).val + 2 := by
      linarith [(hz.1 i).2, (ht.2 i).1, ht.1.2]
    have hlo : (b i).val < (v i).val + 1 := by exact_mod_cast hloR
    have hhi : (v i).val < (b i).val + 2 := by exact_mod_cast hhiR
    omega
  let P : Fin d → Prop := fun i => (v (σ i)).val = (b (σ i)).val + 1
  have hdown : ∀ i j : Fin d, i ≤ j → P j → P i := by
    intro i j hij hPj
    by_contra hPi
    have hi : (v (σ i)).val = (b (σ i)).val :=
      (hchoices (σ i)).resolve_right hPi
    have hj : (v (σ j) : ℝ) = (b (σ j) : ℝ) + 1 := by exact_mod_cast hPj
    have hiR : (v (σ i) : ℝ) = (b (σ i) : ℝ) := by exact_mod_cast hi
    have hsort := hz.2 hij
    linarith [(ht.2 (σ i)).2, (ht.2 (σ j)).1]
  obtain ⟨r, hr⟩ := simplicial_antitone_predicate_cut P hdown
  refine ⟨r, ?_⟩
  funext i
  apply Fin.ext
  change (v i).val = (b i).val + if (σ.symm i).val < r.val then 1 else 0
  by_cases hi : (σ.symm i).val < r.val
  · simp only [hi, ↓reduceIte]
    have hp := (hr (σ.symm i)).mpr hi
    simpa only [P, Equiv.apply_symm_apply] using hp
  · simp only [hi, ↓reduceIte, add_zero]
    apply (hchoices i).resolve_right
    intro hp
    have hPi : P (σ.symm i) := by simpa only [P, Equiv.apply_symm_apply] using hp
    exact hi ((hr (σ.symm i)).mp hPi)

theorem simplicialGridHat_zero_off_kuhnVertices {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (v : SimplicialGridVertex (Fin d) N)
    (hv : ∀ j, v ≠ kuhnGridVertex b σ j) :
    simplicialGridHat z v = 0 := by
  by_contra h
  have hpos : 0 < simplicialGridHat z v :=
    lt_of_le_of_ne (simplicialGridHat_nonneg z v) (fun hh => h hh.symm)
  obtain ⟨j, hj⟩ := simplicialGridHat_pos_exists_kuhnVertex b σ hz v hpos
  exact hv j hj

theorem kuhnWeightAffine_nonneg {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (j : Fin (d + 1)) :
    0 ≤ kuhnWeightAffine b σ j z := by
  by_cases hj0 : j.val = 0
  · have hjd : j.val < d := by have := NeZero.pos d; omega
    simp only [kuhnWeightAffine, AffineMap.coe_sub, Pi.sub_apply,
      kuhnLowerAffine, dif_pos hj0, kuhnUpperAffine, dif_pos hjd,
      AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.proj_apply]
    linarith [(hz.1 (σ ⟨j.val, hjd⟩)).2]
  · let lo : Fin d := ⟨j.val - 1, by have := j.isLt; omega⟩
    by_cases hjd : j.val < d
    · simp only [kuhnWeightAffine, AffineMap.coe_sub, Pi.sub_apply,
        kuhnLowerAffine, dif_neg hj0, kuhnUpperAffine, dif_pos hjd,
        AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.proj_apply]
      have ho := hz.2 (show lo ≤ (⟨j.val, hjd⟩ : Fin d) by change j.val - 1 ≤ j.val; omega)
      change 0 ≤ (1 + (b (σ ⟨j.val, hjd⟩) : ℝ) - z (σ ⟨j.val, hjd⟩)) -
        (1 + (b (σ lo) : ℝ) - z (σ lo))
      linarith
    · simp only [kuhnWeightAffine, AffineMap.coe_sub, Pi.sub_apply,
        kuhnLowerAffine, dif_neg hj0, kuhnUpperAffine, dif_neg hjd,
        AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.proj_apply]
      change 0 ≤ 1 - (1 + (b (σ lo) : ℝ) - z (σ lo))
      linarith [(hz.1 (σ lo)).1]

theorem simplicialGridHat_kuhnVertex {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (j : Fin (d + 1)) :
    simplicialGridHat z (kuhnGridVertex b σ j) = kuhnWeightAffine b σ j z := by
  unfold simplicialGridHat
  rw [simplicialRoundingLower_kuhnVertex b σ hz,
    simplicialRoundingUpper_kuhnVertex b σ hz]
  change max 0 (kuhnWeightAffine b σ j z) = kuhnWeightAffine b σ j z
  exact max_eq_right (kuhnWeightAffine_nonneg b σ hz j)

/-- On an ordered grid simplex the global finite hat sum uses precisely its
chain of vertices. This also proves compatibility on overlapping cells. -/
theorem sum_simplicialGridHat_eq_kuhn_sum {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (c : SimplicialGridVertex (Fin d) N → ℝ) :
    (∑ v, c v * simplicialGridHat z v) =
      ∑ j, c (kuhnGridVertex b σ j) * kuhnWeightAffine b σ j z := by
  classical
  let T : Finset (SimplicialGridVertex (Fin d) N) := univ.image (kuhnGridVertex b σ)
  have hoff : ∀ v ∈ (univ : Finset (SimplicialGridVertex (Fin d) N)), v ∉ T →
      c v * simplicialGridHat z v = 0 := by
    intro v _ hv
    rw [simplicialGridHat_zero_off_kuhnVertices b σ hz v]
    · exact mul_zero _
    · intro j hj
      apply hv
      exact mem_image.mpr ⟨j, mem_univ _, hj.symm⟩
  rw [← Finset.sum_subset (Finset.subset_univ T) hoff]
  dsimp [T]
  rw [Finset.sum_image (fun _ _ _ _ h => kuhnGridVertex_injective b σ h)]
  apply Finset.sum_congr rfl
  intro j _
  rw [simplicialGridHat_kuhnVertex b σ hz]

def kuhnAffineInterpolant {d N : ℕ} (b : Fin d → Fin N)
    (σ : Equiv.Perm (Fin d)) (c : SimplicialGridVertex (Fin d) N → ℝ) :
    (Fin d → ℝ) →ᵃ[ℝ] ℝ :=
  ∑ j, c (kuhnGridVertex b σ j) • kuhnWeightAffine b σ j

theorem kuhnAffineInterpolant_apply {d N : ℕ} (b : Fin d → Fin N)
    (σ : Equiv.Perm (Fin d)) (c : SimplicialGridVertex (Fin d) N → ℝ)
    (z : Fin d → ℝ) :
    kuhnAffineInterpolant b σ c z =
      ∑ j, c (kuhnGridVertex b σ j) * kuhnWeightAffine b σ j z := by
  unfold kuhnAffineInterpolant
  induction (univ : Finset (Fin (d + 1))) using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, AffineMap.coe_add, Pi.add_apply, ih]
      rw [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem sum_simplicialGridHat_eq_affine {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) (c : SimplicialGridVertex (Fin d) N → ℝ) :
    (∑ v, c v * simplicialGridHat z v) = kuhnAffineInterpolant b σ c z := by
  rw [kuhnAffineInterpolant_apply]
  exact sum_simplicialGridHat_eq_kuhn_sum b σ hz c

theorem sum_kuhnWeightAffine {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) {z : Fin d → ℝ}
    (hz : z ∈ kuhnGridSimplex b σ) :
    ∑ j, kuhnWeightAffine b σ j z = 1 := by
  have hzN : ∀ i, z i ∈ Icc (0 : ℝ) N := by
    intro i
    have hb0 : (0 : ℝ) ≤ (b i : ℝ) := by positivity
    have hbN : (b i : ℝ) + 1 ≤ N := by exact_mod_cast (b i).isLt
    exact ⟨hb0.trans (hz.1 i).1, (hz.1 i).2.trans hbN⟩
  have h := sum_simplicialGridHat_eq_kuhn_sum b σ hz (fun _ => 1)
  simp only [one_mul] at h
  apply h.symm.trans
  convert sum_simplicialGridHat z hzN using 1
  apply Finset.sum_congr
  · ext v
    simp
  · intro v _
    rfl

theorem simplicialGridHat_integer_self {d N : ℕ} [NeZero d]
    (v : SimplicialGridVertex (Fin d) N) :
    simplicialGridHat (fun i => (v i : ℝ)) v = 1 := by
  simp [simplicialGridHat, simplicialRoundingLower, simplicialRoundingUpper]

theorem simplicialGridHat_integer_off_diagonal {d N : ℕ} [NeZero d]
    (v w : SimplicialGridVertex (Fin d) N) (hvw : v ≠ w) :
    simplicialGridHat (fun i => (w i : ℝ)) v = 0 := by
  by_contra h
  have hpos : 0 < simplicialGridHat (fun i => (w i : ℝ)) v :=
    lt_of_le_of_ne (simplicialGridHat_nonneg _ _) (fun hh => h hh.symm)
  apply hvw
  funext i
  apply Fin.ext
  have hnear := abs_lt.mp (simplicialGridHat_support_near _ v hpos i)
  have hv : (v i).val < (w i).val + 1 := by
    exact_mod_cast (show (v i : ℝ) < (w i : ℝ) + 1 by linarith)
  have hw : (w i).val < (v i).val + 1 := by
    exact_mod_cast (show (w i : ℝ) < (v i : ℝ) + 1 by linarith)
  omega

theorem simplicialGridPoint_scale {d N : ℕ} (hN : 0 < N)
    (v : SimplicialGridVertex (Fin d) N) :
    (fun i => (N : ℝ) * simplicialGridPoint v i) = (fun i => (v i : ℝ)) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext i
  dsimp [simplicialGridPoint]
  field_simp

/-- The globally continuous interpolant takes the prescribed data exactly at
every vertex of the finite grid, including its boundary. -/
theorem simplicialInterpolantBCF_gridPoint {d N : ℕ} [NeZero d]
    (hN : 0 < N) (g : (Fin d → ℝ) →ᵇ ℝ)
    (v : SimplicialGridVertex (Fin d) N) :
    simplicialInterpolantBCF N g (simplicialGridPoint v) = g (simplicialGridPoint v) := by
  classical
  rw [simplicialInterpolantBCF_apply]
  simp only [scaledSimplicialGridHat, simplicialGridPoint_scale hN v]
  rw [Finset.sum_eq_single v]
  · rw [simplicialGridHat_integer_self, mul_one]
  · intro w _ hw
    rw [simplicialGridHat_integer_off_diagonal w v hw, mul_zero]
  · simp

def scaledKuhnGridSimplex {d N : ℕ} (b : Fin d → Fin N)
    (σ : Equiv.Perm (Fin d)) : Set (Fin d → ℝ) :=
  (fun x i => (N : ℝ) * x i) ⁻¹' kuhnGridSimplex b σ

/-- The unit cube is covered by finitely many scaled ordered grid simplexes. -/
theorem scaledKuhnGridSimplex_cover {d N : ℕ} (hN : 0 < N)
    {x : Fin d → ℝ} (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    ∃ b : Fin d → Fin N, ∃ σ : Equiv.Perm (Fin d), x ∈ scaledKuhnGridSimplex b σ := by
  apply kuhnGridSimplex_cover hN (fun i => (N : ℝ) * x i)
  intro i
  exact ⟨mul_nonneg (Nat.cast_nonneg N) (hx i).1,
    by simpa using mul_le_mul_of_nonneg_left (hx i).2 (Nat.cast_nonneg N)⟩

def scaledKuhnAffineInterpolant {d N : ℕ} (b : Fin d → Fin N)
    (σ : Equiv.Perm (Fin d)) (g : (Fin d → ℝ) →ᵇ ℝ) :
    (Fin d → ℝ) →ᵃ[ℝ] ℝ :=
  (kuhnAffineInterpolant b σ (fun v => g (simplicialGridPoint v))).comp
    ((N : ℝ) • (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))).toAffineMap

theorem scaledKuhnAffineInterpolant_apply {d N : ℕ} (b : Fin d → Fin N)
    (σ : Equiv.Perm (Fin d)) (g : (Fin d → ℝ) →ᵇ ℝ) (x : Fin d → ℝ) :
    scaledKuhnAffineInterpolant b σ g x =
      kuhnAffineInterpolant b σ (fun v => g (simplicialGridPoint v))
        (fun i => (N : ℝ) * x i) := rfl

/-- On each ordered simplex the same global interpolant is an actual affine
map. On shared faces these affine formulas agree because they equal that one
global function. -/
theorem simplicialInterpolantBCF_eq_affine_on_simplex {d N : ℕ} [NeZero d]
    (b : Fin d → Fin N) (σ : Equiv.Perm (Fin d)) (g : (Fin d → ℝ) →ᵇ ℝ)
    {x : Fin d → ℝ} (hx : x ∈ scaledKuhnGridSimplex b σ) :
    simplicialInterpolantBCF N g x = scaledKuhnAffineInterpolant b σ g x := by
  rw [simplicialInterpolantBCF_apply, scaledKuhnAffineInterpolant_apply]
  simp only [scaledSimplicialGridHat]
  apply Eq.trans ?_ (sum_simplicialGridHat_eq_affine b σ hx (fun v => g (simplicialGridPoint v)))
  apply Finset.sum_congr
  · ext v
    simp
  · intro v _
    rfl

theorem simplicialInterpolantBCF_affine_formulas_agree {d N : ℕ} [NeZero d]
    (b b' : Fin d → Fin N) (σ σ' : Equiv.Perm (Fin d)) (g : (Fin d → ℝ) →ᵇ ℝ)
    {x : Fin d → ℝ} (hx : x ∈ scaledKuhnGridSimplex b σ)
    (hx' : x ∈ scaledKuhnGridSimplex b' σ') :
    scaledKuhnAffineInterpolant b σ g x = scaledKuhnAffineInterpolant b' σ' g x := by
  rw [← simplicialInterpolantBCF_eq_affine_on_simplex b σ g hx,
    ← simplicialInterpolantBCF_eq_affine_on_simplex b' σ' g hx']

end Antichain
