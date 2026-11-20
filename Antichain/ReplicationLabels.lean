import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Sum

/-! The actual label choices in replication: each tile receives m labels,
enumerated in increasing order. Their cardinality is N!/(m!)^q. -/

noncomputable section

namespace Antichain

def BalancedLabeling (m q N : ℕ) :=
  {f : Fin N → Fin q // ∀ i, Fintype.card {j // f j = i} = m}

instance (m q N : ℕ) : Fintype (BalancedLabeling m q N) := by
  classical
  unfold BalancedLabeling
  infer_instance

def labelingFiberEquiv (m q N : ℕ) (e : Fin N ≃ Fin q × Fin m) (i : Fin q) :
    {j : Fin N // (e j).1 = i} ≃ Fin m where
  toFun j := (e j.val).2
  invFun k := ⟨e.symm (i, k), by simp⟩
  left_inv j := by apply Subtype.ext; simp [← j.property]
  right_inv k := by simp

def equivLabeling (m q N : ℕ) (e : Fin N ≃ Fin q × Fin m) : BalancedLabeling m q N :=
  ⟨fun j => (e j).1, fun i => (Fintype.card_congr (labelingFiberEquiv m q N e i)).trans
    (Fintype.card_fin m)⟩

def labelingEnumerations (m q N : ℕ) :=
  Σ f : BalancedLabeling m q N, ∀ i, {j : Fin N // f.val j = i} ≃ Fin m

def labelingEnumerationsToEquiv (m q N : ℕ) (a : labelingEnumerations m q N) :
    Fin N ≃ Fin q × Fin m :=
  (Equiv.sigmaFiberEquiv a.1.val).symm.trans (Equiv.sigmaEquivProdOfEquiv a.2)

@[simp] theorem labelingEnumerationsToEquiv_apply (m q N : ℕ)
    (a : labelingEnumerations m q N) (j : Fin N) :
    labelingEnumerationsToEquiv m q N a j = (a.1.val j, a.2 (a.1.val j) ⟨j, rfl⟩) := rfl

theorem labelingEnumerationsToEquiv_bijective (m q N : ℕ) :
    Function.Bijective (labelingEnumerationsToEquiv m q N) := by
  constructor
  · rintro ⟨f, a⟩ ⟨g, b⟩ hab
    have hfg : f = g := by
      apply Subtype.ext
      funext j
      exact congrArg (fun e : Fin N ≃ Fin q × Fin m => (e j).1) hab
    subst g
    have henum : a = b := by
      funext i
      apply Equiv.ext
      rintro ⟨j, hj⟩
      subst i
      exact congrArg (fun e : Fin N ≃ Fin q × Fin m => (e j).2) hab
    subst b
    rfl
  · intro e
    refine ⟨⟨equivLabeling m q N e, labelingFiberEquiv m q N e⟩, ?_⟩
    apply Equiv.ext
    intro j
    rfl

def labelingEnumerationsEquiv (m q N : ℕ) :
    labelingEnumerations m q N ≃ (Fin N ≃ Fin q × Fin m) :=
  Equiv.ofBijective _ (labelingEnumerationsToEquiv_bijective m q N)

instance (m q N : ℕ) : Fintype (labelingEnumerations m q N) := by
  classical
  unfold labelingEnumerations
  infer_instance

theorem card_balancedLabeling_mul (m q N : ℕ) (hN : N = q * m) :
    Fintype.card (BalancedLabeling m q N) * (Nat.factorial m) ^ q = Nat.factorial N := by
  classical
  have hsize : Fintype.card (Fin N) = Fintype.card (Fin q × Fin m) := by simpa using hN
  let e : Fin N ≃ Fin q × Fin m := Classical.choice (Fintype.card_eq.mp hsize)
  have hc := Fintype.card_congr (labelingEnumerationsEquiv m q N)
  rw [Fintype.card_equiv e, Fintype.card_fin] at hc
  change Fintype.card (Σ f : BalancedLabeling m q N,
    ∀ i, {j : Fin N // f.val j = i} ≃ Fin m) = _ at hc
  rw [Fintype.card_sigma] at hc
  have heach (f : BalancedLabeling m q N) :
      Fintype.card (∀ i, {j : Fin N // f.val j = i} ≃ Fin m) = (Nat.factorial m) ^ q := by
    rw [Fintype.card_pi]
    have hf (i : Fin q) : Fintype.card ({j : Fin N // f.val j = i} ≃ Fin m) =
        Nat.factorial m := by
      let ei : {j : Fin N // f.val j = i} ≃ Fin m :=
        (monoEquivOfFin _ (f.property i)).symm.toEquiv
      rw [Fintype.card_equiv ei, f.property i]
    simp_rw [hf]
    simp
  simp_rw [heach] at hc
  simpa using hc

theorem card_balancedLabeling (m q N : ℕ) (hN : N = q * m) :
    Fintype.card (BalancedLabeling m q N) = Nat.factorial N / (Nat.factorial m) ^ q := by
  rw [← card_balancedLabeling_mul m q N hN]
  exact (Nat.mul_div_cancel _ (pow_pos (Nat.factorial_pos m) q)).symm

theorem card_balancedLabeling_real (m q N : ℕ) (hN : N = q * m) :
    (Fintype.card (BalancedLabeling m q N) : ℝ) =
      (Nat.factorial N : ℝ) / (Nat.factorial m : ℝ) ^ q := by
  have hpos : (0 : ℝ) < (Nat.factorial m : ℝ) ^ q := by positivity
  apply (eq_div_iff (ne_of_gt hpos)).mpr
  exact_mod_cast card_balancedLabeling_mul m q N hN

/-- Increasing enumeration of each tile's label set. -/
def balancedLabelEquiv (m q N : ℕ) (f : BalancedLabeling m q N) :
    Fin N ≃ Fin q × Fin m :=
  labelingEnumerationsToEquiv m q N
    ⟨f, fun i => (monoEquivOfFin _ (f.property i)).symm.toEquiv⟩

@[simp] theorem balancedLabelEquiv_fst (m q N : ℕ) (f : BalancedLabeling m q N)
    (j : Fin N) : (balancedLabelEquiv m q N f j).1 = f.val j := rfl

theorem balancedLabelEquiv_increasing (m q N : ℕ) (f : BalancedLabeling m q N)
    (i : Fin q) : StrictMono (fun j : Fin m => (balancedLabelEquiv m q N f).symm (i, j)) := by
  intro j k hjk
  change (monoEquivOfFin _ (f.property i) j).val <
    (monoEquivOfFin _ (f.property i) k).val
  exact (monoEquivOfFin _ (f.property i)).strictMono hjk

/-- Label allocations with arbitrary prescribed occupancies. -/
def PrescribedLabeling (q N : ℕ) (n : Fin q → ℕ) :=
  {f : Fin N → Fin q // ∀ i, Fintype.card {j // f j = i} = n i}

instance (q N : ℕ) (n : Fin q → ℕ) : Fintype (PrescribedLabeling q N n) := by
  classical
  unfold PrescribedLabeling
  infer_instance

def sigmaFirstFiberEquiv (q : ℕ) (n : Fin q → ℕ) (i : Fin q) :
    {x : Σ j, Fin (n j) // x.1 = i} ≃ Fin (n i) where
  toFun x := x.property ▸ x.val.2
  invFun k := ⟨⟨i, k⟩, rfl⟩
  left_inv := by rintro ⟨⟨j, k⟩, h⟩; cases h; rfl
  right_inv _ := rfl

def prescribedFiberEquiv (q N : ℕ) (n : Fin q → ℕ)
    (e : Fin N ≃ Σ i, Fin (n i)) (i : Fin q) :
    {j : Fin N // (e j).1 = i} ≃ Fin (n i) :=
  (e.subtypeEquiv (fun _ => Iff.rfl)).trans (sigmaFirstFiberEquiv q n i)

def equivPrescribedLabeling (q N : ℕ) (n : Fin q → ℕ)
    (e : Fin N ≃ Σ i, Fin (n i)) : PrescribedLabeling q N n :=
  ⟨fun j => (e j).1, fun i =>
    (Fintype.card_congr (prescribedFiberEquiv q N n e i)).trans (Fintype.card_fin (n i))⟩

def prescribedEnumerations (q N : ℕ) (n : Fin q → ℕ) :=
  Σ f : PrescribedLabeling q N n, ∀ i, {j : Fin N // f.val j = i} ≃ Fin (n i)

def prescribedEnumerationsToEquiv (q N : ℕ) (n : Fin q → ℕ)
    (a : prescribedEnumerations q N n) : Fin N ≃ Σ i, Fin (n i) :=
  (Equiv.sigmaFiberEquiv a.1.val).symm.trans (Equiv.sigmaCongrRight a.2)

@[simp] theorem prescribedEnumerationsToEquiv_apply (q N : ℕ) (n : Fin q → ℕ)
    (a : prescribedEnumerations q N n) (j : Fin N) :
    prescribedEnumerationsToEquiv q N n a j = ⟨a.1.val j, a.2 (a.1.val j) ⟨j, rfl⟩⟩ := rfl

theorem prescribedEnumerationsToEquiv_bijective (q N : ℕ) (n : Fin q → ℕ) :
    Function.Bijective (prescribedEnumerationsToEquiv q N n) := by
  constructor
  · rintro ⟨f, a⟩ ⟨g, b⟩ hab
    have hfg : f = g := by
      apply Subtype.ext
      funext j
      exact congrArg (fun e : Fin N ≃ Σ i, Fin (n i) => (e j).1) hab
    subst g
    have henum : a = b := by
      funext i
      apply Equiv.ext
      rintro ⟨j, hj⟩
      subst i
      have hh := congrArg (fun e : Fin N ≃ Σ i, Fin (n i) => e j) hab
      exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    subst b
    rfl
  · intro e
    refine ⟨⟨equivPrescribedLabeling q N n e, prescribedFiberEquiv q N n e⟩, ?_⟩
    apply Equiv.ext
    intro j
    rfl

def prescribedEnumerationsEquiv (q N : ℕ) (n : Fin q → ℕ) :
    prescribedEnumerations q N n ≃ (Fin N ≃ Σ i, Fin (n i)) :=
  Equiv.ofBijective _ (prescribedEnumerationsToEquiv_bijective q N n)

instance (q N : ℕ) (n : Fin q → ℕ) : Fintype (prescribedEnumerations q N n) := by
  classical
  unfold prescribedEnumerations
  infer_instance

theorem card_prescribedLabeling_mul (q N : ℕ) (n : Fin q → ℕ)
    (hN : N = ∑ i, n i) :
    Fintype.card (PrescribedLabeling q N n) * ∏ i, Nat.factorial (n i) = Nat.factorial N := by
  classical
  have hsize : Fintype.card (Fin N) = Fintype.card (Σ i, Fin (n i)) := by simpa using hN
  let e : Fin N ≃ Σ i, Fin (n i) := Classical.choice (Fintype.card_eq.mp hsize)
  have hc := Fintype.card_congr (prescribedEnumerationsEquiv q N n)
  rw [Fintype.card_equiv e, Fintype.card_fin] at hc
  change Fintype.card (Σ f : PrescribedLabeling q N n,
    ∀ i, {j : Fin N // f.val j = i} ≃ Fin (n i)) = _ at hc
  rw [Fintype.card_sigma] at hc
  have heach (f : PrescribedLabeling q N n) :
      Fintype.card (∀ i, {j : Fin N // f.val j = i} ≃ Fin (n i)) = ∏ i, Nat.factorial (n i) := by
    rw [Fintype.card_pi]
    congr 1
    funext i
    let ei : {j : Fin N // f.val j = i} ≃ Fin (n i) :=
      (monoEquivOfFin _ (f.property i)).symm.toEquiv
    rw [Fintype.card_equiv ei, f.property i]
  simp_rw [heach] at hc
  simpa using hc

theorem card_prescribedLabeling (q N : ℕ) (n : Fin q → ℕ)
    (hN : N = ∑ i, n i) :
    Fintype.card (PrescribedLabeling q N n) = Nat.factorial N / ∏ i, Nat.factorial (n i) := by
  classical
  rw [← card_prescribedLabeling_mul q N n hN]
  exact (Nat.mul_div_cancel _ (Finset.prod_pos (fun _ _ => Nat.factorial_pos _))).symm

theorem card_prescribedLabeling_real (q N : ℕ) (n : Fin q → ℕ)
    (hN : N = ∑ i, n i) :
    (Fintype.card (PrescribedLabeling q N n) : ℝ) =
      (Nat.factorial N : ℝ) / ∏ i, (Nat.factorial (n i) : ℝ) := by
  classical
  have hpos : (0 : ℝ) < ∏ i, (Nat.factorial (n i) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (n i))
  apply (eq_div_iff (ne_of_gt hpos)).mpr
  exact_mod_cast card_prescribedLabeling_mul q N n hN

/-- Each occupied tile is given the increasing enumeration of its actual label fiber. -/
def prescribedLabelEquiv (q N : ℕ) (n : Fin q → ℕ) (f : PrescribedLabeling q N n) :
    Fin N ≃ Σ i, Fin (n i) :=
  prescribedEnumerationsToEquiv q N n
    ⟨f, fun i => (monoEquivOfFin _ (f.property i)).symm.toEquiv⟩

@[simp] theorem prescribedLabelEquiv_fst (q N : ℕ) (n : Fin q → ℕ)
    (f : PrescribedLabeling q N n) (j : Fin N) :
    (prescribedLabelEquiv q N n f j).1 = f.val j := rfl

theorem prescribedLabelEquiv_increasing (q N : ℕ) (n : Fin q → ℕ)
    (f : PrescribedLabeling q N n) (i : Fin q) :
    StrictMono (fun j : Fin (n i) => (prescribedLabelEquiv q N n f).symm ⟨i, j⟩) := by
  intro j k hjk
  change (monoEquivOfFin _ (f.property i) j).val <
    (monoEquivOfFin _ (f.property i) k).val
  exact (monoEquivOfFin _ (f.property i)).strictMono hjk

end Antichain
