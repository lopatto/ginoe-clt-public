/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Algebra.PfaffianPermutationBridge

/-! # Cofactors of the literal Pfaffian permutation sum

The auxiliary permutation decomposition uses Mathlib's order-preserving
`Equiv.Perm.decomposeFin'`, with the empty tail supplied explicitly.
-/

@[expose] public section
noncomputable section
open Equiv
open scoped BigOperators Matrix

namespace Paper.PfaffianBridge

/-- The unique permutation of a singleton and its empty tail. -/
def emptyTailPermEquiv : Perm (Fin 1) ≃ Fin 1 × Perm (Fin 0) := by
  letI : Subsingleton (Fin 1) := ⟨fun i j ↦ Fin.ext (by omega)⟩
  exact
    { toFun := fun _ ↦ (0, 1)
      invFun := fun _ ↦ 1
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }

/-- Removing the first image of a permutation, including its empty-tail case. -/
def firstPermEquiv : (n : ℕ) →
    Perm (Fin (n + 1)) ≃ Fin (n + 1) × Perm (Fin n)
  | 0 => emptyTailPermEquiv
  | n + 1 => Equiv.Perm.decomposeFin' (n := n)

@[simp] theorem firstPermEquiv_symm_zero (n : ℕ) (i : Fin (n + 1))
    (σ : Perm (Fin n)) : (firstPermEquiv n).symm (i, σ) 0 = i := by
  cases n with
  | zero => exact Fin.ext (by omega)
  | succ n => exact Equiv.Perm.decomposeFin'Symm_zero i σ

@[simp] theorem firstPermEquiv_symm_succ (n : ℕ) (i : Fin (n + 1))
    (σ : Perm (Fin n)) (j : Fin n) :
    (firstPermEquiv n).symm (i, σ) j.succ = i.succAbove (σ j) := by
  cases n with
  | zero => exact j.elim0
  | succ n => exact Equiv.Perm.decomposeFin'Symm_succ i σ j

@[simp] theorem sign_firstPermEquiv_symm (n : ℕ) (i : Fin (n + 1))
    (σ : Perm (Fin n)) :
    ((firstPermEquiv n).symm (i, σ)).sign = (-1) ^ i.val * σ.sign := by
  cases n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    have hσ : σ = 1 := Subsingleton.elim _ _
    simp [firstPermEquiv, emptyTailPermEquiv, hi, hσ]
  | succ n => exact Equiv.Perm.sign_decomposeFin'Symm i σ

@[simp] theorem firstPermEquiv_fst (n : ℕ) (σ : Perm (Fin (n + 1))) :
    ((firstPermEquiv n) σ).1 = σ 0 := by
  have h := firstPermEquiv_symm_zero n ((firstPermEquiv n σ).1)
    ((firstPermEquiv n σ).2)
  simpa using h.symm

/-- The remaining permutation after fixing the first index. -/
def fixedZeroFinEquiv (n : ℕ) :
    {σ : Perm (Fin (n + 1)) // σ 0 = 0} ≃ Perm (Fin n) where
  toFun σ := ((firstPermEquiv n) σ.val).2
  invFun σ := ⟨(firstPermEquiv n).symm (0, σ), firstPermEquiv_symm_zero n 0 σ⟩
  left_inv σ := by
    apply Subtype.ext
    apply (firstPermEquiv n).injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · simpa only [firstPermEquiv_fst] using σ.property.symm
    · rfl
  right_inv σ := by simp

/-- The literal ordered-pair summand written in ordinary finite coordinates. -/
def finTerm {k : ℕ} (A : Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ)
    (σ : Perm (Fin (2 * k))) : ℂ :=
  permutationSign σ * ∏ i : Fin k,
    A (σ (PfaffianMinor.pairCol k i 0)) (σ (PfaffianMinor.pairCol k i 1))

@[simp] theorem pairCol_zero_zero (k : ℕ) :
    PfaffianMinor.pairCol (k + 1) 0 0 = 0 := by
  apply Fin.ext
  simp [PfaffianMinor.pairCol, PfaffianMinor.pairColumnEquiv, finProdFinEquiv]

@[simp] theorem pairCol_zero_one (k : ℕ) :
    PfaffianMinor.pairCol (k + 1) 0 1 = 1 := by
  apply Fin.ext
  simp [PfaffianMinor.pairCol, PfaffianMinor.pairColumnEquiv, finProdFinEquiv]

@[simp] theorem pairCol_succ (k : ℕ) (i : Fin k) (a : Fin 2) :
    PfaffianMinor.pairCol (k + 1) i.succ a =
      (PfaffianMinor.pairCol k i a).succ.succ := by
  apply Fin.ext
  simp [PfaffianMinor.pairCol, PfaffianMinor.pairColumnEquiv, finProdFinEquiv]
  omega

/-- Changing the indexing conjugates permutations and preserves the signed term. -/
theorem term_eq_finTerm {k : ℕ}
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ)
    (σ : Perm (PairedIndex k)) :
    term (A.submatrix (PfaffianMinor.pairColumnEquiv k)
      (PfaffianMinor.pairColumnEquiv k)) σ =
      finTerm A ((PfaffianMinor.pairColumnEquiv k).permCongr σ) := by
  simp [term, finTerm, permutationSign, Equiv.Perm.sign_permCongr,
    Equiv.permCongr_apply, PfaffianMinor.pairCol]

@[simp] theorem permutationSign_firstPermEquiv_symm (n : ℕ) (i : Fin (n + 1))
    (σ : Perm (Fin n)) :
    permutationSign ((firstPermEquiv n).symm (i, σ)) =
      (-1 : ℂ) ^ i.val * permutationSign σ := by
  simp [permutationSign, sign_firstPermEquiv_symm]

/-- The first pair extracts its partner; every remaining row keeps its order. -/
theorem finTerm_firstPair {k : ℕ}
    (A : Matrix (Fin (2 * (k + 1))) (Fin (2 * (k + 1))) ℂ)
    (j : Fin (2 * k + 1)) (σ : Perm (Fin (2 * k))) :
    finTerm A ((firstPermEquiv (2 * k + 1)).symm
      (0, (firstPermEquiv (2 * k)).symm (j, σ))) =
      (-1 : ℂ) ^ j.val * A 0 j.succ *
        finTerm (A.submatrix (fun i ↦ (j.succAbove i).succ)
          (fun i ↦ (j.succAbove i).succ)) σ := by
  simp only [finTerm, Fin.prod_univ_succ, pairCol_zero_zero, pairCol_zero_one,
    pairCol_succ, permutationSign_firstPermEquiv_symm,
    firstPermEquiv_symm_zero, firstPermEquiv_symm_succ,
    Fin.succAbove_zero, Matrix.submatrix_apply]
  rw [show (1 : Fin (2 * (k + 1))) = (0 : Fin (2 * k + 1)).succ from rfl,
    firstPermEquiv_symm_succ, firstPermEquiv_symm_zero, Fin.succAbove_zero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  ring

end Paper.PfaffianBridge
