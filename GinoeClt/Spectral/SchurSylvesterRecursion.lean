/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurSylvesterBlocks
public import GinoeClt.Spectral.SchurRootFactors
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Recursive Sylvester factors in the actual Fin-indexed Schur matrices -/

@[expose] public section
open scoped Matrix Kronecker

namespace Paper.Spectral

theorem det_sylvester_reindexed_fromBlocks {R : Type*} [CommRing R] {d m n : ℕ}
    (B : Matrix (Fin d) (Fin d) R)
    (D₁ : Matrix (Fin m) (Fin m) R) (D₂ : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin m) (Fin n) R) :
    (sylvesterMatrix
      ((Matrix.fromBlocks D₁ U 0 D₂).reindex finSumFinEquiv finSumFinEquiv) B).det =
        (sylvesterMatrix D₁ B).det * (sylvesterMatrix D₂ B).det := by
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  let ep := (Equiv.refl (Fin d)).prodCongr e
  have hI : Matrix.reindex e e
      (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R) = 1 := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply]
  have hS : sylvesterMatrix ((Matrix.fromBlocks D₁ U 0 D₂).reindex e e) B =
      Matrix.reindex ep ep
        ((Bᵀ ⊗ₖ (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R)) -
          ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ Matrix.fromBlocks D₁ U 0 D₂)) := by
    unfold sylvesterMatrix
    rw [← hI]
    simp only [Matrix.kroneckerMap_reindex_right]
    rfl
  change (sylvesterMatrix ((Matrix.fromBlocks D₁ U 0 D₂).reindex e e) B).det = _
  rw [hS, Matrix.det_reindex_self]
  exact det_sylvester_fromBlocks B D₁ D₂ U


theorem sylvester_reindexed_fromBlocks_injective {d m n : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ)
    (D₁ : Matrix (Fin m) (Fin m) ℝ) (D₂ : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin n) ℝ)
    (h₁ : (sylvesterMatrix D₁ B).det ≠ 0)
    (h₂ : (sylvesterMatrix D₂ B).det ≠ 0) :
    Function.Injective (fun X : Matrix (Fin (m + n)) (Fin d) ℝ =>
      X * B - ((Matrix.fromBlocks D₁ U 0 D₂).reindex finSumFinEquiv finSumFinEquiv) * X) := by
  apply sylvester_injective_of_det_ne_zero
  rw [det_sylvester_reindexed_fromBlocks]
  exact mul_ne_zero h₁ h₂

theorem sylvester_reindexed_fromBlocks_kernel {d m n : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ)
    (D₁ : Matrix (Fin m) (Fin m) ℝ) (D₂ : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin n) ℝ)
    (h₁ : (sylvesterMatrix D₁ B).det ≠ 0)
    (h₂ : (sylvesterMatrix D₂ B).det ≠ 0)
    (X : Matrix (Fin (m + n)) (Fin d) ℝ)
    (hX : ((Matrix.fromBlocks D₁ U 0 D₂).reindex finSumFinEquiv finSumFinEquiv) * X = X * B) :
    X = 0 := by
  apply sylvester_reindexed_fromBlocks_injective B D₁ D₂ U h₁ h₂
  simp only [hX, sub_self, Matrix.zero_mul, Matrix.mul_zero]


end Paper.Spectral
