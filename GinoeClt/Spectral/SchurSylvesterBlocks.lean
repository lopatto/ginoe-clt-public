/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SylvesterBlocks
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Sum

/-! # Exact recursive Sylvester factors for upper Schur blocks

The same row/column coordinate permutation is used throughout, so signed
determinants are preserved. No noncollision or invertibility assumption is used.
-/

@[expose] public section
open scoped Matrix Kronecker

namespace Paper.Spectral

variable {R : Type*} [CommRing R]
variable {d m n : ℕ}

theorem sylvester_fromBlocks_reindex
    (B : Matrix (Fin d) (Fin d) R)
    (D₁ : Matrix (Fin m) (Fin m) R) (D₂ : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin m) (Fin n) R) :
    ((Bᵀ ⊗ₖ (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R)) -
      ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ Matrix.fromBlocks D₁ U 0 D₂)).submatrix
        (Equiv.prodSumDistrib (Fin d) (Fin m) (Fin n)).symm
        (Equiv.prodSumDistrib (Fin d) (Fin m) (Fin n)).symm =
      Matrix.fromBlocks (sylvesterMatrix D₁ B)
        (-((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ U)) 0
        (sylvesterMatrix D₂ B) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩ | ⟨i₁, i₂⟩ <;>
    rcases j with ⟨j₁, j₂⟩ | ⟨j₁, j₂⟩ <;>
      simp [sylvesterMatrix, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply]

theorem det_sylvester_fromBlocks
    (B : Matrix (Fin d) (Fin d) R)
    (D₁ : Matrix (Fin m) (Fin m) R) (D₂ : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin m) (Fin n) R) :
    ((Bᵀ ⊗ₖ (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R)) -
      ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ Matrix.fromBlocks D₁ U 0 D₂)).det =
        (sylvesterMatrix D₁ B).det * (sylvesterMatrix D₂ B).det := by
  rw [← Matrix.det_submatrix_equiv_self
    (Equiv.prodSumDistrib (Fin d) (Fin m) (Fin n)).symm]
  rw [sylvester_fromBlocks_reindex, Matrix.det_fromBlocks_zero₂₁]

end Paper.Spectral
