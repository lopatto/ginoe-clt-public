/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! # The between-block linear maps for real Schur coordinates

Only the needed scalar/two-dimensional blocks are used. No assertion about
nonlinear Schur charts or their full Jacobian is made here.
-/

@[expose] public section
open scoped Matrix Kronecker BigOperators

namespace Paper.Spectral

variable {R : Type*} [CommRing R]

def scalarBlock (a : R) : Matrix (Fin 1) (Fin 1) R := fun _ _ => a

def schurBlock (a b c : R) : Matrix (Fin 2) (Fin 2) R := !![a, b; -c, a]

/-- Column-major coordinate matrix of X ↦ XB - AX. -/
def sylvesterMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) R :=
  Bᵀ ⊗ₖ (1 : Matrix (Fin m) (Fin m) R) -
    (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ A

lemma sylvesterMatrix_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin m) (Fin n) R) :
    sylvesterMatrix A B *ᵥ Matrix.vec X = Matrix.vec (X * B - A * X) := by
  simp only [sylvesterMatrix, Matrix.sub_mulVec, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_transpose, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.vec_sub]

lemma det_sylvester_scalar_scalar (a d : R) :
    (sylvesterMatrix (scalarBlock a) (scalarBlock d)).det = d - a := by
  rw [← Matrix.det_submatrix_equiv_self (finProdFinEquiv.symm), Matrix.det_fin_one]
  simp [sylvesterMatrix, scalarBlock, Matrix.kroneckerMap_apply]

lemma det_sylvester_scalar_block (a d e f : R) :
    (sylvesterMatrix (scalarBlock a) (schurBlock d e f)).det = (d - a) ^ 2 + e * f := by
  let p : Fin 2 × Fin 1 ≃ Fin 2 := finProdFinEquiv
  have he : (sylvesterMatrix (scalarBlock a) (schurBlock d e f)).submatrix p.symm p.symm =
      !![d - a, -f; e, d - a] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      norm_num [sylvesterMatrix, scalarBlock, schurBlock, Matrix.kroneckerMap_apply,
        Matrix.submatrix_apply, p, finProdFinEquiv, Fin.divNat, Fin.modNat]
  rw [← Matrix.det_submatrix_equiv_self p.symm, he, Matrix.det_fin_two]
  change (d - a) * (d - a) - (-f) * e = (d - a) ^ 2 + e * f
  ring

lemma det_sylvester_block_scalar (a b c d : R) :
    (sylvesterMatrix (schurBlock a b c) (scalarBlock d)).det = (d - a) ^ 2 + b * c := by
  let p : Fin 1 × Fin 2 ≃ Fin 2 := finProdFinEquiv
  have he : (sylvesterMatrix (schurBlock a b c) (scalarBlock d)).submatrix p.symm p.symm =
      !![d - a, -b; c, d - a] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      norm_num [sylvesterMatrix, scalarBlock, schurBlock, Matrix.kroneckerMap_apply,
        Matrix.submatrix_apply, p, finProdFinEquiv, Fin.divNat, Fin.modNat]
  rw [← Matrix.det_submatrix_equiv_self p.symm, he, Matrix.det_fin_two]
  change (d - a) * (d - a) - (-b) * c = (d - a) ^ 2 + b * c
  ring

lemma det_sylvester_block_block (a b c d e f : R) :
    (sylvesterMatrix (schurBlock a b c) (schurBlock d e f)).det =
      ((d - a) ^ 2 + b * c + e * f) ^ 2 - 4 * b * c * e * f := by
  let p : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  have he : (sylvesterMatrix (schurBlock a b c) (schurBlock d e f)).submatrix p.symm p.symm =
      !![d - a, -b, -f, 0; c, d - a, 0, -f;
        e, 0, d - a, -b; 0, e, c, d - a] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      norm_num [sylvesterMatrix, schurBlock, Matrix.kroneckerMap_apply,
        Matrix.submatrix_apply, p, finProdFinEquiv, Fin.divNat, Fin.modNat]
  rw [← Matrix.det_submatrix_equiv_self p.symm, he, Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply,
    show (1 : Fin 4).succAbove (2 : Fin 3) = 3 by decide,
    show (2 : Fin 4).succAbove (2 : Fin 3) = 3 by decide]
  ring

end Paper.Spectral
