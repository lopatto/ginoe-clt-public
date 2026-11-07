/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurStepDeterminant
public import GinoeClt.Spectral.SchurPairJacobian

/-! # Scalar and normalized-pair head factors for the actual Schur differential -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

def scalarHeadParameter {R : Type*} [CommRing R] :
    (Fin 1 × Fin 1 → R) →ₗ[R] Matrix (Fin 1) (Fin 1) R where
  toFun h := scalarBlock (h (0, 0))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma scalarHeadParameter_apply {R : Type*} [CommRing R]
    (h : Fin 1 × Fin 1 → R) (i j : Fin 1) :
    scalarHeadParameter h i j = h (0, 0) := rfl

theorem scalarHead_coefficientMatrix {R : Type*} [CommRing R] (a : R) :
    LinearMap.toMatrix' (schurDiagonalLinearMap (scalarBlock a) 0 scalarHeadParameter) = 1 := by
  ext i j
  have hi : i = (0, 0) := Subsingleton.elim _ _
  have hj : j = (0, 0) := Subsingleton.elim _ _
  subst i
  subst j
  simp [LinearMap.toMatrix'_apply, schurDiagonalLinearMap,
    Matrix.vec]

theorem det_scalarHead {R : Type*} [CommRing R] (a : R) :
    (LinearMap.toMatrix'
      (schurDiagonalLinearMap (scalarBlock a) 0 scalarHeadParameter)).det = 1 := by
  rw [scalarHead_coefficientMatrix, Matrix.det_one]

def pairHeadOmega : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun h := pairSkew (h (1, 1))
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairSkew, add_comm]
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairSkew]

def pairHeadParameter : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun h := schurBlock (h (0, 0)) (h (0, 1)) (h (1, 0))
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [schurBlock, add_comm]
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [schurBlock]

@[simp] lemma pairHeadOmega_apply (h : Fin 2 × Fin 2 → ℝ) :
    pairHeadOmega h = pairSkew (h (1, 1)) := rfl

@[simp] lemma pairHeadParameter_apply (h : Fin 2 × Fin 2 → ℝ) :
    pairHeadParameter h = schurBlock (h (0, 0)) (h (0, 1)) (h (1, 0)) := rfl

theorem pairHead_coefficientMatrix (a b c : ℝ) :
    LinearMap.toMatrix'
        (schurDiagonalLinearMap (schurBlock a b c) pairHeadOmega pairHeadParameter) =
      (pairJacobianMatrix b c).submatrix
        (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)
        (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [LinearMap.toMatrix'_apply, schurDiagonalLinearMap, Matrix.vec,
      pairSkew, schurBlock, pairJacobianMatrix, Matrix.submatrix_apply,
      finProdFinEquiv, Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, flip]

theorem det_pairHead (a b c : ℝ) :
    (LinearMap.toMatrix'
      (schurDiagonalLinearMap (schurBlock a b c) pairHeadOmega pairHeadParameter)).det =
      2 * (b - c) := by
  rw [pairHead_coefficientMatrix, Matrix.det_submatrix_equiv_self, det_pairJacobianMatrix]


end Paper.Spectral
