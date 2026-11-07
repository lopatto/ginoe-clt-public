/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurStepCoordinates
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Logic.Equiv.Fin.Basic

/-! The Schur step is a permutation of actual column-row matrix coordinates. -/
@[expose] public section
open scoped Matrix

namespace Paper.Spectral

def schurStepSumCellEquiv (ι κ : Type*) :
    SchurStepIndex ι κ ≃ (ι ⊕ κ) × (ι ⊕ κ) where
  toFun
    | .inl (j, i) => (.inl j, .inr i)
    | .inr (.inl (j, i)) => (.inl j, .inl i)
    | .inr (.inr (.inl (j, i))) => (.inr j, .inr i)
    | .inr (.inr (.inr (j, i))) => (.inr j, .inl i)
  invFun
    | (.inl j, .inr i) => .inl (j, i)
    | (.inl j, .inl i) => .inr (.inl (j, i))
    | (.inr j, .inr i) => .inr (.inr (.inl (j, i)))
    | (.inr j, .inl i) => .inr (.inr (.inr (j, i)))
  left_inv p := by
    rcases p with p | p | p | p <;> rfl
  right_inv p := by
    rcases p with ⟨j | j, i | i⟩ <;> rfl

def schurCellEquiv (d m : ℕ) :
    SchurStepIndex (Fin d) (Fin m) ≃ Fin (d + m) × Fin (d + m) :=
  (schurStepSumCellEquiv (Fin d) (Fin m)).trans
    (finSumFinEquiv.prodCongr finSumFinEquiv)

def schurCellCoordinateEquiv (R : Type*) [Semiring R] (d m : ℕ) :
    (Fin (d + m) × Fin (d + m) → R) ≃ₗ[R]
      (SchurStepIndex (Fin d) (Fin m) → R) :=
  LinearEquiv.funCongrLeft R R (schurCellEquiv d m)

@[simp] theorem schurCellCoordinateEquiv_apply {R : Type*} [Semiring R]
    (d m : ℕ) (x : Fin (d + m) × Fin (d + m) → R)
    (p : SchurStepIndex (Fin d) (Fin m)) :
    schurCellCoordinateEquiv R d m x p = x (schurCellEquiv d m p) := rfl

theorem schurBlockCoordinates_sumCells {R ι κ : Type*}
    (M : Matrix (ι ⊕ κ) (ι ⊕ κ) R) :
    schurBlockCoordinates M = fun p => Matrix.vec M (schurStepSumCellEquiv ι κ p) := by
  funext p
  rcases p with p | p | p | p <;> rfl

theorem schurBlockCoordinates_physicalCells {R : Type*} [Semiring R]
    (d m : ℕ) (M : Matrix (Fin (d + m)) (Fin (d + m)) R) :
    schurBlockCoordinates (M.submatrix finSumFinEquiv finSumFinEquiv) =
      schurCellCoordinateEquiv R d m (Matrix.vec M) := by
  funext p
  rcases p with p | p | p | p <;> rfl

/-- The inverse of ordinary vectorization is the literal column-row unflattening. -/
def matrixColumnLinearEquiv (R : Type*) [Semiring R] (ι κ : Type*) :
    Matrix κ ι R ≃ₗ[R] (ι × κ → R) where
  toFun := Matrix.vec
  invFun x := Matrix.of (fun i j => x (j, i))
  left_inv M := rfl
  right_inv x := by funext p; rcases p with ⟨j, i⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem matrixColumnLinearEquiv_symm_apply {R : Type*} [Semiring R]
    (ι κ : Type*) (x : ι × κ → R) (i : κ) (j : ι) :
    (matrixColumnLinearEquiv R ι κ).symm x i j = x (j, i) := rfl

def schurMatrixCoordinateEquiv (R : Type*) [Semiring R] (d m : ℕ) :
    Matrix (Fin (d + m)) (Fin (d + m)) R ≃ₗ[R]
      (SchurStepIndex (Fin d) (Fin m) → R) :=
  (matrixColumnLinearEquiv R (Fin (d + m)) (Fin (d + m))).trans
    (schurCellCoordinateEquiv R d m)

theorem schurMatrixCoordinateEquiv_apply {R : Type*} [Semiring R]
    (d m : ℕ) (M : Matrix (Fin (d + m)) (Fin (d + m)) R) :
    schurMatrixCoordinateEquiv R d m M =
      schurBlockCoordinates (M.submatrix finSumFinEquiv finSumFinEquiv) :=
  (schurBlockCoordinates_physicalCells d m M).symm

theorem det_schurCellCoordinate_conj {R : Type*} [CommRing R] (d m : ℕ)
    (L : (Fin (d + m) × Fin (d + m) → R) →ₗ[R]
      (Fin (d + m) × Fin (d + m) → R)) :
    LinearMap.det ((schurCellCoordinateEquiv R d m).toLinearMap ∘ₗ L ∘ₗ
      (schurCellCoordinateEquiv R d m).symm.toLinearMap) = LinearMap.det L :=
  LinearMap.det_conj L (schurCellCoordinateEquiv R d m)

end Paper.Spectral
