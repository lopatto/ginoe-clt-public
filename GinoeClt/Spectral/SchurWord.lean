/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurCellCoordinates
public import GinoeClt.Spectral.SchurHeadDeterminants
public import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.Abel

/-! Fixed scalar/pair block words in ordinary physical matrix coordinates. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

def schurOmegaStep {d m : ℕ}
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    (SchurStepIndex (Fin d) (Fin m) → ℝ) →ₗ[ℝ]
      Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ where
  toFun x := Matrix.fromBlocks (ω (schurHeadInput x)) (-(schurLowerInput x)ᵀ)
    (schurLowerInput x) (η (schurTailInput x))
  map_add' x y := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [map_add, Matrix.fromBlocks]
    · simp [map_add, Matrix.fromBlocks, Matrix.transpose_apply]
      abel
    · simp [map_add, Matrix.fromBlocks]
    · simp [map_add, Matrix.fromBlocks]
  map_smul' r x := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [map_smul, Matrix.fromBlocks, Matrix.transpose_apply]

def schurParameterStep {d m : ℕ}
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    (SchurStepIndex (Fin d) (Fin m) → ℝ) →ₗ[ℝ]
      Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ where
  toFun x := Matrix.fromBlocks (K (schurHeadInput x)) (schurUpperInput x) 0
    (L (schurTailInput x))
  map_add' x y := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [map_add, Matrix.fromBlocks]
  map_smul' r x := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [map_smul, Matrix.fromBlocks]

def schurOmegaPhysical (d m : ℕ)
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    (Fin (d + m) × Fin (d + m) → ℝ) →ₗ[ℝ]
      Matrix (Fin (d + m)) (Fin (d + m)) ℝ :=
  (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).toLinearMap.comp
    ((schurOmegaStep ω η).comp (schurCellCoordinateEquiv ℝ d m).toLinearMap)

def schurParameterPhysical (d m : ℕ)
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    (Fin (d + m) × Fin (d + m) → ℝ) →ₗ[ℝ]
      Matrix (Fin (d + m)) (Fin (d + m)) ℝ :=
  (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).toLinearMap.comp
    ((schurParameterStep K L).comp (schurCellCoordinateEquiv ℝ d m).toLinearMap)

theorem schurOmegaStep_skew {d m : ℕ}
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hω : ∀ h, (ω h)ᵀ = -(ω h)) (hη : ∀ t, (η t)ᵀ = -(η t))
    (x : SchurStepIndex (Fin d) (Fin m) → ℝ) :
    (schurOmegaStep ω η x)ᵀ = -(schurOmegaStep ω η x) := by
  change (Matrix.fromBlocks _ _ _ _)ᵀ = -Matrix.fromBlocks _ _ _ _
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg,
    hω, hη, Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg]

theorem reindex_preserves_skew {ι κ : Type*} (e : ι ≃ κ)
    (M : Matrix ι ι ℝ) (hM : Mᵀ = -M) :
    (M.reindex e e)ᵀ = -(M.reindex e e) := by
  ext i j
  exact congrArg (fun B : Matrix ι ι ℝ => B (e.symm i) (e.symm j)) hM

theorem schurOmegaPhysical_skew (d m : ℕ)
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hω : ∀ h, (ω h)ᵀ = -(ω h)) (hη : ∀ t, (η t)ᵀ = -(η t))
    (x : Fin (d + m) × Fin (d + m) → ℝ) :
    (schurOmegaPhysical d m ω η x)ᵀ = -(schurOmegaPhysical d m ω η x) :=
  reindex_preserves_skew finSumFinEquiv _
    (schurOmegaStep_skew ω η hω hη (schurCellCoordinateEquiv ℝ d m x))

/-- False is a scalar block, true a normalized pair block. -/
def schurWordSize : List Bool → ℕ
  | [] => 0
  | false :: w => 1 + schurWordSize w
  | true :: w => 2 + schurWordSize w

/-- Actual skew matrix assembled from the independent angular slots of the word. -/
def schurWordOmega : (w : List Bool) →
    (Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) →ₗ[ℝ]
      Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ
  | [] => 0
  | false :: w => schurOmegaPhysical 1 (schurWordSize w) 0 (schurWordOmega w)
  | true :: w => schurOmegaPhysical 2 (schurWordSize w) pairHeadOmega (schurWordOmega w)

/-- Actual free Schur entries, with pair blocks [a b; -c a]. -/
def schurWordParameter : (w : List Bool) →
    (Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) →ₗ[ℝ]
      Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ
  | [] => 0
  | false :: w => schurParameterPhysical 1 (schurWordSize w)
      scalarHeadParameter (schurWordParameter w)
  | true :: w => schurParameterPhysical 2 (schurWordSize w)
      pairHeadParameter (schurWordParameter w)

theorem schurWordOmega_skew (w : List Bool) :
    ∀ x, (schurWordOmega w x)ᵀ = -(schurWordOmega w x) := by
  induction w with
  | nil => intro x; simp [schurWordOmega]
  | cons b w ih =>
    cases b <;> intro x
    · exact schurOmegaPhysical_skew 1 (schurWordSize w) 0 (schurWordOmega w)
        (by intro h; simp) ih x
    · exact schurOmegaPhysical_skew 2 (schurWordSize w) pairHeadOmega (schurWordOmega w)
        (fun h => pairSkew_transpose (h (1, 1))) ih x

end Paper.Spectral
