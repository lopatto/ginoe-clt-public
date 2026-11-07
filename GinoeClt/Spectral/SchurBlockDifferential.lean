/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SylvesterBlocks
public import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Abel

/-! # The recursive Schur differential block identity

The lower-left block is the genuine Sylvester map, independent of all other
differential coordinates. This algebraic identity is not a full Jacobian formula.
-/

@[expose] public section
open scoped Matrix

namespace Paper.Spectral

theorem schur_commutator_fromBlocks {R ι κ : Type*} [CommRing R]
    [Fintype ι] [Fintype κ]
    (B omega KB : Matrix ι ι R) (D eta KD : Matrix κ κ R)
    (U KU : Matrix ι κ R) (X : Matrix κ ι R) :
    Matrix.fromBlocks KB KU 0 KD +
        Matrix.fromBlocks omega (-Xᵀ) X eta * Matrix.fromBlocks B U 0 D -
        Matrix.fromBlocks B U 0 D * Matrix.fromBlocks omega (-Xᵀ) X eta =
      Matrix.fromBlocks
        (KB + omega * B - B * omega - U * X)
        (KU + omega * U - Xᵀ * D + B * Xᵀ - U * eta)
        (X * B - D * X)
        (KD + X * U + eta * D - D * eta) := by
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.neg_mul, Matrix.mul_neg, add_zero, zero_add]
  congr 1 <;> abel

/-- Splitting a tail Schur block makes its rectangular Sylvester map triangular. -/
theorem sylvester_fromBlocks {R ι κ ν : Type*} [CommRing R]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (B : Matrix ν ν R) (D₁ : Matrix ι ι R) (D₂ : Matrix κ κ R)
    (U : Matrix ι κ R) (X₁ : Matrix ι ν R) (X₂ : Matrix κ ν R) :
    Matrix.of (Sum.elim X₁ X₂) * B -
        Matrix.fromBlocks D₁ U 0 D₂ * Matrix.of (Sum.elim X₁ X₂) =
      Matrix.of (Sum.elim (X₁ * B - D₁ * X₁ - U * X₂) (X₂ * B - D₂ * X₂)) := by
  ext i j
  cases i <;> simp [Sum.elim, Matrix.mul_apply, Fintype.sum_sum_type]; ring

end Paper.Spectral
