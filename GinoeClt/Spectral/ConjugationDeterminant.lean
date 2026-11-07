/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Real.Basic

/-! # The exact determinant of orthogonal conjugation in matrix-entry coordinates -/

@[expose] public section
noncomputable section
open scoped Matrix Kronecker

namespace Paper.Spectral

/-- Column-major coordinates of Q M Q^T; no Frobenius or Haar convention is hidden. -/
theorem orthogonalConjugation_kronecker_action (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) (M : Matrix (Fin N) (Fin N) ℝ) :
    ((Q : Matrix (Fin N) (Fin N) ℝ) ⊗ₖ (Q : Matrix (Fin N) (Fin N) ℝ)) *ᵥ
        Matrix.vec M =
      Matrix.vec ((Q : Matrix (Fin N) (Fin N) ℝ) * M *
        (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ) := by
  rw [Matrix.kronecker_mulVec_vec]

/-- The signed determinant is one, including reflections and dimension zero. -/
theorem det_orthogonalConjugation_kronecker (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    ((Q : Matrix (Fin N) (Fin N) ℝ) ⊗ₖ (Q : Matrix (Fin N) (Fin N) ℝ)).det = 1 := by
  have hQ := (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp Q.property
  have hd := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  rw [Matrix.det_kronecker, Fintype.card_fin, ← mul_pow, hd, one_pow]

end Paper.Spectral
