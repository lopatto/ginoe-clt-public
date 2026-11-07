/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurRootFactors
public import GinoeClt.Spectral.SchurBlockAssembly

/-! Orthogonal Schur-block intertwiners under actual Sylvester separation. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

/-- An orthogonal intertwiner between separated upper-block matrices must be
block diagonal. The hypothesis is the literal cross-block Sylvester determinant. -/
theorem orthogonal_schur_intertwiner_blocks {d m : ℕ}
    (B B' : Matrix (Fin d) (Fin d) ℝ) (D D' : Matrix (Fin m) (Fin m) ℝ)
    (U U' : Matrix (Fin d) (Fin m) ℝ)
    (Q : Matrix.orthogonalGroup (Fin d ⊕ Fin m) ℝ)
    (hsep : (sylvesterMatrix D B').det ≠ 0)
    (hT : Matrix.fromBlocks B U 0 D * (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) =
      (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) * Matrix.fromBlocks B' U' 0 D') :
    ∃ E : Matrix.orthogonalGroup (Fin d) ℝ,
      ∃ R : Matrix.orthogonalGroup (Fin m) ℝ,
        (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) =
          Matrix.fromBlocks (E : Matrix (Fin d) (Fin d) ℝ) 0 0
            (R : Matrix (Fin m) (Fin m) ℝ) ∧
          B * (E : Matrix (Fin d) (Fin d) ℝ) = (E : Matrix (Fin d) (Fin d) ℝ) * B' ∧
          D * (R : Matrix (Fin m) (Fin m) ℝ) = (R : Matrix (Fin m) (Fin m) ℝ) * D' ∧
          U * (R : Matrix (Fin m) (Fin m) ℝ) = (E : Matrix (Fin d) (Fin d) ℝ) * U' := by
  let E := (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ).toBlocks₁₁
  let V := (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ).toBlocks₁₂
  let X := (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ).toBlocks₂₁
  let R := (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ).toBlocks₂₂
  have hQ : (Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) = Matrix.fromBlocks E V X R :=
    (Matrix.fromBlocks_toBlocks _).symm
  have hT' : Matrix.fromBlocks B U 0 D * Matrix.fromBlocks E V X R =
      Matrix.fromBlocks E V X R * Matrix.fromBlocks B' U' 0 D' := by
    simpa only [← hQ] using hT
  have hXeq := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₂₁) hT'
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at hXeq
  have hX : X = 0 := by
    apply sylvester_injective_of_det_ne_zero D B' hsep
    simp only [hXeq, sub_self, Matrix.zero_mul, Matrix.mul_zero]
  have hQQt : Matrix.fromBlocks E V X R * (Matrix.fromBlocks E V X R)ᵀ = 1 := by
    simpa only [← hQ] using (Matrix.mem_orthogonalGroup_iff _ _).mp Q.property
  rw [hX] at hQQt
  have hR := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₂₂) hQQt
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.transpose_zero, Matrix.zero_mul, zero_add] at hR
  have hRorth : R ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
    apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
    simpa only [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂] using hR
  have hRtR : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hRorth
  have hVR := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₁₂) hQQt
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₂, ← Matrix.fromBlocks_one, Matrix.transpose_zero, Matrix.mul_zero, zero_add] at hVR
  have hV : V = 0 := by
    calc
      V = V * (Rᵀ * R) := by rw [hRtR, Matrix.mul_one]
      _ = (V * Rᵀ) * R := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hVR, Matrix.zero_mul]
  rw [hV] at hQQt
  have hE := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₁₁) hQQt
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.transpose_zero, Matrix.zero_mul, add_zero] at hE
  have hEorth : E ∈ Matrix.orthogonalGroup (Fin d) ℝ :=
    by
      apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
      simpa only [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁] using hE
  refine ⟨⟨E, hEorth⟩, ⟨R, hRorth⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [hX, hV] using hQ
  · have h := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₁₁) hT'
    simpa only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
      hX, hV, Matrix.mul_zero, Matrix.zero_mul, add_zero] using h
  · have h := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₂₂) hT'
    simpa only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
      hX, hV, Matrix.mul_zero, Matrix.zero_mul, zero_add] using h
  · have h := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₁₂) hT'
    simpa only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂,
      hX, hV, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] using h

end Paper.Spectral
