/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Probability.OrthogonalInvariance

/-! # Orthogonal conjugation preserves the actual multiplicity counts -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

lemma charpoly_orthogonal_conj (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (M : SampleSpace n) :
    ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    (Matrix.mem_orthogonalGroup_iff' (Fin (n + 1)) ℝ).mp Q.property, Matrix.one_mul]

lemma scaledMatrix_orthogonal_conj (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (M : SampleSpace n) :
    scaledMatrix n ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ) =
      (Q : Matrix _ _ ℝ) * scaledMatrix n M * (Q : Matrix _ _ ℝ)ᵀ := by
  simp only [scaledMatrix, Matrix.smul_mul, Matrix.mul_smul]

theorem eigenvalues_orthogonal_conj (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (M : SampleSpace n) :
    eigenvalues n ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ) = eigenvalues n M := by
  simp only [eigenvalues, scaledMatrix_orthogonal_conj, charpoly_orthogonal_conj]

theorem count_orthogonal_conj (A : Set ℂ) (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (M : SampleSpace n) :
    count A n ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ) = count A n M := by
  simp only [count, eigenvalues_orthogonal_conj]

theorem statistic_orthogonal_conj (A : Set ℂ) (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (M : SampleSpace n) :
    statistic A n ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ) = statistic A n M := by
  simp only [statistic, count_orthogonal_conj]

end Paper.Spectral
