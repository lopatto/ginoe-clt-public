/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurWordRoots
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! The source first-block construction for a specified actual characteristic root. -/
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate

namespace Paper.Spectral

/-- Every actual characteristic root supplies an actual nonzero complex eigenvector. -/
theorem eigenvector_of_mem_mapped_charpoly_roots (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (μ : ℂ)
    (hμ : μ ∈ (A.charpoly.map Complex.ofRealHom).roots) :
    ∃ v : Fin N → ℂ, v ≠ 0 ∧ A.map Complex.ofRealHom *ᵥ v = μ • v := by
  have hr := Polynomial.isRoot_of_mem_roots hμ
  have he : Module.End.HasEigenvalue (A.map Complex.ofRealHom).toLin' μ := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    simpa only [Matrix.charpoly_toLin', Matrix.charpoly_map] using hr
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  exact ⟨v, (Module.End.hasEigenvector_iff.mp hv).2, hv.apply_eq_smul⟩

/-- The chosen real root, rather than an unspecified eigenvalue, is the scalar head. -/
theorem prescribed_real_schur_block (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a : ℝ)
    (ha : (a : ℂ) ∈ (A.charpoly.map Complex.ofRealHom).roots) :
    ∃ Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ,
      ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A *
        (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) 0 0 = a ∧
      ∀ i : Fin (n + 1), 1 ≤ i.val →
        ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A *
          (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) i 0 = 0 := by
  obtain ⟨v, hv, he⟩ := eigenvector_of_mem_mapped_charpoly_roots (n + 1) A (a : ℂ) ha
  obtain ⟨u, hu, hue⟩ := real_eigenvector_of_real_eigenvalue A (a : ℂ) v hv he (by simp)
  exact real_eigenvalue_orthogonal_block n A a u hu hue

/-- The chosen upper root is the normalized pair head, with the exact imaginary-square relation. -/
theorem prescribed_upper_schur_block (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (μ : ℂ)
    (hμ : μ ∈ (A.charpoly.map Complex.ofRealHom).roots) (hpos : 0 < μ.im) :
    ∃ h2N : 2 ≤ N, ∃ b c : ℝ, 0 < c ∧ c ≤ b ∧ b * c = μ.im ^ 2 ∧
      ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ,
        ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A *
          (Q : Matrix (Fin N) (Fin N) ℝ)).submatrix (Fin.castLE h2N) (Fin.castLE h2N) =
            schurBlock μ.re b c ∧
        ∀ (i : Fin N) (j : Fin 2), 2 ≤ i.val →
          ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A *
            (Q : Matrix (Fin N) (Fin N) ℝ)) i (Fin.castLE h2N j) = 0 := by
  obtain ⟨v, hv, he⟩ := eigenvector_of_mem_mapped_charpoly_roots N A μ hμ
  exact nonreal_eigenvalue_orthogonal_block N A μ v hv he hpos

/-- The source pair root is exactly the prescribed eigenvalue, not just one with the same real part. -/
theorem schurRoot_eq_prescribed (μ : ℂ) (b c : ℝ) (hbc : b * c = μ.im ^ 2)
    (hpos : 0 ≤ μ.im) : schurRoot μ.re b c = μ := by
  apply Complex.ext
  · rfl
  · change Real.sqrt (b * c) = μ.im
    rw [hbc, Real.sqrt_sq hpos]

/-- Actual orthogonal similarity preserves the characteristic polynomial in every size. -/
theorem charpoly_orthogonal_similarity (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ)).charpoly =
      A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp Q.property, Matrix.one_mul]

/-- The actual tail carries exactly the remaining characteristic roots as a multiset sum. -/
theorem mapped_roots_of_orthogonal_upperBlock {d m : ℕ}
    (A : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (d + m)) ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ)
    (hA : (Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)ᵀ * A *
      (Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) = upperBlockMatrix B U D) :
    (A.charpoly.map Complex.ofRealHom).roots =
      (B.charpoly.map Complex.ofRealHom).roots + (D.charpoly.map Complex.ofRealHom).roots := by
  have h := congrArg (fun M : Matrix (Fin (d + m)) (Fin (d + m)) ℝ =>
    (M.charpoly.map Complex.ofRealHom).roots) hA
  rw [charpoly_orthogonal_similarity] at h
  exact h.trans (upperBlockMatrix_roots B U D)

end Paper.Spectral
