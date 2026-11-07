/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurBlockAssembly

/-! # Normalized real Schur decomposition

The target shape is the explicit entrywise proposition in SchurBlockAssembly.
It concerns orthogonal similarity of arbitrary real matrices, not charts,
uniqueness, Jacobians, or any random-matrix law.
-/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

lemma upperBlockMatrix_eq_of_corner {d m : ℕ}
    (M : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) (hdN : d ≤ d + m)
    (B : Matrix (Fin d) (Fin d) ℝ)
    (htop : M.submatrix (Fin.castLE hdN) (Fin.castLE hdN) = B)
    (hlo : ∀ (i : Fin (d + m)) (j : Fin d), d ≤ i.val → M i (Fin.castLE hdN j) = 0) :
    M = upperBlockMatrix B (M.submatrix (Fin.castAdd m) (Fin.natAdd d))
      (M.submatrix (Fin.natAdd d) (Fin.natAdd d)) := by
  have hemb : ∀ j : Fin d, Fin.castLE hdN j = Fin.castAdd m j := fun _ => rfl
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have hh := congrArg (fun T : Matrix (Fin d) (Fin d) ℝ => T i j) htop
    simpa only [Matrix.submatrix_apply, hemb, upperBlockMatrix_left_left] using hh
  · simp only [upperBlockMatrix_left_right, Matrix.submatrix_apply]
  · rw [upperBlockMatrix_right_left]
    simpa only [hemb] using hlo (Fin.natAdd d i) j (by simp only [Fin.val_natAdd]; omega)
  · simp only [upperBlockMatrix_right_right, Matrix.submatrix_apply]

lemma exists_schur_upperBlocks {d m : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (hB : IsNormalizedQuasiTriangular B)
    (hD : ∃ R : Matrix.orthogonalGroup (Fin m) ℝ,
      IsNormalizedQuasiTriangular ((R : Matrix (Fin m) (Fin m) ℝ)ᵀ * D * (R : Matrix (Fin m) (Fin m) ℝ))) :
    ∃ Q : Matrix.orthogonalGroup (Fin (d + m)) ℝ,
      IsNormalizedQuasiTriangular
        ((Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)ᵀ * upperBlockMatrix B U D * (Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)) := by
  classical
  obtain ⟨R, hR⟩ := hD
  let P0 : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ :=
    Matrix.fromBlocks 1 0 0 (R : Matrix (Fin m) (Fin m) ℝ)
  let ρ : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ ≃+*
      Matrix (Fin (d + m)) (Fin (d + m)) ℝ :=
    Matrix.reindexRingEquiv ℝ finSumFinEquiv
  let P := ρ P0
  have hP0 : P0 * P0ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff _ _).mp (orthogonal_fromBlocks_identity (ι := Fin d) R)
  have hP : P ∈ Matrix.orthogonalGroup (Fin (d + m)) ℝ := by
    apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
    change ρ P0 * ρ P0ᵀ = 1
    rw [← map_mul, hP0, map_one]
  have hconj : Pᵀ * upperBlockMatrix B U D * P =
      upperBlockMatrix B (U * (R : Matrix (Fin m) (Fin m) ℝ)) ((R : Matrix (Fin m) (Fin m) ℝ)ᵀ * D * (R : Matrix (Fin m) (Fin m) ℝ)) := by
    change ρ P0ᵀ * ρ (Matrix.fromBlocks B U 0 D) * ρ P0 =
      ρ (Matrix.fromBlocks B (U * (R : Matrix (Fin m) (Fin m) ℝ)) 0 ((R : Matrix (Fin m) (Fin m) ℝ)ᵀ * D * (R : Matrix (Fin m) (Fin m) ℝ)))
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (orthogonal_tail_conjugation B U D R)
  refine ⟨⟨P, hP⟩, ?_⟩
  change IsNormalizedQuasiTriangular (Pᵀ * upperBlockMatrix B U D * P)
  rw [hconj]
  exact hB.upperBlocks hR (U * (R : Matrix (Fin m) (Fin m) ℝ))

lemma realSchur_step {N d m : ℕ} (hsize : d + m = N)
    (A : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix.orthogonalGroup (Fin N) ℝ)
    (hdN : d ≤ N) (B : Matrix (Fin d) (Fin d) ℝ)
    (hB : IsNormalizedQuasiTriangular B)
    (htop : ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ)).submatrix
      (Fin.castLE hdN) (Fin.castLE hdN) = B)
    (hlo : ∀ (i : Fin N) (j : Fin d), d ≤ i.val →
      ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ)) i (Fin.castLE hdN j) = 0)
    (hTail : ∀ D : Matrix (Fin m) (Fin m) ℝ, ∃ R : Matrix.orthogonalGroup (Fin m) ℝ,
      IsNormalizedQuasiTriangular ((R : Matrix (Fin m) (Fin m) ℝ)ᵀ * D * (R : Matrix (Fin m) (Fin m) ℝ))) :
    ∃ R : Matrix.orthogonalGroup (Fin N) ℝ,
      IsNormalizedQuasiTriangular ((R : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (R : Matrix (Fin N) (Fin N) ℝ)) := by
  subst N
  let M := (Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)ᵀ * A * (Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)
  let U := M.submatrix (Fin.castAdd m) (Fin.natAdd d)
  let D := M.submatrix (Fin.natAdd d) (Fin.natAdd d)
  have hM : M = upperBlockMatrix B U D :=
    upperBlockMatrix_eq_of_corner M hdN B htop hlo
  obtain ⟨P, hP⟩ := exists_schur_upperBlocks B U D hB (hTail D)
  refine ⟨Q * P, ?_⟩
  change IsNormalizedQuasiTriangular
    (((Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) *
      (P : Matrix (Fin (d + m)) (Fin (d + m)) ℝ))ᵀ * A * ((Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) * (P : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)))
  have heq : (((Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) *
      (P : Matrix (Fin (d + m)) (Fin (d + m)) ℝ))ᵀ * A * ((Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) * (P : Matrix (Fin (d + m)) (Fin (d + m)) ℝ))) =
      (P : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)ᵀ * M * (P : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, M]
  rw [heq, hM]
  exact hP

/-- Every real square matrix, including defective matrices, is orthogonally
similar to a normalized real quasi-triangular matrix. The active 2×2 blocks
have equal diagonal entries and ordered off-diagonals [b;-c] with 0<c≤b. -/
theorem exists_normalized_real_schur (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ,
      IsNormalizedQuasiTriangular
        ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ)) := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero =>
      exact ⟨1, normalizedQuasiTriangular_empty _⟩
    | succ n =>
      obtain hfirst | hfirst := exists_source_first_block n A
      · obtain ⟨a, Q, hentry, hlo⟩ := hfirst
        let B : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => a
        have hdN : 1 ≤ n + 1 := by omega
        have htop : ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A *
            (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).submatrix
              (Fin.castLE hdN) (Fin.castLE hdN) = B := by
          ext i j
          fin_cases i
          fin_cases j
          exact hentry
        have hlo' : ∀ (i : Fin (n + 1)) (j : Fin 1), 1 ≤ i.val →
            ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A *
              (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) i (Fin.castLE hdN j) = 0 := by
          intro i j hi
          fin_cases j
          exact hlo i hi
        exact realSchur_step (d := 1) (m := n) (by omega) A Q hdN B
          (normalizedQuasiTriangular_singleton B) htop hlo' (fun D => ih n (by omega) D)
      · obtain ⟨h2, a, b, c, hc, hcb, Q, htop, hlo⟩ := hfirst
        exact realSchur_step (d := 2) (m := n + 1 - 2) (by omega) A Q h2
          !![a, b; -c, a] (normalizedQuasiTriangular_pair a b c hc hcb)
          htop hlo (fun D => ih (n + 1 - 2) (by omega) D)

end Paper.Spectral
