/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurWordParameters

/-! The original scalar/pair Schur induction in actual fixed-word parameters. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

/-- A literal normalized word, zero angles and an actual orthogonal similarity. -/
def HasSchurWord (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ w : List Bool, ∃ h : schurWordSize w = N, ∃ p : SchurWordCells w,
    SchurWordPositive w p ∧ schurWordOmega w p = 0 ∧
      ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ,
        (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ) =
          (schurWordParameter w p).reindex (finCongr h) (finCongr h)

theorem hasSchurWord_scalar_upper {m : ℕ} (a : ℝ)
    (U : Matrix (Fin 1) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (hD : HasSchurWord m D) : HasSchurWord (1 + m) (upperBlockMatrix (scalarBlock a) U D) := by
  obtain ⟨w, hsize, t, ht, hΩ, R, hR⟩ := hD
  subst m
  have hR' : (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ * D *
      (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) = schurWordParameter w t := by
    simpa [Matrix.reindex_apply] using hR
  let p := schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))
  obtain ⟨hK, hΩp, hpos⟩ := schurWord_free_scalar w a t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)) hΩ ht
  refine ⟨false :: w, rfl, p, hpos, hΩp, schurTailOrthogonal 1 (schurWordSize w) R, ?_⟩
  rw [schurTailOrthogonal_conjugation, hR']
  refine Eq.trans hK.symm ?_
  ext i j
  rfl

theorem hasSchurWord_pair_upper {m : ℕ} (a b c : ℝ)
    (U : Matrix (Fin 2) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (hc : 0 < c) (hcb : c ≤ b) (hD : HasSchurWord m D) :
    HasSchurWord (2 + m) (upperBlockMatrix (schurBlock a b c) U D) := by
  obtain ⟨w, hsize, t, ht, hΩ, R, hR⟩ := hD
  subst m
  have hR' : (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ * D *
      (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) = schurWordParameter w t := by
    simpa [Matrix.reindex_apply] using hR
  let p := schurStepFreeCells (pairFreeInput a b c) t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))
  obtain ⟨hK, hΩp, hpos⟩ := schurWord_free_pair w a b c t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)) hΩ ht hc hcb
  refine ⟨true :: w, rfl, p, hpos, hΩp, schurTailOrthogonal 2 (schurWordSize w) R, ?_⟩
  rw [schurTailOrthogonal_conjugation, hR']
  refine Eq.trans hK.symm ?_
  ext i j
  rfl

theorem hasSchurWord_of_orthogonal_conjugation (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix.orthogonalGroup (Fin N) ℝ)
    (h : HasSchurWord N ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ))) :
    HasSchurWord N A := by
  obtain ⟨w, hsize, p, hp, hΩ, R, hR⟩ := h
  refine ⟨w, hsize, p, hp, hΩ, Q * R, ?_⟩
  change ((Q : Matrix (Fin N) (Fin N) ℝ) * (R : Matrix (Fin N) (Fin N) ℝ))ᵀ * A *
    ((Q : Matrix (Fin N) (Fin N) ℝ) * (R : Matrix (Fin N) (Fin N) ℝ)) = _
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using hR

theorem hasSchurWord_step {N d m : ℕ} (hsize : d + m = N)
    (A : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix.orthogonalGroup (Fin N) ℝ)
    (hdN : d ≤ N) (B : Matrix (Fin d) (Fin d) ℝ)
    (htop : ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ)).submatrix
      (Fin.castLE hdN) (Fin.castLE hdN) = B)
    (hlo : ∀ (i : Fin N) (j : Fin d), d ≤ i.val →
      ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ)) i (Fin.castLE hdN j) = 0)
    (hupper : ∀ (U : Matrix (Fin d) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ),
      HasSchurWord m D → HasSchurWord (d + m) (upperBlockMatrix B U D))
    (hTail : ∀ D : Matrix (Fin m) (Fin m) ℝ, HasSchurWord m D) : HasSchurWord N A := by
  subst N
  apply hasSchurWord_of_orthogonal_conjugation (d + m) A Q
  let M := (Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)ᵀ * A *
    (Q : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)
  let U := M.submatrix (Fin.castAdd m) (Fin.natAdd d)
  let D := M.submatrix (Fin.natAdd d) (Fin.natAdd d)
  have hM : M = upperBlockMatrix B U D := upperBlockMatrix_eq_of_corner M hdN B htop hlo
  change HasSchurWord (d + m) M
  rw [hM]
  exact hupper U D (hTail D)

/-- Every real matrix has actual normalized word parameters, including all
zero, repeated-root and defective cases. No sector order or uniqueness is claimed. -/
theorem exists_normalized_schur_word (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) : HasSchurWord N A := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero =>
      refine ⟨[], rfl, 0, trivial, ?_, 1, ?_⟩
      · simp [schurWordOmega]
      · exact Subsingleton.elim _ _
    | succ n =>
      obtain hfirst | hfirst := exists_source_first_block n A
      · obtain ⟨a, Q, hentry, hlo⟩ := hfirst
        have hdN : 1 ≤ n + 1 := by omega
        have htop : ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A *
            (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).submatrix
              (Fin.castLE hdN) (Fin.castLE hdN) = scalarBlock a := by
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
        exact hasSchurWord_step (d := 1) (m := n) (by omega) A Q hdN (scalarBlock a) htop hlo'
          (fun U D hD => hasSchurWord_scalar_upper a U D hD) (fun D => ih n (by omega) D)
      · obtain ⟨h2, a, b, c, hc, hcb, Q, htop, hlo⟩ := hfirst
        exact hasSchurWord_step (d := 2) (m := n + 1 - 2) (by omega) A Q h2
          (schurBlock a b c) htop hlo
          (fun U D hD => hasSchurWord_pair_upper a b c U D hc hcb hD)
          (fun D => ih (n + 1 - 2) (by omega) D)

end Paper.Spectral
