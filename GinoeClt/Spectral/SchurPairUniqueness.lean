/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurPairStabilizer
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Exact parameter uniqueness of positive strictly ordered real Schur pairs. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

theorem trace_orthogonal_conjugation {N : ℕ}
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace ((Q : Matrix (Fin N) (Fin N) ℝ) * A * Qᵀ) = Matrix.trace A := by
  have hQtQ := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property
  rw [Matrix.trace_mul_cycle, hQtQ, Matrix.one_mul]

theorem det_orthogonal_conjugation {N : ℕ}
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    ((Q : Matrix (Fin N) (Fin N) ℝ) * A * Qᵀ).det = A.det := by
  have hQQt := (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp Q.property
  calc
    _ = A.det * ((Q : Matrix (Fin N) (Fin N) ℝ) * Qᵀ).det := by
      simp only [Matrix.det_mul]
      ring
    _ = _ := by rw [hQQt, Matrix.det_one, mul_one]

theorem trace_square_orthogonal_conjugation {N : ℕ}
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace (((Q : Matrix (Fin N) (Fin N) ℝ) * A * Qᵀ) *
      ((Q : Matrix (Fin N) (Fin N) ℝ) * A * Qᵀ)ᵀ) =
        Matrix.trace (A * Aᵀ) := by
  have hQtQ := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property
  have he :
      ((Q : Matrix (Fin N) (Fin N) ℝ) * A * Qᵀ) *
        ((Q : Matrix (Fin N) (Fin N) ℝ) * A * Qᵀ)ᵀ =
          (Q : Matrix (Fin N) (Fin N) ℝ) * (A * Aᵀ) * Qᵀ := by
    calc
      _ = (Q : Matrix (Fin N) (Fin N) ℝ) * A *
          (Qᵀ * (Q : Matrix (Fin N) (Fin N) ℝ)) * Aᵀ * Qᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hQtQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [he, trace_orthogonal_conjugation]

@[simp] theorem trace_schurBlock (a b c : ℝ) :
    Matrix.trace (schurBlock a b c) = 2 * a := by
  simp [schurBlock, Matrix.trace_fin_two, two_mul]

theorem det_schurBlock (a b c : ℝ) :
    (schurBlock a b c).det = a ^ 2 + b * c := by
  simp only [Matrix.det_fin_two, schurBlock, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem trace_schurBlock_square_transpose (a b c : ℝ) :
    Matrix.trace (schurBlock a b c * (schurBlock a b c)ᵀ) =
      2 * a ^ 2 + b ^ 2 + c ^ 2 := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, schurBlock, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem orthogonal_schurBlock_parameters_unique
    (a b c a' b' c' : ℝ) (hc : 0 < c) (hcb : c < b)
    (hc' : 0 < c') (hcb' : c' < b')
    (Q : Matrix.orthogonalGroup (Fin 2) ℝ)
    (he : (Q : Matrix (Fin 2) (Fin 2) ℝ) * schurBlock a b c * Qᵀ =
      schurBlock a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have ht := congrArg Matrix.trace he
  rw [trace_orthogonal_conjugation, trace_schurBlock, trace_schurBlock] at ht
  have ha : a = a' := by linarith
  have hd := congrArg Matrix.det he
  rw [det_orthogonal_conjugation, det_schurBlock, det_schurBlock, ← ha] at hd
  have hn := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
    Matrix.trace (M * Mᵀ)) he
  rw [trace_square_orthogonal_conjugation, trace_schurBlock_square_transpose,
    trace_schurBlock_square_transpose, ← ha] at hn
  have hp : b * c = b' * c' := by nlinarith only [hd]
  have hsq : b ^ 2 + c ^ 2 = b' ^ 2 + c' ^ 2 := by nlinarith only [hn]
  have hsum : b + c = b' + c' := by
    apply (sq_eq_sq₀ (by linarith : 0 ≤ b + c) (by linarith : 0 ≤ b' + c')).mp
    nlinarith only [hp, hsq]
  have hdiff : b - c = b' - c' := by
    apply (sq_eq_sq₀ (by linarith : 0 ≤ b - c) (by linarith : 0 ≤ b' - c')).mp
    nlinarith only [hp, hsq]
  exact ⟨ha, by linarith, by linarith⟩

theorem orthogonal_schurBlock_similarity_eq_parameters_and_sign
    (a b c a' b' c' : ℝ) (hc : 0 < c) (hcb : c < b)
    (hc' : 0 < c') (hcb' : c' < b')
    (Q : Matrix.orthogonalGroup (Fin 2) ℝ)
    (he : (Q : Matrix (Fin 2) (Fin 2) ℝ) * schurBlock a b c * Qᵀ =
      schurBlock a' b' c') :
    a = a' ∧ b = b' ∧ c = c' ∧
      ((Q : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨
        (Q : Matrix (Fin 2) (Fin 2) ℝ) = -1) := by
  obtain ⟨ha, hb, hcc⟩ :=
    orthogonal_schurBlock_parameters_unique a b c a' b' c' hc hcb hc' hcb' Q he
  refine ⟨ha, hb, hcc, ?_⟩
  apply (orthogonal_schurBlock_conjugation_eq_iff_sign a b c hc hcb Q).mp
  simpa only [← ha, ← hb, ← hcc] using he

end Paper.Spectral
