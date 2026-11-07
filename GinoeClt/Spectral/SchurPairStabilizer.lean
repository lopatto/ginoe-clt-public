/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurPairJacobian

/-! # The exact orthogonal stabilizer of a strict normalized pair

A positive unequal normalized pair has only the two common-sign frame choices.
This is not a global Schur fiber-count theorem.
-/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

theorem orthogonal_commuting_schurBlock_eq_sign
    (a b c : ℝ) (hc : 0 < c) (hcb : c < b)
    (Q : Matrix.orthogonalGroup (Fin 2) ℝ)
    (hcomm : (Q : Matrix (Fin 2) (Fin 2) ℝ) * schurBlock a b c =
      schurBlock a b c * Q) :
    (Q : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨
      (Q : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  have hb : 0 < b := hc.trans hcb
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hcomm
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hcomm
  simp only [Matrix.mul_apply, Fin.sum_univ_two, schurBlock,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h01 h00
  have hw : (Q : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = Q 0 0 := by nlinarith
  have hz : b * Q 1 0 = -(c * Q 0 1) := by nlinarith
  have ho := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp Q.property
  have hr0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) ho
  have hr1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) ho
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
    Matrix.one_apply_eq] at hr0 hr1
  have hy2 : Q 0 1 ^ 2 = Q 1 0 ^ 2 := by rw [hw] at hr1; nlinarith
  have hs := congrArg (fun t : ℝ => t ^ 2) hz
  have hprod : (b ^ 2 - c ^ 2) * Q 0 1 ^ 2 = 0 := by
    nlinarith only [hs, congrArg (fun t : ℝ => b ^ 2 * t) hy2]
  have hgap : 0 < b ^ 2 - c ^ 2 := by nlinarith
  have hy : (Q : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
    have := (mul_eq_zero.mp hprod).resolve_left hgap.ne'
    exact sq_eq_zero_iff.mp this
  have hz0 : (Q : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by rw [hy] at hz; nlinarith
  have hx : Q 0 0 ^ 2 = 1 := by rw [hy] at hr0; nlinarith
  rcases sq_eq_one_iff.mp hx with hx | hx
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all

theorem orthogonal_schurBlock_conjugation_eq_iff_sign
    (a b c : ℝ) (hc : 0 < c) (hcb : c < b)
    (Q : Matrix.orthogonalGroup (Fin 2) ℝ) :
    (Q : Matrix (Fin 2) (Fin 2) ℝ) * schurBlock a b c *
        (Q : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = schurBlock a b c ↔
      (Q : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨
        (Q : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  constructor
  · intro h
    have hQtQ := (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp Q.property
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M * Q) h
    have hcomm : (Q : Matrix (Fin 2) (Fin 2) ℝ) * schurBlock a b c =
        schurBlock a b c * Q := by
      simpa only [Matrix.mul_assoc, hQtQ, Matrix.mul_one] using hh
    exact orthogonal_commuting_schurBlock_eq_sign a b c hc hcb Q hcomm
  · rintro (h | h) <;> rw [h] <;> simp

end Paper.Spectral
