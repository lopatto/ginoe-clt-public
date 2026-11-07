/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SylvesterBlocks
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Spectral factors of the real Schur between-block determinants -/

@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate Polynomial

namespace Paper.Spectral

def schurRoot (a b c : ℝ) : ℂ := ⟨a, Real.sqrt (b * c)⟩

lemma norm_mk_sub_mk_sq (a u d v : ℝ) :
    ‖(⟨a, u⟩ : ℂ) - ⟨d, v⟩‖ ^ 2 = (a - d) ^ 2 + (u - v) ^ 2 := by
  rw [Complex.sq_norm]
  change (a - d) * (a - d) + (u - v) * (u - v) = (a - d) ^ 2 + (u - v) ^ 2
  ring

lemma det_sylvester_scalar_block_root (a d e f : ℝ) (hef : 0 ≤ e * f) :
    (sylvesterMatrix (scalarBlock a) (schurBlock d e f)).det =
      ‖(a : ℂ) - schurRoot d e f‖ ^ 2 := by
  change (sylvesterMatrix (scalarBlock a) (schurBlock d e f)).det =
    ‖(⟨a, 0⟩ : ℂ) - ⟨d, Real.sqrt (e * f)⟩‖ ^ 2
  rw [det_sylvester_scalar_block, norm_mk_sub_mk_sq, zero_sub, neg_sq, Real.sq_sqrt hef]
  ring

lemma det_sylvester_block_scalar_root (a b c d : ℝ) (hbc : 0 ≤ b * c) :
    (sylvesterMatrix (schurBlock a b c) (scalarBlock d)).det =
      ‖schurRoot a b c - (d : ℂ)‖ ^ 2 := by
  change (sylvesterMatrix (schurBlock a b c) (scalarBlock d)).det =
    ‖(⟨a, Real.sqrt (b * c)⟩ : ℂ) - ⟨d, 0⟩‖ ^ 2
  rw [det_sylvester_block_scalar, norm_mk_sub_mk_sq, sub_zero, Real.sq_sqrt hbc]
  ring

lemma det_sylvester_block_block_roots (a b c d e f : ℝ)
    (hbc : 0 ≤ b * c) (hef : 0 ≤ e * f) :
    (sylvesterMatrix (schurBlock a b c) (schurBlock d e f)).det =
      ‖schurRoot a b c - schurRoot d e f‖ ^ 2 *
        ‖schurRoot a b c - conj (schurRoot d e f)‖ ^ 2 := by
  change (sylvesterMatrix (schurBlock a b c) (schurBlock d e f)).det =
    ‖(⟨a, Real.sqrt (b * c)⟩ : ℂ) - ⟨d, Real.sqrt (e * f)⟩‖ ^ 2 *
      ‖(⟨a, Real.sqrt (b * c)⟩ : ℂ) - ⟨d, -Real.sqrt (e * f)⟩‖ ^ 2
  rw [det_sylvester_block_block, norm_mk_sub_mk_sq, norm_mk_sub_mk_sq, sub_neg_eq_add]
  calc
    _ = ((a - d) ^ 2 + Real.sqrt (b * c) ^ 2 + Real.sqrt (e * f) ^ 2) ^ 2 -
        4 * Real.sqrt (b * c) ^ 2 * Real.sqrt (e * f) ^ 2 := by
      rw [Real.sq_sqrt hbc, Real.sq_sqrt hef]
      ring
    _ = _ := by ring

lemma schurBlock_trace (a b c : ℝ) : (schurBlock a b c).trace = 2 * a := by
  simp only [Matrix.trace, Fin.sum_univ_two, schurBlock]
  change a + a = 2 * a
  ring

lemma schurBlock_det (a b c : ℝ) : (schurBlock a b c).det = a ^ 2 + b * c := by
  rw [Matrix.det_fin_two]
  change a * a - b * (-c) = a ^ 2 + b * c
  ring

lemma schurRoot_add_conj (a b c : ℝ) :
    schurRoot a b c + conj (schurRoot a b c) = ((2 * a : ℝ) : ℂ) := by
  apply Complex.ext
  · change a + a = 2 * a
    ring
  · change Real.sqrt (b * c) + -Real.sqrt (b * c) = 0
    ring

lemma schurRoot_mul_conj (a b c : ℝ) (hbc : 0 ≤ b * c) :
    schurRoot a b c * conj (schurRoot a b c) = ((a ^ 2 + b * c : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, schurRoot, Complex.ofReal_re]
    nlinarith only [Real.sq_sqrt hbc]
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, schurRoot, Complex.ofReal_im]
    ring

/-- Exact characteristic factorization, including coincident roots. -/
lemma schurBlock_charpoly_factor (a b c : ℝ) (hbc : 0 ≤ b * c) :
    (schurBlock a b c).charpoly.map Complex.ofRealHom =
      (Polynomial.X - Polynomial.C (schurRoot a b c)) *
        (Polynomial.X - Polynomial.C (conj (schurRoot a b c))) := by
  rw [Matrix.charpoly_fin_two, schurBlock_trace, schurBlock_det]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C]
  change (Polynomial.X : ℂ[X]) ^ 2 - Polynomial.C ((2 * a : ℝ) : ℂ) * Polynomial.X +
    Polynomial.C ((a ^ 2 + b * c : ℝ) : ℂ) = _
  rw [← schurRoot_add_conj a b c, ← schurRoot_mul_conj a b c hbc,
    Polynomial.C_add, Polynomial.C_mul]
  ring

/-- The entire algebraic-multiplicity root multiset of the source two-by-two block. -/
lemma schurBlock_roots (a b c : ℝ) (hbc : 0 ≤ b * c) :
    ((schurBlock a b c).charpoly.map Complex.ofRealHom).roots =
      {schurRoot a b c, conj (schurRoot a b c)} := by
  rw [schurBlock_charpoly_factor a b c hbc,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  rfl

lemma abs_det_sylvester_block_block_roots (a b c d e f : ℝ)
    (hbc : 0 ≤ b * c) (hef : 0 ≤ e * f) :
    |(sylvesterMatrix (schurBlock a b c) (schurBlock d e f)).det| =
      ‖schurRoot a b c - schurRoot d e f‖ ^ 2 *
        ‖schurRoot a b c - conj (schurRoot d e f)‖ ^ 2 := by
  rw [det_sylvester_block_block_roots a b c d e f hbc hef,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]

lemma det_sylvester_block_block_ne_zero (a b c d e f : ℝ)
    (hbc : 0 ≤ b * c) (hef : 0 ≤ e * f)
    (h₁ : schurRoot a b c ≠ schurRoot d e f)
    (h₂ : schurRoot a b c ≠ conj (schurRoot d e f)) :
    (sylvesterMatrix (schurBlock a b c) (schurBlock d e f)).det ≠ 0 := by
  rw [det_sylvester_block_block_roots a b c d e f hbc hef]
  exact mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h₁)))
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h₂)))

/-- Nonzero determinant gives actual injectivity on rectangular matrix variables. -/
lemma sylvester_injective_of_det_ne_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hdet : (sylvesterMatrix A B).det ≠ 0) :
    Function.Injective (fun X : Matrix (Fin m) (Fin n) ℝ => X * B - A * X) := by
  intro X Y hXY
  apply Matrix.vec_inj.mp
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  rw [sylvesterMatrix_mulVec, sylvesterMatrix_mulVec]
  change X * B - A * X = Y * B - A * Y at hXY
  rw [hXY]

lemma sylvester_scalar_block_injective (a d e f : ℝ) (hef : 0 < e * f) :
    Function.Injective (fun X : Matrix (Fin 1) (Fin 2) ℝ =>
      X * schurBlock d e f - scalarBlock a * X) := by
  apply sylvester_injective_of_det_ne_zero
  rw [det_sylvester_scalar_block]
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg (d - a)) hef)

lemma sylvester_block_scalar_injective (a b c d : ℝ) (hbc : 0 < b * c) :
    Function.Injective (fun X : Matrix (Fin 2) (Fin 1) ℝ =>
      X * scalarBlock d - schurBlock a b c * X) := by
  apply sylvester_injective_of_det_ne_zero
  rw [det_sylvester_block_scalar]
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg (d - a)) hbc)

lemma sylvester_block_block_injective (a b c d e f : ℝ)
    (hbc : 0 ≤ b * c) (hef : 0 ≤ e * f)
    (h₁ : schurRoot a b c ≠ schurRoot d e f)
    (h₂ : schurRoot a b c ≠ conj (schurRoot d e f)) :
    Function.Injective (fun X : Matrix (Fin 2) (Fin 2) ℝ =>
      X * schurBlock d e f - schurBlock a b c * X) :=
  sylvester_injective_of_det_ne_zero _ _
    (det_sylvester_block_block_ne_zero a b c d e f hbc hef h₁ h₂)

end Paper.Spectral
