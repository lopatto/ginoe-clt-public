/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurPairJacobian
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases

/-! # Spectral coordinates of a normalized real Schur pair

Input order is (y,delta); output order is (b,c). The signed Jacobian is
negative in these orders; its absolute value is 2*y/s. Boundary delta=0
is retained in all algebraic identities.
-/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

def pairRadius (y delta : ℝ) : ℝ := Real.sqrt (delta ^ 2 + 4 * y ^ 2)

def pairOffDiagonal (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(pairRadius (x 0) (x 1) + x 1) / 2,
    (pairRadius (x 0) (x 1) - x 1) / 2]

def pairOffDiagonalJacobian (y delta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * y / pairRadius y delta, (delta / pairRadius y delta + 1) / 2;
    2 * y / pairRadius y delta, (delta / pairRadius y delta - 1) / 2]

def pairOffDiagonalJacobianCLM (y delta : ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (Matrix.toLin' (pairOffDiagonalJacobian y delta)).toContinuousLinearMap

theorem pairRadius_pos {y delta : ℝ} (hy : 0 < y) : 0 < pairRadius y delta := by
  unfold pairRadius
  apply Real.sqrt_pos.mpr
  nlinarith only [sq_nonneg delta, sq_pos_of_pos hy]

theorem pairRadius_sq (y delta : ℝ) :
    pairRadius y delta ^ 2 = delta ^ 2 + 4 * y ^ 2 := by
  apply Real.sq_sqrt
  positivity

theorem pairRadius_gt_abs {y delta : ℝ} (hy : 0 < y) : |delta| < pairRadius y delta := by
  have hp := pairRadius_pos (delta := delta) hy
  have hs := pairRadius_sq y delta
  have ha : |delta| ^ 2 = delta ^ 2 := sq_abs delta
  nlinarith only [hs, ha, sq_pos_of_pos hy, hp, abs_nonneg delta]

theorem pairOffDiagonal_pos {y delta : ℝ} (hy : 0 < y) :
    0 < pairOffDiagonal ![y, delta] 0 ∧ 0 < pairOffDiagonal ![y, delta] 1 := by
  have hs := pairRadius_gt_abs (delta := delta) hy
  have ha := le_abs_self delta
  have hb := neg_le_abs delta
  change 0 < (pairRadius y delta + delta) / 2 ∧ 0 < (pairRadius y delta - delta) / 2
  constructor <;> linarith

theorem pairOffDiagonal_sum (y delta : ℝ) :
    pairOffDiagonal ![y, delta] 0 + pairOffDiagonal ![y, delta] 1 = pairRadius y delta := by
  change (pairRadius y delta + delta) / 2 + (pairRadius y delta - delta) / 2 = _
  ring

theorem pairOffDiagonal_sub (y delta : ℝ) :
    pairOffDiagonal ![y, delta] 0 - pairOffDiagonal ![y, delta] 1 = delta := by
  change (pairRadius y delta + delta) / 2 - (pairRadius y delta - delta) / 2 = _
  ring

theorem pairOffDiagonal_mul (y delta : ℝ) :
    pairOffDiagonal ![y, delta] 0 * pairOffDiagonal ![y, delta] 1 = y ^ 2 := by
  change (pairRadius y delta + delta) / 2 * ((pairRadius y delta - delta) / 2) = _
  nlinarith only [pairRadius_sq y delta]

theorem pairOffDiagonal_sq_sum (y delta : ℝ) :
    pairOffDiagonal ![y, delta] 0 ^ 2 + pairOffDiagonal ![y, delta] 1 ^ 2 =
      delta ^ 2 + 2 * y ^ 2 := by
  have hm := pairOffDiagonal_mul y delta
  have hd := pairOffDiagonal_sub y delta
  have hs := congrArg (fun r : ℝ => r ^ 2) hd
  nlinarith only [hm, hs]

theorem pairOffDiagonal_order_iff (y delta : ℝ) :
    pairOffDiagonal ![y, delta] 1 ≤ pairOffDiagonal ![y, delta] 0 ↔ 0 ≤ delta := by
  have hh := pairOffDiagonal_sub y delta
  constructor <;> intro h <;> linarith

theorem pairOffDiagonal_inverse {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    pairOffDiagonal ![Real.sqrt (b * c), b - c] = ![b, c] := by
  have hinside : (b - c) ^ 2 + 4 * Real.sqrt (b * c) ^ 2 = (b + c) ^ 2 := by
    rw [Real.sq_sqrt (mul_pos hb hc).le]
    ring
  have hs : pairRadius (Real.sqrt (b * c)) (b - c) = b + c := by
    rw [pairRadius, hinside, Real.sqrt_sq_eq_abs, abs_of_pos (add_pos hb hc)]
  ext i
  fin_cases i
  · change (pairRadius (Real.sqrt (b * c)) (b - c) + (b - c)) / 2 = b
    rw [hs]
    ring
  · change (pairRadius (Real.sqrt (b * c)) (b - c) - (b - c)) / 2 = c
    rw [hs]
    ring

theorem det_pairOffDiagonalJacobian (y delta : ℝ) :
    (pairOffDiagonalJacobian y delta).det = -(2 * y / pairRadius y delta) := by
  rw [Matrix.det_fin_two]
  change 2 * y / pairRadius y delta * ((delta / pairRadius y delta - 1) / 2) -
    (delta / pairRadius y delta + 1) / 2 * (2 * y / pairRadius y delta) = _
  ring

theorem abs_det_pairOffDiagonalJacobian {y delta : ℝ} (hy : 0 < y) :
    |(pairOffDiagonalJacobian y delta).det| = 2 * y / pairRadius y delta := by
  rw [det_pairOffDiagonalJacobian, abs_neg, abs_of_pos]
  exact div_pos (mul_pos (by norm_num) hy) (pairRadius_pos hy)

/-- The actual inverse pair-coordinate map has this derivative for y>0.
No strict inequality on delta is required. -/
theorem hasFDerivAt_pairOffDiagonal {y delta : ℝ} (hy : 0 < y) :
    HasFDerivAt pairOffDiagonal (pairOffDiagonalJacobianCLM y delta) ![y, delta] := by
  let x0 : Fin 2 → ℝ := ![y, delta]
  have hdy := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x0
  have hdd := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x0
  have harg := (hdd.pow 2).add ((hdy.pow 2).const_mul 4)
  have harg0 : x0 1 ^ 2 + 4 * x0 0 ^ 2 ≠ 0 := by
    change delta ^ 2 + 4 * y ^ 2 ≠ 0
    have hh : 0 < delta ^ 2 + 4 * y ^ 2 := by
      nlinarith only [sq_nonneg delta, sq_pos_of_pos hy]
    exact hh.ne'
  have hs := harg.sqrt harg0
  have hb := (hs.add hdd).mul_const (1 / 2 : ℝ)
  have hc := (hs.sub hdd).mul_const (1 / 2 : ℝ)
  have hrad := (pairRadius_pos (delta := delta) hy).ne'
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! hb using 1
    · funext x
      simp [pairOffDiagonal, pairRadius, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext
      intro x
      norm_num [pairOffDiagonalJacobianCLM, pairOffDiagonalJacobian, pairRadius,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, x0]
      field_simp
      ring
  · convert! hc using 1
    · funext x
      simp [pairOffDiagonal, pairRadius, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext
      intro x
      norm_num [pairOffDiagonalJacobianCLM, pairOffDiagonalJacobian, pairRadius,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, x0]
      field_simp
      ring

theorem det_fderiv_pairOffDiagonal {y delta : ℝ} (hy : 0 < y) :
    (LinearMap.toMatrix' (fderiv ℝ pairOffDiagonal ![y, delta]).toLinearMap).det =
      -(2 * y / pairRadius y delta) := by
  rw [(hasFDerivAt_pairOffDiagonal hy).fderiv]
  change (LinearMap.toMatrix' (Matrix.toLin' (pairOffDiagonalJacobian y delta))).det = _
  rw [LinearMap.toMatrix'_toLin', det_pairOffDiagonalJacobian]

theorem abs_det_fderiv_pairOffDiagonal {y delta : ℝ} (hy : 0 < y) :
    |(LinearMap.toMatrix' (fderiv ℝ pairOffDiagonal ![y, delta]).toLinearMap).det| =
      2 * y / pairRadius y delta := by
  rw [det_fderiv_pairOffDiagonal hy, abs_neg, abs_of_pos]
  exact div_pos (mul_pos (by norm_num) hy) (pairRadius_pos hy)

theorem pairOffDiagonal_spectral {y delta : ℝ} (hy : 0 < y) :
    Real.sqrt (pairOffDiagonal ![y, delta] 0 * pairOffDiagonal ![y, delta] 1) = y ∧
      pairOffDiagonal ![y, delta] 0 - pairOffDiagonal ![y, delta] 1 = delta := by
  rw [pairOffDiagonal_mul, Real.sqrt_sq_eq_abs, abs_of_pos hy]
  exact ⟨rfl, pairOffDiagonal_sub y delta⟩

theorem det_fderiv_pairOffDiagonal_ne_zero {y delta : ℝ} (hy : 0 < y) :
    (LinearMap.toMatrix' (fderiv ℝ pairOffDiagonal ![y, delta]).toLinearMap).det ≠ 0 := by
  rw [det_fderiv_pairOffDiagonal hy]
  exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) hy.ne') (pairRadius_pos hy).ne')

end Paper.Spectral
