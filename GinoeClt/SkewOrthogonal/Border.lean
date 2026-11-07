/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.EvenNorms

/-! # The actual real Gaussian border for odd matrix sizes

The double factorial at index zero is written as `Nat.doubleFactorial (2*j-1)`;
at j = 0 it equals 0!! = 1, the source convention (-1)!! = 1.
-/
@[expose] public section
noncomputable section
open MeasureTheory

namespace Paper.SkewOrthogonal

/-- The literal real Gaussian moment functional in the odd bordered skew matrix. -/
def realBorder (P : Polynomial ℂ) : ℂ := ∫ x : ℝ, realGaussianPolynomial P x

theorem realBorder_sub (P Q : Polynomial ℂ) : realBorder (P - Q) = realBorder P - realBorder Q := by
  unfold realBorder
  rw [← integral_sub (integrable_realGaussianPolynomial P) (integrable_realGaussianPolynomial Q)]
  congr 1
  funext x
  simp only [realGaussianPolynomial, Polynomial.eval_sub]
  ring

theorem realBorder_C_mul (P : Polynomial ℂ) (c : ℂ) :
    realBorder (Polynomial.C c * P) = c * realBorder P := by
  unfold realBorder
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [realGaussianPolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem realBorder_raising (Q : Polynomial ℂ) : realBorder (raising Q) = 0 :=
  integral_realGaussianPolynomial_raising Q

theorem realBorder_one : realBorder 1 = (Real.sqrt (2 * Real.pi) : ℂ) := by
  unfold realBorder realGaussianPolynomial
  simp only [Polynomial.eval_one, mul_one]
  rw [integral_complex_ofReal]
  have he : (fun x : ℝ ↦ Real.exp (-x ^ 2 / 2)) =
      fun x ↦ Real.exp (-(1 / 2) * x ^ 2) := by
    funext x
    congr 1
    ring
  rw [he, integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring]

theorem realBorder_even_step (j : ℕ) :
    realBorder (evenPolynomial (j + 1)) =
      ((2 * j + 1 : ℕ) : ℂ) * realBorder (evenPolynomial j) := by
  have h := realBorder_raising (Polynomial.X ^ (2 * j + 1))
  rw [raising_odd_monomial, realBorder_sub, realBorder_C_mul] at h
  exact sub_eq_zero.mp h

/-- All actual even Gaussian border moments, including the lowest index. -/
theorem realBorder_even (j : ℕ) :
    realBorder (evenPolynomial j) =
      ((2 * j - 1).doubleFactorial : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) := by
  induction j with
  | zero => simpa only [evenPolynomial, mul_zero, pow_zero, Nat.zero_sub,
      Nat.doubleFactorial, Nat.cast_one, one_mul] using realBorder_one
  | succ j ih =>
    rw [realBorder_even_step, ih,
      show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
      Nat.doubleFactorial_add_one, Nat.cast_mul]
    ring

/-- Odd skew polynomials have zero actual Gaussian border moment. -/
theorem realBorder_odd (j : ℕ) : realBorder (oddPolynomial j) = 0 :=
  realBorder_raising (evenPolynomial j)

/-- The last even border moment is strictly positive; it can therefore be used as a divisor. -/
theorem realBorder_even_pos (j : ℕ) : 0 < (realBorder (evenPolynomial j)).re := by
  have hf : (0 : ℝ) < ((2 * j - 1).doubleFactorial : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * j - 1)
  have hs : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  simpa only [realBorder_even, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using mul_pos hf hs

theorem realBorder_even_ne_zero (j : ℕ) : realBorder (evenPolynomial j) ≠ 0 := by
  intro h
  have hp := realBorder_even_pos j
  rw [h] at hp
  exact (lt_irrefl 0) hp

end Paper.SkewOrthogonal
