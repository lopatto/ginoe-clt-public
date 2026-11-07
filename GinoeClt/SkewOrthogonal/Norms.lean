/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.GaussianPairing
public import GinoeClt.SkewOrthogonal.ComplexIBP

/-! # The actual tau-zero skew polynomials and their normalization

The form is the literal sum of the real and complex Gaussian integrals.
-/
@[expose] public section
noncomputable section
open MeasureTheory

namespace Paper.SkewOrthogonal

/-- The source even skew polynomial. -/
def evenPolynomial (j : ℕ) : Polynomial ℂ := Polynomial.X ^ (2 * j)

/-- The source odd skew polynomial; its lowest case has no negative power. -/
def oddPolynomial (j : ℕ) : Polynomial ℂ := raising (evenPolynomial j)

theorem skewConstant_mul_pi : skewConstant * Real.pi = 2 * Real.sqrt (2 * Real.pi) := by
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    skewConstant * Real.pi = 2 * Real.sqrt 2 * Real.sqrt Real.pi := by
      unfold skewConstant
      field_simp [hs]
      ring_nf
      rw [Real.sq_sqrt Real.pi_pos.le]
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; ring

/-- Pairing a raising monomial extracts the actual unconjugated coefficient. -/
theorem skewForm_raising_monomial (P : Polynomial ℂ) (m : ℕ) :
    skewForm P (raising (Polynomial.X ^ m)) =
      ((2 * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * (m.factorial : ℂ) * P.coeff m := by
  rw [skewForm_raising]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [gaussian_polynomial_monomial]
  calc
    _ = ((skewConstant : ℂ) * (Real.pi : ℂ)) * (m.factorial : ℂ) * P.coeff m := by ring
    _ = _ := by rw [← Complex.ofReal_mul, skewConstant_mul_pi]

/-- The exact mixed skew norm, for every pair of indices. -/
theorem skewForm_even_odd (i j : ℕ) :
    skewForm (evenPolynomial i) (oddPolynomial j) =
      if i = j then ((2 * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((2 * j).factorial : ℂ) else 0 := by
  change skewForm (evenPolynomial i) (raising (Polynomial.X ^ (2 * j))) = _
  rw [skewForm_raising_monomial]
  by_cases h : i = j
  · subst i
    simp [evenPolynomial]
  · simp [evenPolynomial, Polynomial.coeff_X_pow, h, Ne.symm h]

/-- An odd skew polynomial has no even coefficient, directly from the actual raising definition. -/
theorem oddPolynomial_coeff_even (i j : ℕ) : (oddPolynomial i).coeff (2 * j) = 0 := by
  have hx : Polynomial.X * evenPolynomial i = (Polynomial.X : Polynomial ℂ) ^ (2 * i + 1) := by
    rw [evenPolynomial, pow_succ]
    ring
  rw [oddPolynomial, raising, Polynomial.coeff_sub, hx, Polynomial.coeff_derivative]
  have h₁ : 2 * i + 1 ≠ 2 * j := by omega
  have h₂ : 2 * i ≠ 2 * j + 1 := by omega
  simp [evenPolynomial, Polynomial.coeff_X_pow, Ne.symm h₁, Ne.symm h₂]

/-- Every odd-odd skew pairing vanishes for the literal Gaussian form. -/
theorem skewForm_odd_odd (i j : ℕ) :
    skewForm (oddPolynomial i) (oddPolynomial j) = 0 := by
  change skewForm (oddPolynomial i) (raising (Polynomial.X ^ (2 * j))) = 0
  rw [skewForm_raising_monomial, oddPolynomial_coeff_even, mul_zero]

end Paper.SkewOrthogonal
