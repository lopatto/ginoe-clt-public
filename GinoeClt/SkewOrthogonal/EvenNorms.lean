/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.Norms
public import GinoeClt.SkewOrthogonal.Algebra

/-! # Completion of the actual tau-zero skew-orthogonality identities -/
@[expose] public section
noncomputable section

namespace Paper.SkewOrthogonal

/-- The source odd polynomial formula; the zero coefficient handles index zero. -/
theorem oddPolynomial_eq (j : ℕ) :
    oddPolynomial j = Polynomial.X ^ (2 * j + 1) -
      Polynomial.C ((2 * j : ℕ) : ℂ) * Polynomial.X ^ (2 * j - 1) := by
  unfold oddPolynomial raising evenPolynomial
  rw [Polynomial.derivative_X_pow, ← pow_succ']

/-- The odd raising recurrence is an equality of actual polynomials. -/
theorem raising_odd_monomial (j : ℕ) :
    raising (Polynomial.X ^ (2 * j + 1)) = evenPolynomial (j + 1) -
      Polynomial.C ((2 * j + 1 : ℕ) : ℂ) * evenPolynomial j := by
  unfold raising evenPolynomial
  rw [Polynomial.derivative_X_pow, ← pow_succ']
  have h₁ : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  have h₂ : 2 * j + 1 - 1 = 2 * j := by omega
  rw [h₁, h₂]

theorem skewForm_even_step (i j : ℕ) :
    skewForm (evenPolynomial i) (evenPolynomial (j + 1)) =
      ((2 * j + 1 : ℕ) : ℂ) * skewForm (evenPolynomial i) (evenPolynomial j) := by
  have h := skewForm_raising_monomial (evenPolynomial i) (2 * j + 1)
  have hc : (evenPolynomial i).coeff (2 * j + 1) = 0 := by
    have hne : 2 * j + 1 ≠ 2 * i := by omega
    simp [evenPolynomial, Polynomial.coeff_X_pow, hne]
  rw [hc, mul_zero, raising_odd_monomial, skewForm_sub_right, skewForm_C_mul_right] at h
  exact sub_eq_zero.mp h

theorem skewForm_even_zero_left (j : ℕ) :
    skewForm (evenPolynomial 0) (evenPolynomial j) = 0 := by
  induction j with
  | zero => exact skewForm_self _
  | succ j ih => rw [skewForm_even_step, ih, mul_zero]

/-- Every even-even skew pairing vanishes, by the source raising recurrence. -/
theorem skewForm_even_even (i j : ℕ) :
    skewForm (evenPolynomial i) (evenPolynomial j) = 0 := by
  induction j with
  | zero => rw [skewForm_antisymm, skewForm_even_zero_left, neg_zero]
  | succ j ih => rw [skewForm_even_step, ih, mul_zero]

/-- The source skew norm is strictly positive as a real number, at every index. -/
theorem skew_norm_pos (j : ℕ) : 0 < 2 * Real.sqrt (2 * Real.pi) * ((2 * j).factorial : ℝ) := by
  apply mul_pos
  · exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
  · exact_mod_cast Nat.factorial_pos (2 * j)

theorem skewForm_even_odd_ne_zero (j : ℕ) :
    skewForm (evenPolynomial j) (oddPolynomial j) ≠ 0 := by
  rw [skewForm_even_odd, ite_eq_left rfl]
  exact_mod_cast (skew_norm_pos j).ne'

end Paper.SkewOrthogonal
