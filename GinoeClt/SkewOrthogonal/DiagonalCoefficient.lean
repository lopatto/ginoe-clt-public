/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.PolynomialPfaffian
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # The exact factorial relating a diagonal polynomial to its full mixed coefficient

This uses Mathlib's proved multinomial coefficient formula. It does not assume
an assignment count, interchange a coefficient with an integral, or assert a
continuous generating identity.
-/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace Paper.SkewOrthogonal

theorem fullSquarefreeIndex_support (r : ℕ) : (fullSquarefreeIndex r).support = Finset.univ := by
  ext i
  simp [Finsupp.mem_support_iff, fullSquarefreeIndex, Finsupp.indicator_apply]

theorem fullSquarefreeIndex_sum (r : ℕ) : (fullSquarefreeIndex r).sum (fun _ n ↦ n) = r := by
  change (∑ i ∈ (fullSquarefreeIndex r).support, fullSquarefreeIndex r i) = r
  rw [fullSquarefreeIndex_support]
  simp [fullSquarefreeIndex, Finsupp.indicator_apply]

theorem fullSquarefreeIndex_multinomial (r : ℕ) : (fullSquarefreeIndex r).multinomial = r.factorial := by
  unfold Finsupp.multinomial
  change ((fullSquarefreeIndex r).sum (fun _ n ↦ n)).factorial / _ = _
  rw [fullSquarefreeIndex_sum]
  have hp : (fullSquarefreeIndex r).prod (fun _ n ↦ n.factorial) = 1 := by
    change (∏ i ∈ (fullSquarefreeIndex r).support, (fullSquarefreeIndex r i).factorial) = 1
    apply Finset.prod_eq_one
    intro i hi
    simp [fullSquarefreeIndex, Finsupp.indicator_apply]
  rw [hp, Nat.div_one]

/-- The full squarefree coefficient in a power of the variable sum, all r,n. -/
theorem coeff_fullSquarefree_sum_X_pow (r n : ℕ) :
    ((∑ i : Fin r, (MvPolynomial.X i : MvPolynomial (Fin r) ℂ)) ^ n).coeff
        (fullSquarefreeIndex r) = if n = r then (r.factorial : ℂ) else 0 := by
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype]
  by_cases h : n = r
  · subst n
    simp [fullSquarefreeIndex_sum, fullSquarefreeIndex_multinomial]
  · simp [fullSquarefreeIndex_sum, h, Ne.symm h]

/-- Standard polynomial substitution t = sum of the independent variables. -/
def diagonalLift (r : ℕ) (p : Polynomial ℂ) : MvPolynomial (Fin r) ℂ :=
  p.eval₂ MvPolynomial.C (∑ i : Fin r, MvPolynomial.X i)

theorem eval_diagonalLift (r : ℕ) (p : Polynomial ℂ) (c : Fin r → ℂ) :
    MvPolynomial.eval c (diagonalLift r p) = p.eval (∑ i : Fin r, c i) := by
  simp [diagonalLift, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum]

/-- The factorial is a proved coefficient identity, including the zero-variable case. -/
theorem coeff_diagonalLift (r : ℕ) (p : Polynomial ℂ) :
    (diagonalLift r p).coeff (fullSquarefreeIndex r) = (r.factorial : ℂ) * p.coeff r := by
  rw [diagonalLift, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    coeff_fullSquarefree_sum_X_pow, mul_ite, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · ring
  · rw [Polynomial.notMem_support_iff.mp h, mul_zero]

end Paper.SkewOrthogonal
