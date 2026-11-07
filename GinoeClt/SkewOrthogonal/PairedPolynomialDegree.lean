/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.OddBasis
public import GinoeClt.Algebra.PfaffianMinorCoordinates
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.Vandermonde
@[expose] public section
noncomputable section
open Polynomial
namespace Paper.SkewOrthogonal

theorem raising_X_pow_eq (n : ℕ) :
    raising ((X : Polynomial ℂ)^n) = X^(n+1) - ((X : Polynomial ℂ)^n).derivative := by
  rw [raising,← pow_succ']

/-- This strict bound includes n=0: the zero derivative has natural degree zero. -/
theorem natDegree_derivative_X_pow_lt (n : ℕ) :
    (((X : Polynomial ℂ)^n).derivative).natDegree < ((X : Polynomial ℂ)^(n+1)).natDegree := by
  have h := Polynomial.natDegree_derivative_le ((X : Polynomial ℂ)^n)
  rw [Polynomial.natDegree_X_pow] at h ⊢
  omega

theorem raising_X_pow_monic (n : ℕ) : (raising ((X : Polynomial ℂ)^n)).Monic := by
  rw [raising_X_pow_eq]
  exact (Polynomial.monic_X_pow (n+1)).sub_of_left
    (Polynomial.degree_lt_degree (natDegree_derivative_X_pow_lt n))

theorem raising_X_pow_natDegree (n : ℕ) : (raising ((X : Polynomial ℂ)^n)).natDegree = n+1 := by
  rw [raising_X_pow_eq,
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt (natDegree_derivative_X_pow_lt n),
    Polynomial.natDegree_X_pow]

/-- The EXISTING source family is monic in both interlaced columns. -/
theorem pairedPolynomial_monic (m : ℕ) (p : Fin m × Fin 2) : (pairedPolynomial m p).Monic := by
  rcases p with ⟨i,a⟩
  fin_cases a
  · simp [pairedPolynomial,evenPolynomial]
  · simpa [pairedPolynomial,oddPolynomial,evenPolynomial] using raising_X_pow_monic (2*i.val)

theorem pairedPolynomial_natDegree (m : ℕ) (p : Fin m × Fin 2) :
    (pairedPolynomial m p).natDegree = 2*p.1.val+p.2.val := by
  rcases p with ⟨i,a⟩
  fin_cases a
  · simp [pairedPolynomial,evenPolynomial]
  · simpa [pairedPolynomial,oddPolynomial,evenPolynomial] using raising_X_pow_natDegree (2*i.val)

theorem pairColumnEquiv_val (m : ℕ) (p : Fin m × Fin 2) :
    (PfaffianMinor.pairColumnEquiv m p).val = 2*p.1.val+p.2.val := by
  simp [PfaffianMinor.pairColumnEquiv,finProdFinEquiv]
  omega

/-- The ordinary finite polynomial index has EXACTLY the corresponding degree. -/
theorem pairedPolynomial_fin_natDegree (m : ℕ) (i : Fin (2*m)) :
    (pairedPolynomial m ((PfaffianMinor.pairColumnEquiv m).symm i)).natDegree = i.val := by
  rw [pairedPolynomial_natDegree]
  have h := congrArg Fin.val ((PfaffianMinor.pairColumnEquiv m).apply_symm_apply i)
  simpa only [pairColumnEquiv_val] using h

theorem pairedPolynomial_fin_monic (m : ℕ) (i : Fin (2*m)) :
    (pairedPolynomial m ((PfaffianMinor.pairColumnEquiv m).symm i)).Monic :=
  pairedPolynomial_monic m _

/-- Polynomial ROWS and root COLUMNS; transposition introduces no sign. -/
theorem det_pairedPolynomial_eval_fin (m : ℕ) (v : Fin (2*m) → ℂ) :
    (Matrix.of (fun i j : Fin (2*m) =>
      (pairedPolynomial m ((PfaffianMinor.pairColumnEquiv m).symm i)).eval (v j))).det =
      (Matrix.vandermonde v).det := by
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
    (fun i => pairedPolynomial m ((PfaffianMinor.pairColumnEquiv m).symm i))
    (pairedPolynomial_fin_natDegree m) (pairedPolynomial_fin_monic m)
  rw [← Matrix.det_transpose]
  exact h.symm

/-- Simultaneously reindex the ACTUAL paired polynomial rows and paired root
columns. No permutation sign survives, including the empty matrix m=0. -/
theorem det_pairedPolynomial_eval (m : ℕ) (v : (Fin m × Fin 2) → ℂ) :
    (Matrix.of (fun p q : Fin m × Fin 2 => (pairedPolynomial m p).eval (v q))).det =
      (Matrix.vandermonde (fun i : Fin (2*m) => v ((PfaffianMinor.pairColumnEquiv m).symm i))).det := by
  let A : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ :=
    fun p q => (pairedPolynomial m p).eval (v q)
  have h : (A.submatrix (PfaffianMinor.pairColumnEquiv m).symm
      (PfaffianMinor.pairColumnEquiv m).symm).det =
      (Matrix.vandermonde (fun i : Fin (2*m) => v ((PfaffianMinor.pairColumnEquiv m).symm i))).det :=
    det_pairedPolynomial_eval_fin m _
  exact (Matrix.det_submatrix_equiv_self (PfaffianMinor.pairColumnEquiv m).symm A).symm.trans h

end Paper.SkewOrthogonal
