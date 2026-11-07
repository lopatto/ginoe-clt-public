/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.Border

/-! # The actual odd-size border adjustment

Only the paired polynomials are adjusted. The last even polynomial is retained,
and its actual nonzero Gaussian moment supplies the denominator.
-/
@[expose] public section
noncomputable section

namespace Paper.SkewOrthogonal

theorem skewForm_sub_left (P Q R : Polynomial ℂ) :
    skewForm (P - Q) R = skewForm P R - skewForm Q R := by
  rw [skewForm_antisymm R (P - Q), skewForm_sub_right,
    skewForm_antisymm P R, skewForm_antisymm Q R]
  ring

theorem skewForm_C_mul_left (P Q : Polynomial ℂ) (c : ℂ) :
    skewForm (Polynomial.C c * P) Q = c * skewForm P Q := by
  rw [skewForm_antisymm Q (Polynomial.C c * P), skewForm_C_mul_right,
    skewForm_antisymm P Q]
  ring

/-- Subtraction of the actual Gaussian border along a selected last polynomial. -/
def adjustBorder (L P : Polynomial ℂ) : Polynomial ℂ :=
  P - Polynomial.C (realBorder P / realBorder L) * L

theorem realBorder_adjustBorder (L P : Polynomial ℂ) (hL : realBorder L ≠ 0) :
    realBorder (adjustBorder L P) = 0 := by
  rw [adjustBorder, realBorder_sub, realBorder_C_mul, div_mul_cancel₀ _ hL, sub_self]

/-- A radical last polynomial preserves the actual paired skew Gram matrix. -/
theorem skewForm_adjustBorder (L P Q : Polynomial ℂ)
    (hLP : skewForm L P = 0) (hLQ : skewForm L Q = 0) :
    skewForm (adjustBorder L P) (adjustBorder L Q) = skewForm P Q := by
  have hPL : skewForm P L = 0 := by rw [skewForm_antisymm L P, hLP, neg_zero]
  simp only [adjustBorder, skewForm_sub_left, skewForm_sub_right,
    skewForm_C_mul_left, skewForm_C_mul_right, skewForm_self, hPL, hLQ]
  ring

/-- The original interlaced family of paired source polynomials. -/
def pairedPolynomial (m : ℕ) (p : Fin m × Fin 2) : Polynomial ℂ :=
  if p.2 = 0 then evenPolynomial p.1.val else oddPolynomial p.1.val

theorem lastEven_radical (m : ℕ) (p : Fin m × Fin 2) :
    skewForm (evenPolynomial m) (pairedPolynomial m p) = 0 := by
  unfold pairedPolynomial
  split_ifs
  · exact skewForm_even_even m p.1.val
  · rw [skewForm_even_odd]
    have hne : m ≠ p.1.val := by have hi := p.1.isLt; omega
    exact ite_eq_right hne

/-- `none` is the unchanged last even polynomial; `some p` is an adjusted paired one. -/
def oddBasisPolynomial (m : ℕ) : Option (Fin m × Fin 2) → Polynomial ℂ
  | none => evenPolynomial m
  | some p => adjustBorder (evenPolynomial m) (pairedPolynomial m p)

@[simp] theorem oddBasisPolynomial_none (m : ℕ) :
    oddBasisPolynomial m none = evenPolynomial m := rfl

/-- Every paired border entry is zero after the actual source adjustment. -/
theorem realBorder_oddBasis_some (m : ℕ) (p : Fin m × Fin 2) :
    realBorder (oddBasisPolynomial m (some p)) = 0 :=
  realBorder_adjustBorder _ _ (realBorder_even_ne_zero m)

theorem realBorder_oddBasis_none_ne_zero (m : ℕ) :
    realBorder (oddBasisPolynomial m none) ≠ 0 := realBorder_even_ne_zero m

/-- Every entry of the actual paired Gram matrix is preserved. -/
theorem skewForm_oddBasis_some_some (m : ℕ) (p q : Fin m × Fin 2) :
    skewForm (oddBasisPolynomial m (some p)) (oddBasisPolynomial m (some q)) =
      skewForm (pairedPolynomial m p) (pairedPolynomial m q) :=
  skewForm_adjustBorder _ _ _ (lastEven_radical m p) (lastEven_radical m q)

theorem skewForm_oddBasis_none_some (m : ℕ) (p : Fin m × Fin 2) :
    skewForm (oddBasisPolynomial m none) (oddBasisPolynomial m (some p)) = 0 := by
  change skewForm (evenPolynomial m)
    (adjustBorder (evenPolynomial m) (pairedPolynomial m p)) = 0
  rw [adjustBorder, skewForm_sub_right, skewForm_C_mul_right,
    lastEven_radical, skewForm_self]
  ring

theorem skewForm_oddBasis_some_none (m : ℕ) (p : Fin m × Fin 2) :
    skewForm (oddBasisPolynomial m (some p)) (oddBasisPolynomial m none) = 0 := by
  rw [skewForm_antisymm, skewForm_oddBasis_none_some, neg_zero]

/-- Odd paired polynomials already have zero border, so their adjustment is literally trivial. -/
theorem oddBasisPolynomial_odd (m : ℕ) (i : Fin m) :
    oddBasisPolynomial m (some (i, 1)) = oddPolynomial i.val := by
  simp [oddBasisPolynomial, pairedPolynomial, adjustBorder, realBorder_odd]

end Paper.SkewOrthogonal
