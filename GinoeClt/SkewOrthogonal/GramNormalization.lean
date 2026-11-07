/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.OddBasis
public import GinoeClt.Algebra.Pfaffian

/-! # Finite Pfaffian normalization of the actual Gaussian skew Gram matrices -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace Paper.SkewOrthogonal

/-- The exact source skew norm, as a complex scalar. -/
def skewNorm (j : ℕ) : ℂ :=
  ((2 * Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((2 * j).factorial : ℂ)

theorem skewNorm_ne_zero (j : ℕ) : skewNorm j ≠ 0 := by
  unfold skewNorm
  exact_mod_cast (skew_norm_pos j).ne'

/-- The actual skew Gram matrix of the source paired polynomials. -/
def pairedGram (m : ℕ) : Matrix (PairedIndex m) (PairedIndex m) ℂ :=
  fun p q ↦ skewForm (pairedPolynomial m p) (pairedPolynomial m q)

theorem pairedGram_eq_interlaced (m : ℕ) :
    pairedGram m = interlacedMatrix (Matrix.diagonal (fun i : Fin m ↦ skewNorm i.val)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b
  · simp [pairedGram, pairedPolynomial, interlacedMatrix, skewForm_even_even]
  · by_cases h : i = j
    · subst j
      simp [pairedGram, pairedPolynomial, interlacedMatrix, Matrix.diagonal,
        skewForm_even_odd, skewNorm]
    · have hv : i.val ≠ j.val := fun hh ↦ h (Fin.ext hh)
      simp [pairedGram, pairedPolynomial, interlacedMatrix, Matrix.diagonal,
        skewForm_even_odd, h, hv, skewNorm]
  · by_cases h : i = j
    · subst j
      simp [pairedGram, pairedPolynomial, interlacedMatrix, Matrix.diagonal,
        skewForm_antisymm (evenPolynomial i.val) (oddPolynomial i.val),
        skewForm_even_odd, skewNorm]
    · have hv : j.val ≠ i.val := fun hh ↦ h (Fin.ext hh.symm)
      simp [pairedGram, pairedPolynomial, interlacedMatrix, Matrix.diagonal,
        skewForm_antisymm (evenPolynomial j.val) (oddPolynomial i.val),
        skewForm_even_odd, Ne.symm h, hv, skewNorm]
  · simp [pairedGram, pairedPolynomial, interlacedMatrix, skewForm_odd_odd]

/-- The even-size full Pfaffian is the product of the actual nonzero skew norms. -/
theorem pfaffian_pairedGram (m : ℕ) :
    pfaffian (pairedGram m) = ∏ i : Fin m, skewNorm i.val := by
  rw [pairedGram_eq_interlaced, pfaffian_interlacedMatrix_det, Matrix.det_diagonal]

theorem pfaffian_pairedGram_ne_zero (m : ℕ) : pfaffian (pairedGram m) ≠ 0 := by
  rw [pfaffian_pairedGram]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ skewNorm_ne_zero i.val)

/-- The polynomial associated with each nonborder row of the odd augmented matrix.
At the last pair, side zero is the unchanged final even polynomial. -/
def oddPolynomialAt (m : ℕ) (i : Fin (m + 1)) (a : Fin 2) : Polynomial ℂ :=
  Fin.lastCases (evenPolynomial m)
    (fun j : Fin m ↦ oddBasisPolynomial m (some (j, a))) i

/-- The final side-one index represents the border, rather than a polynomial row. -/
def isBorderIndex (m : ℕ) (p : PairedIndex (m + 1)) : Prop :=
  p.1 = Fin.last m ∧ p.2 = 1

instance (m : ℕ) (p : PairedIndex (m + 1)) : Decidable (isBorderIndex m p) := inferInstanceAs
  (Decidable (p.1 = Fin.last m ∧ p.2 = 1))

/-- The actual odd-size adjusted skew Gram matrix with its Gaussian border. -/
def oddAugmentedGram (m : ℕ) : Matrix (PairedIndex (m + 1)) (PairedIndex (m + 1)) ℂ :=
  fun p q ↦ if isBorderIndex m p then
      if isBorderIndex m q then 0 else -realBorder (oddPolynomialAt m q.1 q.2)
    else if isBorderIndex m q then realBorder (oddPolynomialAt m p.1 p.2)
    else skewForm (oddPolynomialAt m p.1 p.2) (oddPolynomialAt m q.1 q.2)

/-- The last weight is the actual unchanged final Gaussian border moment. -/
def oddNormWeight (m : ℕ) (i : Fin (m + 1)) : ℂ :=
  Fin.lastCases (realBorder (evenPolynomial m)) (fun j : Fin m ↦ skewNorm j.val) i

theorem pairedPolynomial_pairing (m : ℕ) (p q : PairedIndex m) :
    skewForm (pairedPolynomial m p) (pairedPolynomial m q) =
      interlacedMatrix (Matrix.diagonal (fun i : Fin m ↦ skewNorm i.val)) p q :=
  congrArg (fun A ↦ A p q) (pairedGram_eq_interlaced m)

theorem lastEven_modified_zero (m : ℕ) (p : PairedIndex m) :
    skewForm (evenPolynomial m) (oddBasisPolynomial m (some p)) = 0 :=
  skewForm_oddBasis_none_some m p

theorem modified_lastEven_zero (m : ℕ) (p : PairedIndex m) :
    skewForm (oddBasisPolynomial m (some p)) (evenPolynomial m) = 0 :=
  skewForm_oddBasis_some_none m p

/-- Every entry of the actual bordered odd Gram matrix has the exact diagonal skew-block form. -/
theorem oddAugmentedGram_eq_interlaced (m : ℕ) :
    oddAugmentedGram m = interlacedMatrix (Matrix.diagonal (oddNormWeight m)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    fin_cases a <;> fin_cases b <;>
    simp [oddAugmentedGram, isBorderIndex, oddPolynomialAt, oddNormWeight,
      interlacedMatrix, Matrix.diagonal, realBorder_oddBasis_some,
      skewForm_oddBasis_some_some, lastEven_modified_zero, modified_lastEven_zero,
      pairedPolynomial_pairing, skewForm_even_even]
  all_goals
    intro h
    exact ((ne_of_lt (Fin.castSucc_lt_last _)) h.symm).elim

/-- The odd-size full Pfaffian is the final Gaussian border times the paired norm product. -/
theorem pfaffian_oddAugmentedGram (m : ℕ) :
    pfaffian (oddAugmentedGram m) =
      realBorder (evenPolynomial m) * ∏ i : Fin m, skewNorm i.val := by
  rw [oddAugmentedGram_eq_interlaced, pfaffian_interlacedMatrix_det, Matrix.det_diagonal,
    Fin.prod_univ_castSucc]
  simp only [oddNormWeight, Fin.lastCases_castSucc, Fin.lastCases_last]
  ring

theorem pfaffian_oddAugmentedGram_ne_zero (m : ℕ) : pfaffian (oddAugmentedGram m) ≠ 0 := by
  rw [pfaffian_oddAugmentedGram]
  exact mul_ne_zero (realBorder_even_ne_zero m)
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ skewNorm_ne_zero i.val))

end Paper.SkewOrthogonal
