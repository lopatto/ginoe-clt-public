/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.OddRawGram
public import GinoeClt.SkewOrthogonal.WeightBridge

/-! # The genuine odd source features under finite complex-pair perturbations

Mays, arXiv:1202.1218v1, Definition 4.26 and Proposition 4.27, adjusts the
paired polynomials while retaining the last even polynomial and a zero border
feature. The row transformation is fixed by the unperturbed Gaussian border.
No radical property is imposed on a perturbed skew form.
-/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace Paper.SkewOrthogonal

/-- Actual raw odd polynomial evaluations, with the border coordinate zero. -/
def rawOddEvaluation (m : ℕ) (z : ℂ) (p : PairedIndex (m + 1)) : ℂ :=
  if isBorderIndex m p then 0
  else (extendedPolynomial m (pairedPolynomial m) (evenPolynomial m) p).eval z

/-- Actual adjusted odd evaluations, with the unchanged last even polynomial. -/
def adjustedOddEvaluation (m : ℕ) (z : ℂ) (p : PairedIndex (m + 1)) : ℂ :=
  if isBorderIndex m p then 0 else (oddPolynomialAt m p.1 p.2).eval z

@[simp] theorem rawOddEvaluation_inl (m : ℕ) (z : ℂ) (p : PairedIndex m) :
    rawOddEvaluation m z ((splitLastPair m).symm (Sum.inl p)) =
      (pairedPolynomial m p).eval z := by
  simp [rawOddEvaluation, isBorderIndex, extendedPolynomial]

@[simp] theorem rawOddEvaluation_inr (m : ℕ) (z : ℂ) (a : Fin 2) :
    rawOddEvaluation m z ((splitLastPair m).symm (Sum.inr a)) =
      if a = 0 then (evenPolynomial m).eval z else 0 := by
  fin_cases a <;> simp [rawOddEvaluation, isBorderIndex, extendedPolynomial]

@[simp] theorem adjustedOddEvaluation_inl (m : ℕ) (z : ℂ) (p : PairedIndex m) :
    adjustedOddEvaluation m z ((splitLastPair m).symm (Sum.inl p)) =
      (adjustBorder (evenPolynomial m) (pairedPolynomial m p)).eval z := by
  simp [adjustedOddEvaluation, isBorderIndex, oddPolynomialAt, oddBasisPolynomial]

@[simp] theorem adjustedOddEvaluation_inr (m : ℕ) (z : ℂ) (a : Fin 2) :
    adjustedOddEvaluation m z ((splitLastPair m).symm (Sum.inr a)) =
      if a = 0 then (evenPolynomial m).eval z else 0 := by
  fin_cases a <;> simp [adjustedOddEvaluation, isBorderIndex, oddPolynomialAt]

theorem rowBasisBlock_mulVec (m : ℕ) (u f : PairedIndex m → ℂ) (d l : ℂ) :
    rowBasisBlock m u d *ᵥ Sum.elim f (fun a : Fin 2 ↦ if a = 0 then l else 0) =
      Sum.elim (fun p ↦ f p - u p / d * l) (fun a : Fin 2 ↦ if a = 0 then l else 0) := by
  rw [rowBasisBlock, Matrix.fromBlocks_mulVec]
  ext p
  rcases p with p | a
  · simp [borderAdjustment, Matrix.mulVec, dotProduct]
    ring
  · simp

/-- The fixed row matrix transports actual evaluation features for every z.
This identity is pointwise and does not presume a weighted radical property. -/
theorem oddRowBasis_mulVec_evaluation (m : ℕ) (z : ℂ) :
    oddRowBasis m *ᵥ rawOddEvaluation m z = adjustedOddEvaluation m z := by
  rw [oddRowBasis, Matrix.submatrix_mulVec_equiv]
  have hr : rawOddEvaluation m z ∘ (splitLastPair m).symm =
      Sum.elim (fun p ↦ (pairedPolynomial m p).eval z)
        (fun a : Fin 2 ↦ if a = 0 then (evenPolynomial m).eval z else 0) := by
    funext p
    rcases p with p | a
    · exact rawOddEvaluation_inl m z p
    · exact rawOddEvaluation_inr m z a
  rw [hr, rowBasisBlock_mulVec]
  funext p
  obtain ⟨q, rfl⟩ := (splitLastPair m).symm.surjective p
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rcases q with q | a
  · rw [adjustedOddEvaluation_inl]
    simp [adjustBorder]
  · exact (adjustedOddEvaluation_inr m z a).symm

end Paper.SkewOrthogonal
