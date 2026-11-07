/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.AffineProductIntegral

/-! # A proved continuous coefficient identity for the frozen full Pfaffian

Only entry L1 is a premise. Finite-product integrability and every interchange
are proved. This finite algebra/analysis identity does not assert an ensemble law.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
open Equiv

namespace Paper.SkewOrthogonal

/-- Actual affine entries, with independently labelled point updates. -/
def affineMatrixPolynomial {m k : ℕ} (G : Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (H : Fin k → Matrix (PairedIndex m) (PairedIndex m) ℂ) :
    Matrix (PairedIndex m) (PairedIndex m) (MvPolynomial (Fin k) ℂ) :=
  fun p q ↦ (∑ i : Fin k, MvPolynomial.C (H i p q) * MvPolynomial.X i) + MvPolynomial.C (G p q)

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

theorem integrable_coeff_pfaffian_affine {m : ℕ} (k : ℕ)
    (G : Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (H : X → Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (hH : ∀ p q, Integrable (fun u ↦ H u p q) μ) :
    Integrable (fun x : Fin k → X ↦
      (pfaffianPolynomial (affineMatrixPolynomial G (fun i ↦ H (x i)))).coeff
        (fullSquarefreeIndex k)) (Measure.pi (fun _ ↦ μ)) := by
  simp_rw [pfaffianPolynomial, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro τ hτ
  apply Integrable.const_mul
  exact integrable_coeff_affineProductPolynomial μ k
    (fun j ↦ G (τ (j,0)) (τ (j,1)))
    (fun j u ↦ H u (τ (j,0)) (τ (j,1))) (fun j ↦ hH _ _)

/-- A full coefficient of the actual finite Pfaffian sum commutes with entry integration. -/
theorem integral_coeff_pfaffian_affine {m : ℕ} (k : ℕ)
    (G : Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (H : X → Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (hH : ∀ p q, Integrable (fun u ↦ H u p q) μ) :
    (∫ x : Fin k → X,
      (pfaffianPolynomial (affineMatrixPolynomial G (fun i ↦ H (x i)))).coeff
        (fullSquarefreeIndex k) ∂(Measure.pi (fun _ ↦ μ))) =
      (pfaffianPolynomial (affineMatrixPolynomial G
        (fun _ p q ↦ ∫ u, H u p q ∂μ))).coeff (fullSquarefreeIndex k) := by
  simp_rw [pfaffianPolynomial, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [integral_const_mul, integral_finsetSum _ (fun τ _ ↦
    (integrable_coeff_affineProductPolynomial μ k
      (fun j ↦ G (τ (j,0)) (τ (j,1)))
      (fun j u ↦ H u (τ (j,0)) (τ (j,1))) (fun j ↦ hH _ _)).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [integral_const_mul]
  exact congrArg (fun c ↦ permutationSign τ * c)
    (integral_coeff_affineProductPolynomial μ k
      (fun j ↦ G (τ (j,0)) (τ (j,1)))
      (fun j u ↦ H u (τ (j,0)) (τ (j,1))) (fun j ↦ hH _ _))

/-- The same normalized full permutation sum over ordinary polynomial entries. -/
def univariatePfaffianPolynomial {m : ℕ}
    (M : Matrix (PairedIndex m) (PairedIndex m) (Polynomial ℂ)) : Polynomial ℂ :=
  Polynomial.C (((2 : ℂ) ^ m * (m.factorial : ℂ))⁻¹) *
    ∑ τ : Perm (PairedIndex m), Polynomial.C (permutationSign τ) *
      ∏ i : Fin m, M (τ (i,0)) (τ (i,1))

/-- An actual one-parameter affine matrix, without any stochastic interpretation. -/
def univariateAffineMatrix {m : ℕ} (G h : Matrix (PairedIndex m) (PairedIndex m) ℂ) :
    Matrix (PairedIndex m) (PairedIndex m) (Polynomial ℂ) :=
  fun p q ↦ Polynomial.C (h p q) * Polynomial.X + Polynomial.C (G p q)

theorem diagonalLift_univariatePfaffian {m : ℕ} (k : ℕ)
    (M : Matrix (PairedIndex m) (PairedIndex m) (Polynomial ℂ)) :
    diagonalLift k (univariatePfaffianPolynomial M) =
      pfaffianPolynomial (fun p q ↦ diagonalLift k (M p q)) := by
  simp [diagonalLift, univariatePfaffianPolynomial, pfaffianPolynomial,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetProd, Polynomial.eval₂_mul]

theorem diagonalLift_univariateAffine {m : ℕ} (k : ℕ)
    (G h : Matrix (PairedIndex m) (PairedIndex m) ℂ) :
    (fun p q ↦ diagonalLift k (univariateAffineMatrix G h p q)) =
      affineMatrixPolynomial G (fun _ ↦ h) := by
  ext p q
  simp [diagonalLift, univariateAffineMatrix, affineMatrixPolynomial, Finset.mul_sum]

/-- The exact factorial/coefficient identity, with genuine L1 and Fubini prerequisites. -/
theorem integral_coeff_pfaffian_affine_eq_factorial {m : ℕ} (k : ℕ)
    (G : Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (H : X → Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (hH : ∀ p q, Integrable (fun u ↦ H u p q) μ) :
    (∫ x : Fin k → X,
      (pfaffianPolynomial (affineMatrixPolynomial G (fun i ↦ H (x i)))).coeff
        (fullSquarefreeIndex k) ∂(Measure.pi (fun _ ↦ μ))) =
      (k.factorial : ℂ) *
        (univariatePfaffianPolynomial (univariateAffineMatrix G
          (fun p q ↦ ∫ u, H u p q ∂μ))).coeff k := by
  rw [integral_coeff_pfaffian_affine μ k G H hH]
  let h : Matrix (PairedIndex m) (PairedIndex m) ℂ := fun p q ↦ ∫ u, H u p q ∂μ
  have hd : diagonalLift k (univariatePfaffianPolynomial (univariateAffineMatrix G h)) =
      pfaffianPolynomial (affineMatrixPolynomial G (fun _ ↦ h)) := by
    rw [diagonalLift_univariatePfaffian, diagonalLift_univariateAffine]
  calc
    _ = (diagonalLift k (univariatePfaffianPolynomial (univariateAffineMatrix G h))).coeff
        (fullSquarefreeIndex k) := by
      simpa only [h] using! congrArg (fun p ↦ p.coeff (fullSquarefreeIndex k)) hd.symm
    _ = _ := coeff_diagonalLift k _

end Paper.SkewOrthogonal
