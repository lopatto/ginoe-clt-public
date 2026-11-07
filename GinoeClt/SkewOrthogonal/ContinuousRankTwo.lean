/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

-/
module

public import GinoeClt.SkewOrthogonal.ContinuousPfaffianCoefficient

/-! # The normalized rank-two continuous Pfaffian coefficient wrapper

This combines proved finite atomic algebra and proved entry-L1 Fubini. It does
not identify this polynomial with an ensemble generating function.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Paper.SkewOrthogonal

/-- The literal rank-two entry update, with ordinary products and no conjugation. -/
def rankTwoEntry {m : ℕ} {X : Type*} (A : X → PairedIndex m → Fin 2 → ℂ)
    (x : X) (p q : PairedIndex m) : ℂ :=
  A x p 0 * A x q 1 - A x p 1 * A x q 0

/-- The actual univariate base-normalized Gram Pfaffian, not an ensemble law. -/
def continuousAtomicGeneratingPolynomial {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {m : ℕ} (w : Fin m → ℂ) (A : X → PairedIndex m → Fin 2 → ℂ) :
    Polynomial ℂ :=
  Polynomial.C ((pfaffian (interlacedMatrix (Matrix.diagonal w)))⁻¹) *
    univariatePfaffianPolynomial (univariateAffineMatrix (interlacedMatrix (Matrix.diagonal w))
      (fun p q ↦ ∫ x, rankTwoEntry A x p q ∂μ))

/-- The univariate Pfaffian is the same actual normalized full permutation sum. -/
theorem eval_univariatePfaffianPolynomial {m : ℕ}
    (M : Matrix (PairedIndex m) (PairedIndex m) (Polynomial ℂ)) (t : ℂ) :
    (univariatePfaffianPolynomial M).eval t =
      pfaffian (fun p q ↦ (M p q).eval t) := by
  simp [univariatePfaffianPolynomial, pfaffian, Polynomial.eval_finsetSum,
    Polynomial.eval_prod]

theorem eval_continuousAtomicGeneratingPolynomial {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {m : ℕ} (w : Fin m → ℂ) (A : X → PairedIndex m → Fin 2 → ℂ) (t : ℂ) :
    (continuousAtomicGeneratingPolynomial μ w A).eval t =
      pfaffian (fun p q ↦ interlacedMatrix (Matrix.diagonal w) p q +
        t * ∫ x, rankTwoEntry A x p q ∂μ) /
          pfaffian (interlacedMatrix (Matrix.diagonal w)) := by
  let G := interlacedMatrix (Matrix.diagonal w)
  let h : Matrix (PairedIndex m) (PairedIndex m) ℂ := fun p q ↦ ∫ x, rankTwoEntry A x p q ∂μ
  change (Polynomial.C ((pfaffian G)⁻¹) *
    univariatePfaffianPolynomial (univariateAffineMatrix G h)).eval t =
      pfaffian (fun p q ↦ G p q + t * h p q) / pfaffian G
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_univariatePfaffianPolynomial]
  have hm : (fun p q ↦ (univariateAffineMatrix G h p q).eval t) =
      fun p q ↦ G p q + t * h p q := by
    funext p q
    simp only [univariateAffineMatrix, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hm, div_eq_mul_inv, mul_comm]

/-- Matrix-entry order is the only bridge between the atomic and affine encodings. -/
theorem atomicGramPolynomial_eq_affine {X : Type*} {m k : ℕ}
    (w : Fin m → ℂ) (A : X → PairedIndex m → Fin 2 → ℂ) (x : Fin k → X) :
    atomicGramPolynomial w (fun i ↦ A (x i)) =
      affineMatrixPolynomial (interlacedMatrix (Matrix.diagonal w))
        (fun i ↦ rankTwoEntry A (x i)) := by
  funext p q
  change MvPolynomial.C (interlacedMatrix (Matrix.diagonal w) p q) +
      ∑ i : Fin k, MvPolynomial.X i * MvPolynomial.C (rankTwoEntry A (x i) p q) =
    (∑ i : Fin k, MvPolynomial.C (rankTwoEntry A (x i) p q) * MvPolynomial.X i) +
      MvPolynomial.C (interlacedMatrix (Matrix.diagonal w) p q)
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem atomicGeneratingPolynomial_eq_affine {X : Type*} {m k : ℕ}
    (w : Fin m → ℂ) (A : X → PairedIndex m → Fin 2 → ℂ) (x : Fin k → X) :
    atomicGeneratingPolynomial w (fun i ↦ A (x i)) =
      MvPolynomial.C ((pfaffian (interlacedMatrix (Matrix.diagonal w)))⁻¹) *
        pfaffianPolynomial (affineMatrixPolynomial (interlacedMatrix (Matrix.diagonal w))
          (fun i ↦ rankTwoEntry A (x i))) := by
  rw [atomicGeneratingPolynomial, atomicGramPolynomial_eq_affine]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Genuine kernel-Pfaffian L1 follows from rank-two entry L1 and the proved mixed coefficient identity. -/
theorem integrable_pfaffian_atomicFeatureKernel {m : ℕ} (k : ℕ)
    (w : Fin m → ℂ) (hw : ∀ i, w i ≠ 0) (A : X → PairedIndex m → Fin 2 → ℂ)
    (hA : ∀ p q, Integrable (fun x ↦ rankTwoEntry A x p q) μ) :
    Integrable (fun x : Fin k → X ↦ pfaffian (atomicFeatureKernel w (fun i ↦ A (x i))))
      (Measure.pi (fun _ ↦ μ)) := by
  simp_rw [← coeff_atomicGeneratingPolynomial_kernel w hw,
    atomicGeneratingPolynomial_eq_affine, MvPolynomial.coeff_C_mul]
  exact (integrable_coeff_pfaffian_affine μ k
    (interlacedMatrix (Matrix.diagonal w)) (rankTwoEntry A) hA).const_mul _

/-- All k,m, including0: the exact normalized finite Pfaffian coefficient integral.
The entry-integrability premise is an ordinary discharged proof prerequisite, not an external assumption. -/
theorem integral_pfaffian_atomicFeatureKernel {m : ℕ} (k : ℕ)
    (w : Fin m → ℂ) (hw : ∀ i, w i ≠ 0) (A : X → PairedIndex m → Fin 2 → ℂ)
    (hA : ∀ p q, Integrable (fun x ↦ rankTwoEntry A x p q) μ) :
    (∫ x : Fin k → X, pfaffian (atomicFeatureKernel w (fun i ↦ A (x i)))
      ∂(Measure.pi (fun _ ↦ μ))) =
      (k.factorial : ℂ) * (continuousAtomicGeneratingPolynomial μ w A).coeff k := by
  simp_rw [← coeff_atomicGeneratingPolynomial_kernel w hw,
    atomicGeneratingPolynomial_eq_affine, MvPolynomial.coeff_C_mul]
  rw [integral_const_mul, integral_coeff_pfaffian_affine_eq_factorial μ k
    (interlacedMatrix (Matrix.diagonal w)) (rankTwoEntry A) hA]
  simp only [continuousAtomicGeneratingPolynomial, Polynomial.coeff_C_mul]
  ring

end Paper.SkewOrthogonal
