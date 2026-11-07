/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.RealIBP
public import GinoeClt.SkewOrthogonal.MixedProductIntegral
public import GinoeClt.Algebra.PfaffianMinorCoordinates
@[expose] public section
noncomputable section
open MeasureTheory Set Classical
open scoped BigOperators ComplexConjugate NNReal
namespace Paper.SkewOrthogonal

/-- One actual complex-pair factor, with the count test applied once to the upper root. -/
def complexCountPolynomial (B : Set ℂ) (t : ℝ≥0) (P Q : Polynomial ℂ) (z : ℂ) : ℂ :=
  (complexWeight z : ℂ) * (if z ∈ B then 1 + (t : ℂ) else 1) *
    P.eval z * Q.eval (conj z)

theorem integrable_complexCountPolynomial (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (P Q : Polynomial ℂ) :
    Integrable (complexCountPolynomial B t P Q)
      (volume.restrict {z : ℂ | 0 < z.im}) := by
  classical
  have h := integrableOn_complexWeight_polynomials P Q
  apply (h.add ((h.indicator hB).const_mul (t : ℂ))).congr
  filter_upwards [] with z
  by_cases hz : z ∈ B <;>
    simp [complexCountPolynomial, hz, Set.indicator_of_mem, Set.indicator_of_notMem]; ring

/-- A separated mixed product with respect to ordinary real and upper-complex volume. -/
def mixedPolynomialProduct {k l : ℕ} (B : Set ℂ) (t : ℝ≥0)
    (R : Fin k → Polynomial ℂ) (P Q : Fin l → Polynomial ℂ)
    (xz : (Fin k → ℝ) × (Fin l → ℂ)) : ℂ :=
  (∏ i, realGaussianPolynomial (R i) (xz.1 i)) *
    ∏ j, complexCountPolynomial B t (P j) (Q j) (xz.2 j)

theorem integrable_mixedPolynomialProduct {k l : ℕ} (B : Set ℂ)
    (hB : MeasurableSet B) (t : ℝ≥0) (R : Fin k → Polynomial ℂ)
    (P Q : Fin l → Polynomial ℂ) :
    Integrable (mixedPolynomialProduct B t R P Q)
      ((Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : Fin l ↦ volume.restrict {z : ℂ | 0 < z.im}))) := by
  exact (Integrable.fintype_prod (fun i ↦ integrable_realGaussianPolynomial (R i))).mul_prod
    (Integrable.fintype_prod (fun j ↦ integrable_complexCountPolynomial B hB t (P j) (Q j)))

/-- Real coordinates followed by adjacent upper/conjugate pairs, with full multiplicity. -/
def mixedRoots (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) : Fin (k + 2 * l) → ℂ :=
  Fin.append (fun i ↦ (x i : ℂ)) (fun i ↦
    let p := (PfaffianMinor.pairColumnEquiv l).symm i
    if p.2 = 0 then z p.1 else conj (z p.1))

/-- The exact scalar factors multiplying the mixed determinant. -/
def mixedDeterminantWeight (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) : ℂ :=
  (∏ i, (Real.exp (-(x i)^2 / 2) : ℂ)) *
    ∏ j, ((complexWeight (z j) : ℂ) * (if z j ∈ B then 1 + (t : ℂ) else 1))

theorem mixedWeight_mul_permTerm (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (P : Fin (k + 2*l) → Polynomial ℂ) (σ : Equiv.Perm (Fin (k + 2*l)))
    (x : Fin k → ℝ) (z : Fin l → ℂ) :
    mixedDeterminantWeight B t k l x z *
      (∏ i, (P (σ i)).eval (mixedRoots k l x z i)) =
    mixedPolynomialProduct B t
      (fun i ↦ P (σ (Fin.castAdd (2*l) i)))
      (fun j ↦ P (σ (Fin.natAdd k (PfaffianMinor.pairColumnEquiv l (j,0)))))
      (fun j ↦ P (σ (Fin.natAdd k (PfaffianMinor.pairColumnEquiv l (j,1))))) (x,z) := by
  simp only [mixedDeterminantWeight, mixedPolynomialProduct, realGaussianPolynomial,
    complexCountPolynomial, Fin.prod_univ_add, mixedRoots, Fin.append_left, Fin.append_right]
  rw [← (PfaffianMinor.pairColumnEquiv l).prod_comp]
  simp only [Equiv.symm_apply_apply, Fintype.prod_prod_type, Fin.prod_univ_two]
  simp only [Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  simp only [Finset.prod_mul_distrib]
  ring

/-- Every term of the determinant expansion is L1 before any interchange. -/
theorem integrable_mixedDeterminant (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) (P : Fin (k + 2*l) → Polynomial ℂ) :
    Integrable (fun xz : (Fin k → ℝ) × (Fin l → ℂ) ↦
      mixedDeterminantWeight B t k l xz.1 xz.2 *
        (Matrix.of (fun i j ↦ (P i).eval (mixedRoots k l xz.1 xz.2 j))).det)
      ((Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : Fin l ↦ volume.restrict {z : ℂ | 0 < z.im}))) := by
  simp_rw [Matrix.det_apply', Finset.mul_sum]
  apply integrable_finsetSum
  intro σ hσ
  have h := integrable_mixedPolynomialProduct B hB t
    (fun i ↦ P (σ (Fin.castAdd (2*l) i)))
    (fun j ↦ P (σ (Fin.natAdd k (PfaffianMinor.pairColumnEquiv l (j,0)))))
    (fun j ↦ P (σ (Fin.natAdd k (PfaffianMinor.pairColumnEquiv l (j,1)))))
  apply (h.const_mul ((Equiv.Perm.sign σ : ℤ) : ℂ)).congr
  filter_upwards [] with xz
  rw [← mixedWeight_mul_permTerm]
  simp only [Matrix.of_apply]
  ring

end Paper.SkewOrthogonal
