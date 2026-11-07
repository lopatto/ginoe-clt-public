/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.SingleBorderFeature
public import GinoeClt.SkewOrthogonal.FeatureTransport
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ComplexConjugate NNReal Matrix
namespace Paper.SkewOrthogonal

/-- Polynomial-valued version of the EXISTING rawOddEvaluation, without adjusting
any nonborder polynomial or the final even polynomial. -/
def rawOddPolynomial (m : ℕ) (p : PairedIndex (m+1)) : Polynomial ℂ :=
  if isBorderIndex m p then 0
  else extendedPolynomial m (pairedPolynomial m) (evenPolynomial m) p

theorem rawOddPolynomial_eval (m : ℕ) (p : PairedIndex (m+1)) (z : ℂ) :
    (rawOddPolynomial m p).eval z = rawOddEvaluation m z p := by
  by_cases hp : isBorderIndex m p <;> simp [rawOddPolynomial,rawOddEvaluation,hp]

theorem isBorderIndex_iff_eq_last_one (m : ℕ) (p : PairedIndex (m+1)) :
    isBorderIndex m p ↔ p = (Fin.last m,1) := by
  simp only [isBorderIndex,Prod.ext_iff]

@[simp] theorem rawOddPolynomial_border (m : ℕ) : rawOddPolynomial m (Fin.last m,1) = 0 := by
  simp [rawOddPolynomial,isBorderIndex]

/-- The last even polynomial is LITERALLY unchanged, including m=0. -/
@[simp] theorem rawOddPolynomial_last_even (m : ℕ) :
    rawOddPolynomial m (Fin.last m,0) = evenPolynomial m := by
  simp [rawOddPolynomial,isBorderIndex,extendedPolynomial]

/-- The original raw bordered Gram, reconstructed from the zero border polynomial
and the genuine Gaussian moment. No weighted radical assumption occurs. -/
theorem rawOddPolynomial_gram (m : ℕ) (p q : PairedIndex (m+1)) :
    skewForm (rawOddPolynomial m p) (rawOddPolynomial m q) +
      realBorder (rawOddPolynomial m p) * (if q = (Fin.last m,1) then (1 : ℂ) else 0) -
      (if p = (Fin.last m,1) then (1 : ℂ) else 0) * realBorder (rawOddPolynomial m q) =
        rawOddAugmentedGram m p q := by
  have hzR (P : Polynomial ℂ) : skewForm P 0 = 0 := by
    simpa using skewForm_C_mul_right P 1 0
  have hzL (P : Polynomial ℂ) : skewForm 0 P = 0 := by
    rw [skewForm_antisymm,hzR,neg_zero]
  have hb0 : realBorder 0 = 0 := by simpa using realBorder_C_mul 1 0
  simp only [← isBorderIndex_iff_eq_last_one]
  by_cases hp : isBorderIndex m p <;> by_cases hq : isBorderIndex m q <;>
    simp [rawOddPolynomial,rawOddAugmentedGram,borderedGram,hp,hq,hzR,hzL,hb0]

/-- The ACTUAL continuous odd source Gram entry is the old raw bordered Gram plus
the raw evaluation update. Coefficients remain unconjugated at every occurrence. -/
theorem integral_rawOddBorderFeature_wedge (B : Set ℂ) (hB : MeasurableSet B)
    (hupper : B ⊆ {z : ℂ | 0 < z.im}) (t : ℝ≥0) (m : ℕ)
    (p q : PairedIndex (m+1)) :
    (∫ s, deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1) s p 0 *
      deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1) s q 1 -
      deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1) s p 1 *
      deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1) s q 0
        ∂deBruijnBorderMeasure) =
      rawOddAugmentedGram m p q + (t : ℂ) *
        ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
          (rawOddEvaluation m z p * rawOddEvaluation m (conj z) q -
            rawOddEvaluation m z q * rawOddEvaluation m (conj z) p) := by
  calc
    _ = (skewForm (rawOddPolynomial m p) (rawOddPolynomial m q) +
        realBorder (rawOddPolynomial m p) * (if q = (Fin.last m,1) then (1 : ℂ) else 0) -
        (if p = (Fin.last m,1) then (1 : ℂ) else 0) * realBorder (rawOddPolynomial m q)) +
        (t : ℂ) * ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
          (rawOddEvaluation m z p * rawOddEvaluation m (conj z) q -
            rawOddEvaluation m z q * rawOddEvaluation m (conj z) p) := by
      rw [integral_deBruijnBorderFeature_wedge B hB hupper t (rawOddPolynomial m) (Fin.last m,1) p q]
      simp_rw [rawOddPolynomial_eval]
      ring
    _ = _ := by rw [rawOddPolynomial_gram]

/-- With NO singletons, the original paired determinant has a genuine zero
border row. The row index is an explicit existing element, so no empty-row claim. -/
theorem det_deBruijnBorderFeature_no_single (B : Set ℂ) (t : ℝ≥0) (m : ℕ)
    (y : Fin (m+1) → (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ))
    (hy : ∀ i, ∃ s : (ℝ × ℝ) ⊕ ℂ, y i = Sum.inl s) :
    (pairedFeatureMatrix (fun i => deBruijnBorderFeature B t (rawOddPolynomial m)
      (Fin.last m,1) (y i))).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last m,1)
  intro col
  obtain ⟨s,hs⟩ := hy col.1
  change deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)
    (y col.1) (Fin.last m,1) col.2 = 0
  rw [hs]
  exact deBruijnBorderFeature_pair_border_zero B t (rawOddPolynomial m) (Fin.last m,1)
    (rawOddPolynomial_border m) s col.2

/-- Two distinct singleton positions give identical ACTUAL side-one columns.
This elementary zero does not depend on any property of the polynomial family. -/
theorem det_deBruijnBorderFeature_two_singles (B : Set ℂ) (t : ℝ≥0) (m : ℕ)
    (P : PairedIndex (m+1) → Polynomial ℂ) (b : PairedIndex (m+1))
    (y : Fin (m+1) → (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (i j : Fin (m+1)) (hij : i ≠ j)
    (x z : ℝ) (hi : y i = Sum.inr x) (hj : y j = Sum.inr z) :
    (pairedFeatureMatrix (fun a => deBruijnBorderFeature B t P b (y a))).det = 0 := by
  have hc : ((i,1) : PairedIndex (m+1)) ≠ ((j,1) : PairedIndex (m+1)) :=
    fun h => hij (congrArg Prod.fst h)
  apply Matrix.det_zero_of_column_eq hc
  intro row
  change deBruijnBorderFeature B t P b (y i) row 1 = deBruijnBorderFeature B t P b (y j) row 1
  rw [hi,hj]
  exact congrFun (deBruijnBorderFeature_single_second_eq B t P b x z) row

end Paper.SkewOrthogonal
