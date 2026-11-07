/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

-/
module

public import GinoeClt.SkewOrthogonal.ContinuousRankTwo
public import GinoeClt.SkewOrthogonal.SourceFeatures

/-! # Actual balanced source-feature L1 on a restricted upper-half-plane domain

Only the proved whole-upper W-polynomial integrability theorem is used.
No whole-plane identity between W and the reflected square-root weights is asserted.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Paper.SkewOrthogonal

/-- The exact existing balanced feature, evaluated at one point. -/
def pointBalancedFeatures {κ : Type*} (E : ℂ → κ → ℂ) (z : ℂ) : κ → Fin 2 → ℂ :=
  balancedFeatures E (fun _ : Fin 1 ↦ z) 0

/-- The ordinary source weighted polynomial wedge is L1 on every subdomain of the strict upper half-plane. -/
theorem integrableOn_sourcePolynomialWedge {κ : Type*} (P : κ → Polynomial ℂ)
    (B : Set ℂ) (hB : B ⊆ {z : ℂ | 0 < z.im}) (p q : κ) :
    IntegrableOn (fun z : ℂ ↦ (2 * Complex.I) * (complexWeight z : ℂ) *
      ((P p).eval z * (P q).eval (conj z) - (P p).eval (conj z) * (P q).eval z)) B := by
  have h1 := (integrableOn_complexWeight_polynomials (P p) (P q)).mono_set hB
  have h2 := (integrableOn_complexWeight_polynomials (P q) (P p)).mono_set hB
  apply ((h1.sub h2).const_mul (2 * Complex.I)).congr
  filter_upwards [] with z
  dsimp only [Pi.sub_apply]
  ring

/-- The reflected phi product is converted to W only ON the actual upper domain. -/
theorem integrableOn_rankTwo_pointBalanced_polynomial {m : ℕ}
    (P : PairedIndex m → Polynomial ℂ) (B : Set ℂ) (hBm : MeasurableSet B)
    (hB : B ⊆ {z : ℂ | 0 < z.im}) (p q : PairedIndex m) :
    IntegrableOn (fun z : ℂ ↦ rankTwoEntry
      (pointBalancedFeatures (fun u a ↦ (P a).eval u)) z p q) B := by
  apply (integrableOn_sourcePolynomialWedge P B hB p q).congr_fun ?_ hBm
  intro z hz
  have he := balancedFeatures_wedge (fun u a ↦ (P a).eval u)
    (fun _ : Fin 1 ↦ z) (fun _ ↦ (hB hz).le) (0 : Fin 1) p q
  simpa only [rankTwoEntry, pointBalancedFeatures] using he.symm

/-- Genuine even source integrability, all m including0. -/
theorem integrableOn_rankTwo_balanced_even (m : ℕ) (B : Set ℂ)
    (hBm : MeasurableSet B) (hB : B ⊆ {z : ℂ | 0 < z.im})
    (p q : PairedIndex m) :
    IntegrableOn (fun z : ℂ ↦ rankTwoEntry
      (pointBalancedFeatures (fun u a ↦ (pairedPolynomial m a).eval u)) z p q) B :=
  integrableOn_rankTwo_pointBalanced_polynomial (pairedPolynomial m) B hBm hB p q

/-- Every actual adjusted odd evaluation is an ordinary polynomial, including the zero BORDER coordinate.
The last even polynomial remains unchanged by its existing definition. -/
theorem adjustedOddEvaluation_eq_polynomial (m : ℕ) :
    (fun z p ↦ ((if isBorderIndex m p then (0 : Polynomial ℂ)
      else oddPolynomialAt m p.1 p.2)).eval z) = adjustedOddEvaluation m := by
  funext z p
  by_cases hp : isBorderIndex m p <;> simp [adjustedOddEvaluation, hp]

/-- Genuine odd source integrability; the final border evaluation is0 and is not replaced by a polynomial radical. -/
theorem integrableOn_rankTwo_balanced_odd (m : ℕ) (B : Set ℂ)
    (hBm : MeasurableSet B) (hB : B ⊆ {z : ℂ | 0 < z.im})
    (p q : PairedIndex (m + 1)) :
    IntegrableOn (fun z : ℂ ↦ rankTwoEntry
      (pointBalancedFeatures (adjustedOddEvaluation m)) z p q) B := by
  have h := integrableOn_rankTwo_pointBalanced_polynomial
    (fun p ↦ if isBorderIndex m p then (0 : Polynomial ℂ) else oddPolynomialAt m p.1 p.2)
      B hBm hB p q
  rw [adjustedOddEvaluation_eq_polynomial] at h
  exact h

/-- The actual even balanced kernel coefficient identity over ordinary restricted area.
All source entry-L1 premises are discharged; no finite density or ensemble law is asserted. -/
theorem integral_pfaffian_balanced_even (m k : ℕ) (B : Set ℂ)
    (hBm : MeasurableSet B) (hB : B ⊆ {z : ℂ | 0 < z.im}) :
    (∫ x : Fin k → ℂ, pfaffian (atomicFeatureKernel (fun i : Fin m ↦ skewNorm i.val)
      (balancedFeatures (fun u p ↦ (pairedPolynomial m p).eval u) x))
        ∂(Measure.pi (fun _ ↦ volume.restrict B))) =
      (k.factorial : ℂ) * (continuousAtomicGeneratingPolynomial (volume.restrict B)
        (fun i : Fin m ↦ skewNorm i.val)
        (pointBalancedFeatures (fun u p ↦ (pairedPolynomial m p).eval u))).coeff k := by
  simpa only [pointBalancedFeatures, balancedFeatures] using!
    integral_pfaffian_atomicFeatureKernel (volume.restrict B) k
      (fun i : Fin m ↦ skewNorm i.val) (fun i ↦ skewNorm_ne_zero i.val)
      (pointBalancedFeatures (fun u p ↦ (pairedPolynomial m p).eval u))
      (fun p q ↦ integrableOn_rankTwo_balanced_even m B hBm hB p q)

/-- The actual odd balanced kernel coefficient identity over ordinary restricted area.
The unchanged Gaussian border is in the base weight, and its point feature is0. -/
theorem integral_pfaffian_balanced_odd (m k : ℕ) (B : Set ℂ)
    (hBm : MeasurableSet B) (hB : B ⊆ {z : ℂ | 0 < z.im}) :
    (∫ x : Fin k → ℂ, pfaffian (atomicFeatureKernel (oddNormWeight m)
      (balancedFeatures (adjustedOddEvaluation m) x))
        ∂(Measure.pi (fun _ ↦ volume.restrict B))) =
      (k.factorial : ℂ) * (continuousAtomicGeneratingPolynomial (volume.restrict B)
        (oddNormWeight m) (pointBalancedFeatures (adjustedOddEvaluation m))).coeff k := by
  simpa only [pointBalancedFeatures, balancedFeatures] using!
    integral_pfaffian_atomicFeatureKernel (volume.restrict B) k
      (oddNormWeight m) (oddNormWeight_ne_zero m)
      (pointBalancedFeatures (adjustedOddEvaluation m))
      (fun p q ↦ integrableOn_rankTwo_balanced_odd m B hBm hB p q)

end Paper.SkewOrthogonal
