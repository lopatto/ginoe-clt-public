/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.CountGeneratingIdentity
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Classical
namespace Paper
open Paper.Spectral Paper.SkewOrthogonal

/-- Actual even factorial moments equal the original balanced kernel integral
on the raw scaled domain, with no correlation-density hypothesis. -/
theorem countFactorialMoment_eq_balancedIntegral_even (A : Set ℂ) (hA : IsOpen A)
    (n m : ℕ) (hN : n+1 = 2*m) (hupper : ∀ a ∈ A, 0 < a.im) (k : ℕ) :
    (countFactorialMoment A n k : ℂ) =
      ∫ x : Fin k → ℂ, pfaffian (atomicFeatureKernel (fun i : Fin m ↦ skewNorm i.val)
        (balancedFeatures (fun u p ↦ (pairedPolynomial m p).eval u) x))
        ∂Measure.pi (fun _ ↦ volume.restrict (scaledCountDomain n A)) := by
  have hc := congrArg (fun p : Polynomial ℂ ↦ p.coeff k)
    (countGeneratingPolynomial_even A hA n m hN hupper)
  rw [countGeneratingPolynomial_coeff] at hc
  have hi := integral_pfaffian_balanced_even m k (scaledCountDomain n A)
    (isOpen_scaledCountDomain A hA n).measurableSet (scaledCountDomain_upper A n hupper)
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  calc
    _ = (k.factorial : ℂ)*((countFactorialMoment A n k : ℂ)/(k.factorial : ℂ)) := by
      field_simp
    _ = _ := (congrArg (fun c : ℂ ↦ (k.factorial : ℂ)*c) hc).trans hi.symm

/-- Actual odd factorial moments, including size one, use the unchanged Gaussian
border normalization and the original adjusted source features. -/
theorem countFactorialMoment_eq_balancedIntegral_odd (A : Set ℂ) (hA : IsOpen A)
    (n m : ℕ) (hN : n+1 = 2*m+1) (hupper : ∀ a ∈ A, 0 < a.im) (k : ℕ) :
    (countFactorialMoment A n k : ℂ) =
      ∫ x : Fin k → ℂ, pfaffian (atomicFeatureKernel (oddNormWeight m)
        (balancedFeatures (adjustedOddEvaluation m) x))
        ∂Measure.pi (fun _ ↦ volume.restrict (scaledCountDomain n A)) := by
  have hc := congrArg (fun p : Polynomial ℂ ↦ p.coeff k)
    (countGeneratingPolynomial_odd A hA n m hN hupper)
  rw [countGeneratingPolynomial_coeff] at hc
  have hi := integral_pfaffian_balanced_odd m k (scaledCountDomain n A)
    (isOpen_scaledCountDomain A hA n).measurableSet (scaledCountDomain_upper A n hupper)
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  calc
    _ = (k.factorial : ℂ)*((countFactorialMoment A n k : ℂ)/(k.factorial : ℂ)) := by
      field_simp
    _ = _ := (congrArg (fun c : ℂ ↦ (k.factorial : ℂ)*c) hc).trans hi.symm

end Paper
