/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Cumulants.CountGeneratingPolynomial
public import GinoeClt.SkewOrthogonal.DeBruijnOddPartition
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Classical
namespace Paper
open Paper.Spectral Paper.SkewOrthogonal

/-- The ordinary complex expectation equals the actual nonnegative count integral. -/
theorem eval_countGeneratingPolynomial_nnreal (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (t : ℝ≥0) :
    (countGeneratingPolynomial A n).eval (t : ℂ) =
      Complex.ofReal (∫⁻ M : SampleSpace n,
        (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n).toReal := by
  have hm : Measurable (fun M : SampleSpace n ↦ (1+(t : ℝ))^count A n M) :=
    (measurable_of_countable (fun k : ℕ ↦ (1+(t : ℝ))^k)).comp
      (measurable_count_nat_of_isOpen A hA n)
  have hn : ∀ M : SampleSpace n, 0 ≤ (1+(t : ℝ))^count A n M := fun _ ↦ by positivity
  have hi := integral_eq_lintegral_of_nonneg_ae (μ := matrixLaw n) (Filter.Eventually.of_forall hn)
    hm.aestronglyMeasurable
  have he (M : SampleSpace n) :
      ENNReal.ofReal ((1+(t : ℝ))^count A n M) = (1+(t : ℝ≥0∞))^count A n M := by
    rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_add (by positivity) t.coe_nonneg]
    simp
  calc
    _ = ∫ M : SampleSpace n, (1+(t : ℂ))^count A n M ∂matrixLaw n :=
      eval_countGeneratingPolynomial (countMeasurable_of_isOpen A hA) n (t : ℂ)
    _ = Complex.ofReal (∫ M : SampleSpace n, (1+(t : ℝ))^count A n M ∂matrixLaw n) := by
      simpa only [RCLike.ofReal_pow,RCLike.ofReal_add,RCLike.ofReal_one] using!
        (integral_ofReal (𝕜 := ℂ) (μ := matrixLaw n)
          (f := fun M : SampleSpace n ↦ (1+(t : ℝ))^count A n M))
    _ = _ := by
      rw [hi]
      simp_rw [he]

/-- Polynomial extensionality on nonnegative parameters, proved using natural values. -/
theorem polynomial_eq_of_eval_nnreal (p q : Polynomial ℂ)
    (h : ∀ t : ℝ≥0, p.eval (t : ℂ) = q.eval (t : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (show Function.Injective (fun k : ℕ ↦ (k : ℂ)) from Nat.cast_injective)).mono
  rintro z ⟨k,rfl⟩
  simpa using! h (k : ℝ≥0)

/-- Exact actual count polynomial identity at every physical EVEN size. -/
theorem countGeneratingPolynomial_even (A : Set ℂ) (hA : IsOpen A)
    (n m : ℕ) (hN : n+1 = 2*m) (hupper : ∀ a ∈ A, 0 < a.im) :
    countGeneratingPolynomial A n =
      continuousAtomicGeneratingPolynomial (volume.restrict (scaledCountDomain n A))
        (fun i : Fin m ↦ skewNorm i.val)
        (pointBalancedFeatures (fun z p ↦ (pairedPolynomial m p).eval z)) := by
  have hB := (isOpen_scaledCountDomain A hA n).measurableSet
  have hBu := scaledCountDomain_upper A n hupper
  apply polynomial_eq_of_eval_nnreal
  intro t
  rw [eval_countGeneratingPolynomial_nnreal A hA n t,
    (countGeneratingIntegral_even_pfaffian A hA n m hN hupper t).2,
    eval_continuousAtomicGeneratingPolynomial_evenCountGram m _ hB hBu (t : ℂ)]

/-- Exact actual count polynomial identity at every physical ODD size, including one. -/
theorem countGeneratingPolynomial_odd (A : Set ℂ) (hA : IsOpen A)
    (n m : ℕ) (hN : n+1 = 2*m+1) (hupper : ∀ a ∈ A, 0 < a.im) :
    countGeneratingPolynomial A n =
      continuousAtomicGeneratingPolynomial (volume.restrict (scaledCountDomain n A))
        (oddNormWeight m) (pointBalancedFeatures (adjustedOddEvaluation m)) := by
  have hB := (isOpen_scaledCountDomain A hA n).measurableSet
  have hBu := scaledCountDomain_upper A n hupper
  apply polynomial_eq_of_eval_nnreal
  intro t
  rw [eval_countGeneratingPolynomial_nnreal A hA n t,
    (countGeneratingIntegral_odd_pfaffian A hA n m hN hupper t).2,
    eval_continuousAtomicGeneratingPolynomial_rawOddCountGram m _ hB hBu (t : ℂ)]

end Paper
