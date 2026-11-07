/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Cumulants.CountFactorialMoments
public import Mathlib.Algebra.Polynomial.Roots
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace Paper

/-- The genuine bounded-count factorial generating polynomial. Its coefficients
are the already-defined actual Gaussian count moments, with no ensemble assumption. -/
def countGeneratingPolynomial (A : Set ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n+2),
    Polynomial.monomial k ((countFactorialMoment A n k : ℂ)/(k.factorial : ℂ))

theorem countFactorialMoment_eq_zero_of_lt (A : Set ℂ) (n k : ℕ) (hk : n+1 < k) :
    countFactorialMoment A n k = 0 := by
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun M ↦ by
    change ((count A n M).descFactorial k : ℝ) = 0
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr ((count_le A n M).trans_lt hk)]
    simp

/-- Every coefficient, including orders beyond the actual count bound. -/
theorem countGeneratingPolynomial_coeff (A : Set ℂ) (n k : ℕ) :
    (countGeneratingPolynomial A n).coeff k =
      (countFactorialMoment A n k : ℂ)/(k.factorial : ℂ) := by
  by_cases hk : k < n+2
  · simp [countGeneratingPolynomial,Polynomial.coeff_monomial,Finset.mem_range,hk]
  · have hm := countFactorialMoment_eq_zero_of_lt A n k (by omega)
    simp [countGeneratingPolynomial,Polynomial.coeff_monomial,Finset.mem_range,hk,hm]

/-- A bounded natural power has the finite falling-factorial expansion at one. -/
theorem one_add_pow_eq_sum_descFactorial (c N : ℕ) (hc : c ≤ N) (t : ℂ) :
    (1+t)^c = ∑ k ∈ Finset.range (N+1), (c.descFactorial k : ℂ)/(k.factorial : ℂ)*t^k := by
  have hterm (k : ℕ) :
      (c.descFactorial k : ℂ)/(k.factorial : ℂ) = (c.choose k : ℂ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)
  simp_rw [hterm]
  calc
    _ = ∑ k ∈ Finset.range (c+1), (c.choose k : ℂ)*t^k := by
      rw [add_comm (1 : ℂ) t,add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [one_pow,mul_one]
      ring
    _ = _ := Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hc 1)) (by
      intro k hk hnot
      have hck : c < k := by simp only [Finset.mem_range] at hnot; omega
      rw [Nat.choose_eq_zero_of_lt hck,Nat.cast_zero,zero_mul])

theorem count_descFactorial_complex_integrable {A : Set ℂ} (h : CountMeasurable A) (n k : ℕ) :
    Integrable (fun M : SampleSpace n ↦ ((count A n M).descFactorial k : ℂ)) (matrixLaw n) := by
  simpa only [RCLike.ofReal_natCast] using!
    (count_descFactorial_integrable h n k).ofReal (𝕜 := ℂ)

theorem count_descFactorial_complex_integral (A : Set ℂ) (n k : ℕ) :
    (∫ M : SampleSpace n, ((count A n M).descFactorial k : ℂ) ∂matrixLaw n) =
      (countFactorialMoment A n k : ℂ) := by
  simpa only [countFactorialMoment,RCLike.ofReal_natCast] using!
    (integral_ofReal (𝕜 := ℂ)
      (f := fun M : SampleSpace n ↦ ((count A n M).descFactorial k : ℝ))
      (μ := matrixLaw n))

theorem integrable_countGeneratingPower {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) (t : ℂ) :
    Integrable (fun M : SampleSpace n ↦ (1+t)^count A n M) (matrixLaw n) := by
  have hI : Integrable (fun M : SampleSpace n ↦
      ∑ k ∈ Finset.range (n+2), ((count A n M).descFactorial k : ℂ)/(k.factorial : ℂ)*t^k)
      (matrixLaw n) :=
    integrable_finsetSum _ (fun k _ ↦
      ((count_descFactorial_complex_integrable h n k).div_const _).mul_const _)
  exact hI.congr (Filter.Eventually.of_forall fun M ↦
    (one_add_pow_eq_sum_descFactorial (count A n M) (n+1) (count_le A n M) t).symm)

/-- Actual expectation of the bounded count power, for every complex parameter. -/
theorem eval_countGeneratingPolynomial {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) (t : ℂ) :
    (countGeneratingPolynomial A n).eval t =
      ∫ M : SampleSpace n, (1+t)^count A n M ∂matrixLaw n := by
  have hI (k : ℕ) : Integrable
      (fun M : SampleSpace n ↦ ((count A n M).descFactorial k : ℂ)/(k.factorial : ℂ)*t^k)
      (matrixLaw n) :=
    ((count_descFactorial_complex_integrable h n k).div_const _).mul_const _
  calc
    _ = ∑ k ∈ Finset.range (n+2), ((countFactorialMoment A n k : ℂ)/(k.factorial : ℂ))*t^k := by
      simp only [countGeneratingPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
    _ = ∑ k ∈ Finset.range (n+2), ∫ M : SampleSpace n,
        ((count A n M).descFactorial k : ℂ)/(k.factorial : ℂ)*t^k ∂matrixLaw n := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_mul_const,integral_div,count_descFactorial_complex_integral]
    _ = ∫ M : SampleSpace n, ∑ k ∈ Finset.range (n+2),
        ((count A n M).descFactorial k : ℂ)/(k.factorial : ℂ)*t^k ∂matrixLaw n :=
      (integral_finsetSum _ (fun k _ ↦ hI k)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun M ↦
      (one_add_pow_eq_sum_descFactorial (count A n M) (n+1) (count_le A n M) t).symm)

end Paper
