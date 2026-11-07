/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.Weight
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The actual planar Gaussian monomial pairing -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Real

namespace Paper.SkewOrthogonal

/-- Every nonzero integral angular frequency has zero ordinary angular integral. -/
theorem angular_frequency_Ioo (k : ℤ) (hk : k ≠ 0) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      Complex.exp (((k : ℂ) * Complex.I) * (θ : ℂ))) = 0 := by
  have hc : (k : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
  have h := _root_.integral_exp_mul_complex
    (a := -Real.pi) (b := Real.pi) hc
  have hp : (k : ℂ) * Complex.I * (Real.pi : ℂ) =
      (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by ring
  have hm : (k : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) =
      (k : ℂ) * (-((Real.pi : ℂ) * Complex.I)) := by push_cast; ring
  rw [hp, hm, Complex.exp_int_mul, Complex.exp_int_mul, Complex.exp_neg,
    Complex.exp_pi_mul_I] at h
  norm_num at h
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  exact h

/-- The diagonal moment has the exact factorial normalization for ordinary planar volume. -/
theorem gaussian_monomial_diagonal (n : ℕ) :
    (∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) * z ^ n * (starRingEnd ℂ z) ^ n) =
      (Real.pi : ℂ) * (n.factorial : ℂ) := by
  have heq : (fun z : ℂ ↦ (Real.exp (-‖z‖ ^ 2) : ℂ) * z ^ n * (starRingEnd ℂ z) ^ n) =
      fun z ↦ ((‖z‖ ^ (2 * n) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
    funext z
    calc
      _ = (Real.exp (-‖z‖ ^ 2) : ℂ) * (z * starRingEnd ℂ z) ^ n := by
        rw [mul_pow]
        ring
      _ = _ := by
        rw [Complex.mul_conj']
        push_cast
        rw [pow_mul]
        ring
  rw [heq, integral_complex_ofReal]
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := ((2 * n : ℕ) : ℝ)) (b := 1) (by norm_num)
    (by have hn := Nat.cast_nonneg (α := ℝ) (2 * n); linarith) (by norm_num)
  simp only [Real.rpow_natCast, Real.rpow_two, neg_mul, one_mul] at h
  have hg : Real.Gamma ((((2 * n : ℕ) : ℝ) + 2) / 2) = (n.factorial : ℝ) := by
    rw [show (((2 * n : ℕ) : ℝ) + 2) / 2 = (n : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  rw [h, hg]
  norm_num

theorem exp_monomial_frequency (n m : ℕ) (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ n *
      (starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I))) ^ m =
        Complex.exp (((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I) * (θ : ℂ)) := by
  have hc : starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [hc, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The polar integrand separates into its genuine radial and integral-frequency factors. -/
theorem gaussian_monomial_polar (n m : ℕ) (p : ℝ × ℝ) (hr : 0 < p.1) :
    p.1 • ((Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2) : ℂ) *
      (Complex.polarCoord.symm p) ^ n * (starRingEnd ℂ (Complex.polarCoord.symm p)) ^ m) =
      ((p.1 : ℂ) ^ (n + m + 1) * (Real.exp (-p.1 ^ 2) : ℂ)) *
        Complex.exp (((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I) * (p.2 : ℂ)) := by
  have hp : Complex.polarCoord.symm p =
      (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
    simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  rw [Complex.norm_polarCoord_symm, abs_of_pos hr, hp]
  simp only [mul_pow, map_mul, Complex.conj_ofReal, Complex.real_smul]
  calc
    _ = ((p.1 : ℂ) ^ (n + m + 1) * (Real.exp (-p.1 ^ 2) : ℂ)) *
        (Complex.exp ((p.2 : ℂ) * Complex.I) ^ n *
          (starRingEnd ℂ (Complex.exp ((p.2 : ℂ) * Complex.I))) ^ m) := by
      simp only [pow_add, pow_one]
      ring
    _ = _ := by rw [exp_monomial_frequency]

/-- Every off-diagonal planar Gaussian monomial pairing vanishes. -/
theorem gaussian_monomial_offDiagonal (n m : ℕ) (hnm : n ≠ m) :
    (∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) * z ^ n * (starRingEnd ℂ z) ^ m) = 0 := by
  have hk : (n : ℤ) - (m : ℤ) ≠ 0 := by
    intro h
    apply hnm
    exact_mod_cast sub_eq_zero.mp h
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  calc
    _ = ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        ((p.1 : ℂ) ^ (n + m + 1) * (Real.exp (-p.1 ^ 2) : ℂ)) *
          Complex.exp (((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I) * (p.2 : ℂ)) := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      exact gaussian_monomial_polar n m p hp.1
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) ^ (n + m + 1) * (Real.exp (-r ^ 2) : ℂ)) *
        ∫ θ in Ioo (-Real.pi) Real.pi,
          Complex.exp (((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I) * (θ : ℂ)) := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod_mul
        (fun r : ℝ ↦ (r : ℂ) ^ (n + m + 1) * (Real.exp (-r ^ 2) : ℂ))
        (fun θ : ℝ ↦ Complex.exp
          (((((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I) * (θ : ℂ)))
        (Ioi 0) (Ioo (-Real.pi) Real.pi)
    _ = 0 := by rw [angular_frequency_Ioo _ hk, mul_zero]

/-- The complete Gaussian monomial pairing, with all factorial and volume factors explicit. -/
theorem gaussian_monomial_pairing (n m : ℕ) :
    (∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) * z ^ n * (starRingEnd ℂ z) ^ m) =
      if n = m then (Real.pi : ℂ) * (n.factorial : ℂ) else 0 := by
  split_ifs with h
  · subst m
    exact gaussian_monomial_diagonal n
  · exact gaussian_monomial_offDiagonal n m h

/-- Pairing with a conjugate monomial extracts the actual unconjugated polynomial coefficient. -/
theorem gaussian_polynomial_monomial (P : Polynomial ℂ) (m : ℕ) :
    (∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) * P.eval z * (starRingEnd ℂ z) ^ m) =
      (Real.pi : ℂ) * (m.factorial : ℂ) * P.coeff m := by
  have heq : (fun z : ℂ ↦ (Real.exp (-‖z‖ ^ 2) : ℂ) *
      P.eval z * (starRingEnd ℂ z) ^ m) =
      fun z ↦ ∑ n ∈ P.support, P.coeff n *
        ((Real.exp (-‖z‖ ^ 2) : ℂ) * z ^ n * (starRingEnd ℂ z) ^ m) := by
    funext z
    simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hi (n : ℕ) : Integrable (fun z : ℂ ↦ P.coeff n *
      ((Real.exp (-‖z‖ ^ 2) : ℂ) * z ^ n * (starRingEnd ℂ z) ^ m)) := by
    simpa only [neg_mul, one_mul] using
      (integrable_gaussian_monomials n m (a := 1) (by norm_num)).const_mul (P.coeff n)
  rw [heq, integral_finsetSum P.support (fun n _ ↦ hi n)]
  simp_rw [integral_const_mul, gaussian_monomial_pairing]
  by_cases hm : m ∈ P.support
  · rw [Finset.sum_eq_single m]
    · simp
      ring
    · intro n _ hnm
      simp [hnm]
    · exact fun h ↦ (h hm).elim
  · have hc : P.coeff m = 0 := Polynomial.notMem_support_iff.mp hm
    rw [hc, mul_zero]
    apply Finset.sum_eq_zero
    intro n hn
    have hnm : n ≠ m := by intro h; subst n; exact hm hn
    simp [hnm]

end Paper.SkewOrthogonal
