/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.TruncatedPrimitive
public import GinoeClt.Lambert.QuantitativeStirling

/-! # Uniform truncated-exponential asymptotics via the genuine Lambert path -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology

namespace Paper.Lambert

theorem pathCoefficient_stirling (n : ℕ) :
    pathCoefficient n =
      (((stirlingTau (n + 1))⁻¹ *
        Real.sqrt ((n + 1 : ℝ) / (2 * Real.pi)) : ℝ) : ℂ) := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have ht : 0 < stirlingTau (n + 1) := stirlingTau_pos (by omega)
  have hs : 0 < Real.sqrt (2 * Real.pi * (n + 1 : ℝ)) := by positivity
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have he : Real.exp (n + 1 : ℝ) = Real.exp 1 ^ (n + 1) := by
    simpa only [mul_one, Nat.cast_add, Nat.cast_one] using Real.exp_nat_mul 1 (n + 1)
  have hp : (n + 1 : ℝ) ^ (n + 1) * Real.exp (-(n + 1 : ℝ)) =
      ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1) := by
    rw [Real.exp_neg, he, div_pow, div_eq_mul_inv]
  have hfac := factorial_eq_stirlingTau (N := n + 1) (by omega)
  rw [Nat.factorial_succ] at hfac
  push_cast at hfac
  have hc :
      (n + 1 : ℝ) ^ (n + 1) * Real.exp (-(n + 1 : ℝ)) / (n.factorial : ℝ) =
      (n + 1 : ℝ) /
        (Real.sqrt (2 * Real.pi * (n + 1 : ℝ)) * stirlingTau (n + 1)) := by
    apply (div_eq_div_iff hf.ne' (mul_pos hs ht).ne').mpr
    rw [hp]
    linear_combination -hfac
  have hsq : Real.sqrt ((n + 1 : ℝ) / (2 * Real.pi)) *
      Real.sqrt (2 * Real.pi * (n + 1 : ℝ)) = (n + 1 : ℝ) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (n + 1 : ℝ) / (2 * Real.pi))]
    have ha : (n + 1 : ℝ) / (2 * Real.pi) * (2 * Real.pi * (n + 1 : ℝ)) =
        (n + 1 : ℝ) ^ 2 := by
      field_simp
    rw [ha, Real.sqrt_sq hn.le]
  have hr :
      (n + 1 : ℝ) ^ (n + 1) * Real.exp (-(n + 1 : ℝ)) / (n.factorial : ℝ) =
      (stirlingTau (n + 1))⁻¹ * Real.sqrt ((n + 1 : ℝ) / (2 * Real.pi)) := by
    rw [hc]
    apply (div_eq_iff (mul_pos hs ht).ne').mpr
    symm
    calc
      _ = Real.sqrt ((n + 1 : ℝ) / (2 * Real.pi)) *
          Real.sqrt (2 * Real.pi * (n + 1 : ℝ)) *
          ((stirlingTau (n + 1))⁻¹ * stirlingTau (n + 1)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ ht.ne', mul_one, hsq]
  unfold pathCoefficient
  have hh := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_exp,
    Complex.ofReal_neg] using hh

def weightedIntegral (N : ℕ) (q : ℂ) : ℂ :=
  ∫ t : ℝ in 0..1, (1 - (t : ℂ)) ^ (N - 1) * pathFactor q t

def integralRelativeError (N : ℕ) (q : ℂ) : ℂ :=
  (N : ℂ) * (1 - q) * weightedIntegral N q - 1

def truncationError (N : ℕ) (q : ℂ) : ℂ :=
  (((stirlingTau N)⁻¹ : ℝ) : ℂ) * (1 + integralRelativeError N q) - 1

theorem sqrt_prefactor_product {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt ((N : ℝ) / (2 * Real.pi)) * Real.sqrt (2 * Real.pi * N) = (N : ℝ) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (N : ℝ) / (2 * Real.pi))]
  have hh : (N : ℝ) / (2 * Real.pi) * (2 * Real.pi * N) = (N : ℝ) ^ 2 := by
    field_simp
  rw [hh, Real.sqrt_sq (by positivity : 0 ≤ (N : ℝ))]

theorem pathCoefficient_mul_sqrt (n : ℕ) :
    pathCoefficient n * (Real.sqrt (2 * Real.pi * (n + 1)) : ℂ) =
      (n + 1 : ℂ) * (((stirlingTau (n + 1))⁻¹ : ℝ) : ℂ) := by
  rw [pathCoefficient_stirling]
  have hh := sqrt_prefactor_product (N := n + 1) (by omega)
  push_cast at hh
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hh
  push_cast at hc
  calc
    _ = (((stirlingTau (n + 1))⁻¹ : ℝ) : ℂ) *
        ((Real.sqrt ((n + 1 : ℝ) / (2 * Real.pi)) : ℂ) *
          (Real.sqrt (2 * Real.pi * (n + 1)) : ℂ)) := by push_cast; ring
    _ = _ := by rw [hc]; ring

theorem phi_pow (N : ℕ) (q : ℂ) :
    (phi q) ^ N = Complex.exp ((N : ℂ) * (1 - q)) * q ^ N := by
  rw [phi, mul_pow, ← Complex.exp_nat_mul]
  ring

theorem truncatedExponential_expansion {N : ℕ} (hN : 1 ≤ N)
    {q : ℂ} (hq : ‖q‖ < 1) :
    Kernel.truncatedExponential N ((N : ℂ) * q) =
      1 - Complex.exp ((N : ℂ) * (1 - q)) * q ^ N /
        ((Real.sqrt (2 * Real.pi * N) : ℂ) * (1 - q)) *
          (1 + truncationError N q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  have hh := truncatedExponential_lambert_integral n hq
  have hs : (Real.sqrt (2 * Real.pi * (n + 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (2 * Real.pi * (n + 1)) ≠ 0 by positivity)
  have hq0 : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm (show q ≠ 1 by
    intro h
    subst q
    norm_num only [norm_one] at hq))
  have hc := pathCoefficient_mul_sqrt n
  simp only [Complex.ofReal_inv] at hc
  simp only [Nat.succ_eq_add_one] at *
  rw [phi_pow] at hh
  unfold truncationError integralRelativeError weightedIntegral
  push_cast at hh ⊢
  rw [hh]
  field_simp
  linear_combination
    -Complex.exp ((n + 1 : ℂ) * (1 - q)) * q ^ (n + 1) *
      (∫ t : ℝ in 0..1, (1 - (t : ℂ)) ^ n * pathFactor q t) * (1 - q) * hc

theorem norm_integralRelativeError_le {r M : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hM0 : 0 ≤ M)
    (hM : ∀ q : ℂ, ‖q‖ ≤ r → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pathFactorDerivative q t‖ ≤ M)
    {q : ℂ} (hq : ‖q‖ ≤ r) {N : ℕ} (hN : 1 ≤ N) :
    ‖integralRelativeError N q‖ ≤ M * (1 + r) / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hq1 : ‖q‖ < 1 := hq.trans_lt hr
  have hq0 : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm (show q ≠ 1 by
    intro h
    subst q
    norm_num only [norm_one] at hq1))
  have hh := weighted_pathFactor_remainder_N hr hM hq hN
  have he : integralRelativeError N q =
      ((N : ℂ) * (1 - q)) *
        (weightedIntegral N q - 1 / ((N : ℂ) * (1 - q))) := by
    unfold integralRelativeError
    field_simp
  have hnorm : ‖1 - q‖ ≤ 1 + r := by
    have hh := norm_sub_le (1 : ℂ) q
    norm_num only [norm_one] at hh
    linarith
  rw [he, norm_mul, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ) * (1 + r) * (M / ((N : ℝ) * (N + 1 : ℝ))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hnorm hn.le) hh
        (norm_nonneg _) (mul_nonneg hn.le (by linarith))
    _ = M * (1 + r) / (N + 1 : ℝ) := by field_simp
    _ ≤ M * (1 + r) / (N : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg hM0 (by linarith)) hn (by linarith)

theorem norm_truncationError_le {r M : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hM0 : 0 ≤ M)
    (hM : ∀ q : ℂ, ‖q‖ ≤ r → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pathFactorDerivative q t‖ ≤ M)
    {q : ℂ} (hq : ‖q‖ ≤ r) {N : ℕ} (hN : 1 ≤ N) :
    ‖truncationError N q‖ ≤ (M * (1 + r) + 1) / (N : ℝ) := by
  have hT := stirlingTau_relative_error hN
  have hTerr : |(stirlingTau N)⁻¹ - 1| ≤ 1 / (N : ℝ) :=
    (le_add_of_nonneg_left (abs_nonneg (stirlingTau N - 1))).trans hT
  have hTc : ‖(((stirlingTau N)⁻¹ : ℝ) : ℂ) - 1‖ ≤ 1 / (N : ℝ) := by
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hTerr
  have hTnorm : ‖(((stirlingTau N)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (stirlingTau_pos hN).le)]
    exact inv_le_one_of_one_le₀ (one_le_stirlingTau hN)
  have hE := norm_integralRelativeError_le hr0 hr hM0 hM hq hN
  calc
    _ = ‖(((stirlingTau N)⁻¹ : ℝ) : ℂ) * integralRelativeError N q +
        ((((stirlingTau N)⁻¹ : ℝ) : ℂ) - 1)‖ := by
      congr 1
      unfold truncationError
      ring
    _ ≤ ‖(((stirlingTau N)⁻¹ : ℝ) : ℂ)‖ * ‖integralRelativeError N q‖ +
        ‖(((stirlingTau N)⁻¹ : ℝ) : ℂ) - 1‖ := by
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ 1 * (M * (1 + r) / (N : ℝ)) + 1 / (N : ℝ) :=
      add_le_add (mul_le_mul hTnorm hE (norm_nonneg _) zero_le_one) hTc
    _ = _ := by ring

/-- Lemma A.1, with a completely defined uniform remainder and the original
Lambert inverse path proof. -/
theorem truncatedExponential_asymptotic {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ q : ℂ, ‖q‖ ≤ r →
      Kernel.truncatedExponential N ((N : ℂ) * q) =
        1 - Complex.exp ((N : ℂ) * (1 - q)) * q ^ N /
          ((Real.sqrt (2 * Real.pi * N) : ℂ) * (1 - q)) *
            (1 + truncationError N q) ∧
      ‖truncationError N q‖ ≤ C / (N : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_pathFactorDerivative_bound hr
  refine ⟨M * (1 + r) + 1, by positivity, fun N hN q hq => ?_⟩
  exact ⟨truncatedExponential_expansion hN (hq.trans_lt hr),
    norm_truncationError_le hr0.le hr hM0 hM hq hN⟩

end Paper.Lambert
