/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.Asymptotic

/-! # The source's corrected N-1 truncation, by one-term subtraction -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology

namespace Paper.Lambert

def correctedTruncationError (N : ℕ) (q : ℂ) : ℂ :=
  q * truncationError N q +
    (1 - q) * ((((stirlingTau N)⁻¹ : ℝ) : ℂ) - 1)

theorem truncation_difference {N : ℕ} (hN : 1 ≤ N) (q : ℂ) :
    Kernel.truncatedExponential (N - 1) ((N : ℂ) * q) =
      Kernel.truncatedExponential N ((N : ℂ) * q) -
        Complex.exp (-((N : ℂ) * q)) * ((N : ℂ) * q) ^ (N - 1) /
          ((N - 1).factorial : ℂ) := by
  have hh := truncatedExponential_succ (N - 1) ((N : ℂ) * q)
  rw [Nat.sub_add_cancel hN] at hh
  linear_combination -hh

theorem subtracted_term_stirling_succ (n : ℕ) (q : ℂ) :
    Complex.exp (-((n + 1 : ℂ) * q)) * ((n + 1 : ℂ) * q) ^ n /
        (n.factorial : ℂ) =
      Complex.exp ((n + 1 : ℂ) * (1 - q)) * q ^ n /
        (Real.sqrt (2 * Real.pi * (n + 1)) : ℂ) *
          (((stirlingTau (n + 1))⁻¹ : ℝ) : ℂ) := by
  have hs : (Real.sqrt (2 * Real.pi * (n + 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (2 * Real.pi * (n + 1)) ≠ 0 by positivity)
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hc := pathCoefficient_mul_sqrt n
  have hb :
      ((n + 1 : ℂ) ^ n * Complex.exp (-(n + 1 : ℂ)) / (n.factorial : ℂ)) *
          (Real.sqrt (2 * Real.pi * (n + 1)) : ℂ) =
        (((stirlingTau (n + 1))⁻¹ : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hn
    unfold pathCoefficient at hc
    rw [pow_succ] at hc
    linear_combination hc
  have he : Complex.exp (-((n + 1 : ℂ) * q)) =
      Complex.exp ((n + 1 : ℂ) * (1 - q)) * Complex.exp (-(n + 1 : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he, mul_pow, div_mul_eq_mul_div]
  apply (eq_div_iff hs).mpr
  linear_combination
    Complex.exp ((n + 1 : ℂ) * (1 - q)) * q ^ n * hb

theorem subtracted_term_stirling {N : ℕ} (hN : 1 ≤ N) (q : ℂ) :
    Complex.exp (-((N : ℂ) * q)) * ((N : ℂ) * q) ^ (N - 1) /
        ((N - 1).factorial : ℂ) =
      Complex.exp ((N : ℂ) * (1 - q)) * q ^ (N - 1) /
        (Real.sqrt (2 * Real.pi * N) : ℂ) *
          (((stirlingTau N)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
    subtracted_term_stirling_succ n q

theorem corrected_truncation_expansion {N : ℕ} (hN : 2 ≤ N)
    {q : ℂ} (hq : ‖q‖ < 1) :
    Kernel.truncatedExponential (N - 1) ((N : ℂ) * q) =
      1 - Complex.exp ((N : ℂ) * (1 - q)) * q ^ (N - 1) /
        ((Real.sqrt (2 * Real.pi * N) : ℂ) * (1 - q)) *
          (1 + correctedTruncationError N q) := by
  have hN1 : 1 ≤ N := by omega
  have hs : (Real.sqrt (2 * Real.pi * N) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (2 * Real.pi * N) ≠ 0 by positivity)
  have hq0 : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm (show q ≠ 1 by
    intro h
    subst q
    norm_num only [norm_one] at hq))
  have hp : q ^ N = q ^ (N - 1) * q := by
    rw [← pow_succ, Nat.sub_add_cancel hN1]
  rw [truncation_difference hN1, truncatedExponential_expansion hN1 hq,
    subtracted_term_stirling hN1, hp]
  unfold correctedTruncationError
  field_simp
  ring

theorem norm_correctedTruncationError_le {r C : ℝ} (hr0 : 0 ≤ r)
    {q : ℂ} (hq : ‖q‖ ≤ r) {N : ℕ} (hN : 1 ≤ N)
    (hR : ‖truncationError N q‖ ≤ C / (N : ℝ)) :
    ‖correctedTruncationError N q‖ ≤ (r * C + (1 + r)) / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hT := stirlingTau_relative_error hN
  have hTerr : |(stirlingTau N)⁻¹ - 1| ≤ 1 / (N : ℝ) :=
    (le_add_of_nonneg_left (abs_nonneg (stirlingTau N - 1))).trans hT
  have hTc : ‖(((stirlingTau N)⁻¹ : ℝ) : ℂ) - 1‖ ≤ 1 / (N : ℝ) := by
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hTerr
  have hqnorm : ‖1 - q‖ ≤ 1 + r := by
    have hh := norm_sub_le (1 : ℂ) q
    norm_num only [norm_one] at hh
    linarith
  unfold correctedTruncationError
  calc
    _ ≤ ‖q‖ * ‖truncationError N q‖ +
        ‖1 - q‖ * ‖(((stirlingTau N)⁻¹ : ℝ) : ℂ) - 1‖ := by
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    _ ≤ r * (C / (N : ℝ)) + (1 + r) * (1 / (N : ℝ)) :=
      add_le_add (mul_le_mul hq hR (norm_nonneg _) hr0)
        (mul_le_mul hqnorm hTc (norm_nonneg _) (by linarith))
    _ = _ := by ring

/-- Corollary A.2, retaining the source's exact one-term subtraction and remainder. -/
theorem corrected_truncation {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ q : ℂ, ‖q‖ ≤ r →
      Kernel.truncatedExponential (N - 1) ((N : ℂ) * q) =
        1 - Complex.exp ((N : ℂ) * (1 - q)) * q ^ (N - 1) /
          ((Real.sqrt (2 * Real.pi * N) : ℂ) * (1 - q)) *
            (1 + correctedTruncationError N q) ∧
      ‖correctedTruncationError N q‖ ≤ C / (N : ℝ) := by
  obtain ⟨C, hC, hR⟩ := truncatedExponential_asymptotic hr0 hr
  refine ⟨r * C + (1 + r), by positivity, fun N hN q hq => ?_⟩
  have hN1 : 1 ≤ N := by omega
  exact ⟨corrected_truncation_expansion hN (hq.trans_lt hr),
    norm_correctedTruncationError_le hr0.le hq hN1 ((hR N hN1 q hq).2)⟩

end Paper.Lambert
