/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Leading

/-! # The source entropy and the exponentially small truncation tails -/

@[expose] public section
noncomputable section
open Set
open scoped Real ComplexConjugate

namespace Paper.Kernel

def entropy (t : ℝ) : ℝ := t - 1 - Real.log t

theorem entropy_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 0 < entropy t := by
  have hh := Real.log_lt_sub_one_of_pos ht (ne_of_lt ht1)
  unfold entropy
  linarith

theorem entropy_antitone_below_one {t r : ℝ} (ht : 0 < t)
    (htr : t ≤ r) (hr1 : r ≤ 1) : entropy r ≤ entropy t := by
  have hr : 0 < r := ht.trans_le htr
  have hh := Real.log_le_sub_one_of_pos (div_pos ht hr)
  rw [Real.log_div ht.ne' hr.ne'] at hh
  have hp : 0 ≤ (1 - r) * (1 - t / r) :=
    mul_nonneg (by linarith) (by
      have hdiv : t / r ≤ 1 := (div_le_one hr).mpr htr
      linarith)
  have he : t - r - (t / r - 1) = (1 - r) * (1 - t / r) := by
    field_simp
    ring
  unfold entropy
  linarith

theorem norm_exp_mul_pow (N : ℕ) (a q : ℂ) (hq : 0 < ‖q‖) :
    ‖Complex.exp a * q ^ N‖ =
      Real.exp (a.re + (N : ℝ) * Real.log ‖q‖) := by
  rw [norm_mul, Complex.norm_exp, norm_pow]
  have hp : ‖q‖ ^ N = Real.exp ((N : ℝ) * Real.log ‖q‖) := by
    rw [Real.exp_nat_mul, Real.exp_log hq]
  rw [hp, ← Real.exp_add]

theorem norm_S_tail_numerator (N : ℕ) {z w : ℂ} (hz : 0 < ‖z‖) (hw : 0 < ‖w‖) :
    ‖Complex.exp (leadingSExponent N z w) *
        Complex.exp ((N : ℂ) * (1 - z * conj w)) * (z * conj w) ^ N‖ =
      Real.exp (-(N : ℝ) / 2 * (entropy (‖z‖ ^ 2) + entropy (‖w‖ ^ 2))) := by
  have hq : 0 < ‖z * conj w‖ := by rw [norm_mul, Complex.norm_conj]; positivity
  rw [← Complex.exp_add, norm_exp_mul_pow N _ _ hq, leadingSExponent_tail_re,
    norm_mul, Complex.norm_conj, Real.log_mul hz.ne' hw.ne']
  congr 1
  simp only [entropy, Real.log_pow]
  ring

theorem norm_D_tail_numerator (N : ℕ) {z w : ℂ} (hz : 0 < ‖z‖) (hw : 0 < ‖w‖) :
    ‖Complex.exp (leadingDExponent N z w) *
        Complex.exp ((N : ℂ) * (1 - z * w)) * (z * w) ^ N‖ =
      Real.exp (-(N : ℝ) / 2 * (entropy (‖z‖ ^ 2) + entropy (‖w‖ ^ 2))) := by
  have hq : 0 < ‖z * w‖ := by rw [norm_mul]; positivity
  rw [← Complex.exp_add, norm_exp_mul_pow N _ _ hq, leadingDExponent_tail_re,
    norm_mul, Real.log_mul hz.ne' hw.ne']
  congr 1
  simp only [entropy, Real.log_pow]
  ring

theorem entropy_bulk_decay {d : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2)
    {z w : ℂ} (hz0 : d ≤ ‖z‖) (hw0 : d ≤ ‖w‖)
    (hz1 : ‖z‖ ≤ 1 - d) (hw1 : ‖w‖ ≤ 1 - d) (N : ℕ) :
    Real.exp (-(N : ℝ) / 2 * (entropy (‖z‖ ^ 2) + entropy (‖w‖ ^ 2))) ≤
      Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) := by
  have hr0 : 0 < (1 - d) ^ 2 := by nlinarith
  have hr1 : (1 - d) ^ 2 < 1 := by nlinarith
  have hzsq : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (hd.trans_le hz0)
  have hwsq : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (hd.trans_le hw0)
  have hzle : ‖z‖ ^ 2 ≤ (1 - d) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hz1
  have hwle : ‖w‖ ^ 2 ≤ (1 - d) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hw1
  have hhz := entropy_antitone_below_one hzsq hzle hr1.le
  have hhw := entropy_antitone_below_one hwsq hwle hr1.le
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

def truncationTail (N : ℕ) (q : ℂ) : ℂ :=
  Complex.exp ((N : ℂ) * (1 - q)) * q ^ (N - 1) /
    ((Real.sqrt (2 * Real.pi * N) : ℂ) * (1 - q)) *
      (1 + Lambert.correctedTruncationError N q)

theorem truncatedExponential_eq_one_sub_tail {N : ℕ} (hN : 2 ≤ N)
    {q : ℂ} (hq : ‖q‖ < 1) :
    truncatedExponential (N - 1) ((N : ℂ) * q) = 1 - truncationTail N q :=
  Lambert.corrected_truncation_expansion hN hq

theorem exp_mul_truncationTail {N : ℕ} (hN : 1 ≤ N) (a : ℂ)
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    Complex.exp a * truncationTail N q =
      (Complex.exp a * Complex.exp ((N : ℂ) * (1 - q)) * q ^ N) /
        (q * (Real.sqrt (2 * Real.pi * N) : ℂ) * (1 - q)) *
          (1 + Lambert.correctedTruncationError N q) := by
  have hs : (Real.sqrt (2 * Real.pi * N) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (2 * Real.pi * N) ≠ 0 by positivity)
  have hq : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm (show q ≠ 1 by
    intro h
    subst q
    norm_num only [norm_one] at hq1))
  have hp : q ^ N = q ^ (N - 1) * q := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  unfold truncationTail
  rw [hp]
  field_simp

theorem norm_exp_mul_truncationTail_le {d C : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2)
    (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) {a q : ℂ}
    (hq0 : d ^ 2 ≤ ‖q‖) (hq1 : ‖q‖ ≤ (1 - d) ^ 2)
    (hR : ‖Lambert.correctedTruncationError N q‖ ≤ C / (N : ℝ))
    (hnum : ‖Complex.exp a * Complex.exp ((N : ℂ) * (1 - q)) * q ^ N‖ ≤
      Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ))) :
    ‖Complex.exp a * truncationTail N q‖ ≤
      ((1 + C) / (d ^ 2 * Real.sqrt (2 * Real.pi) * (1 - (1 - d) ^ 2))) *
        Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hr : (1 - d) ^ 2 < 1 := by nlinarith
  have hqpos : 0 < ‖q‖ := (sq_pos_of_pos hd).trans_le hq0
  have hqne : q ≠ 0 := norm_pos_iff.mp hqpos
  have hs : 0 < Real.sqrt (2 * Real.pi * N) := by positivity
  have hs0 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsq : Real.sqrt (2 * Real.pi) ≤ Real.sqrt (2 * Real.pi * N) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hqden : 1 - (1 - d) ^ 2 ≤ ‖1 - q‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) q
    norm_num only [norm_one] at hh
    linarith
  have hd0 : 0 < d ^ 2 * Real.sqrt (2 * Real.pi) * (1 - (1 - d) ^ 2) := by positivity
  have hden : d ^ 2 * Real.sqrt (2 * Real.pi) * (1 - (1 - d) ^ 2) ≤
      ‖q‖ * Real.sqrt (2 * Real.pi * N) * ‖1 - q‖ :=
    mul_le_mul (mul_le_mul hq0 hsq hs0.le (norm_nonneg _)) hqden
      (by linarith) (mul_nonneg (norm_nonneg _) hs.le)
  have hR1 : ‖1 + Lambert.correctedTruncationError N q‖ ≤ 1 + C := by
    have hRC : C / (N : ℝ) ≤ C := div_le_self hC hn
    have hh := norm_add_le (1 : ℂ) (Lambert.correctedTruncationError N q)
    norm_num only [norm_one] at hh
    linarith
  have hdn : ‖q * (Real.sqrt (2 * Real.pi * N) : ℂ) * (1 - q)‖ =
      ‖q‖ * Real.sqrt (2 * Real.pi * N) * ‖1 - q‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [exp_mul_truncationTail hN a hqne (hq1.trans_lt hr), norm_mul, norm_div, hdn]
  calc
    _ ≤ (Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) /
        (d ^ 2 * Real.sqrt (2 * Real.pi) * (1 - (1 - d) ^ 2))) * (1 + C) := by
      apply mul_le_mul
      · exact (div_le_div_of_nonneg_left (norm_nonneg _) hd0 hden).trans
          (div_le_div_of_nonneg_right hnum hd0.le)
      · exact hR1
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

end Paper.Kernel
