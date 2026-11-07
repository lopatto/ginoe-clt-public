/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling

/-! # Quantitative Stirling normalization used in the Lambert appendix

The effective bound follows from Mathlib's proved Robbins step estimate and
its proved Stirling limit. No asymptotic formula is taken as an assumption.
-/

@[expose] public section
noncomputable section
open Filter Real
open scoped Topology

namespace Paper.Lambert

def stirlingTau (N : ℕ) : ℝ := Stirling.stirlingSeq N / Real.sqrt Real.pi

theorem stirlingTau_pos {N : ℕ} (hN : 1 ≤ N) : 0 < stirlingTau N := by
  have hs : 0 < Stirling.stirlingSeq N :=
    (Real.sqrt_pos.mpr Real.pi_pos).trans_le
      (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  exact div_pos hs (Real.sqrt_pos.mpr Real.pi_pos)

theorem one_le_stirlingTau {N : ℕ} (hN : 1 ≤ N) : 1 ≤ stirlingTau N := by
  exact (one_le_div (Real.sqrt_pos.mpr Real.pi_pos)).mpr
    (Stirling.sqrt_pi_le_stirlingSeq (by omega))

theorem factorial_eq_stirlingTau {N : ℕ} (hN : 1 ≤ N) :
    (N.factorial : ℝ) = Real.sqrt (2 * Real.pi * N) *
      (N / Real.exp 1) ^ N * stirlingTau N := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs : Real.sqrt (2 * Real.pi * N) =
      Real.sqrt (2 * N : ℝ) * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (2 * N : ℝ))]
    congr 1
    ring
  rw [hs, stirlingTau, Stirling.stirlingSeq]
  field_simp

private def correctedStirlingLog (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq (n + 1)) - 1 / (12 * ((n : ℝ) + 1))

private theorem correctedStirlingLog_monotone : Monotone correctedStirlingLog := by
  apply monotone_nat_of_le_succ
  intro n
  have hs := Stirling.log_stirlingSeq_sdiff_le (n + 1)
  push_cast at hs
  have hd : 1 / (12 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
    field_simp
    ring
  simp only [correctedStirlingLog, Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] at hs ⊢
  linarith

private theorem tendsto_correctedStirlingLog :
    Tendsto correctedStirlingLog atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hl := (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp hs
  have hi : Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 12 : ℝ) using 1
    · ext n
      field_simp
    · simp
  unfold correctedStirlingLog
  simpa only [Function.comp_def, sub_zero] using hl.sub hi

theorem log_stirlingTau_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.log (stirlingTau N) ∧ Real.log (stirlingTau N) ≤ 1 / (12 * N : ℝ) := by
  refine ⟨Real.log_nonneg (one_le_stirlingTau hN), ?_⟩
  have hh := correctedStirlingLog_monotone.ge_of_tendsto
    tendsto_correctedStirlingLog (N - 1)
  have hs : 0 < Stirling.stirlingSeq N :=
    (Real.sqrt_pos.mpr Real.pi_pos).trans_le
      (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have hn : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  simp only [correctedStirlingLog, Nat.sub_add_cancel hN] at hh
  rw [hn] at hh
  rw [stirlingTau, Real.log_div hs.ne' (by positivity)]
  linarith

theorem stirlingTau_relative_error {N : ℕ} (hN : 1 ≤ N) :
    |stirlingTau N - 1| + |(stirlingTau N)⁻¹ - 1| ≤ 1 / (N : ℝ) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨hl0, hl⟩ := log_stirlingTau_bounds hN
  have hlu : Real.log (stirlingTau N) ≤ 1 := by
    have hp : 0 < 12 * (N : ℝ) := by positivity
    have hh : 1 / (12 * N : ℝ) ≤ 1 := (div_le_one hp).mpr (by linarith)
    exact hl.trans hh
  have h1 := Real.abs_exp_sub_one_le (x := Real.log (stirlingTau N))
    (by simpa only [abs_of_nonneg hl0] using hlu)
  rw [Real.exp_log (stirlingTau_pos hN), abs_of_nonneg hl0] at h1
  have h2 := Real.abs_exp_sub_one_le (x := -Real.log (stirlingTau N))
    (by simpa only [abs_neg, abs_of_nonneg hl0] using hlu)
  rw [Real.exp_neg, Real.exp_log (stirlingTau_pos hN), abs_neg,
    abs_of_nonneg hl0] at h2
  have hfrac : 4 * (1 / (12 * N : ℝ)) ≤ 1 / (N : ℝ) := by
    have hp : 0 < (N : ℝ) := by linarith
    field_simp
    nlinarith
  linarith

end Paper.Lambert
