/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Global Taylor remainder bounds for characteristic functions -/

public section
open MeasureTheory Filter Set
open scoped Topology

namespace Paper.Probability

/-- Scaling to the fixed interval handles both signs of the argument. -/
theorem taylor_comp_mul (f : ℝ → ℂ) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) (x : ℝ) :
    taylorWithinEval (fun u : ℝ ↦ f (x * u)) n (Icc 0 1) 0 1 =
      taylorWithinEval f n univ 0 x := by
  have hg : ContDiff ℝ (n + 1) (fun u : ℝ ↦ f (x * u)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  rw [taylor_within_apply, taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n + 1 := (Finset.mem_range.mp hk).le
  have hfk : ContDiff ℝ k f := hf.of_le (by exact_mod_cast hkn)
  have hgk : ContDiff ℝ k (fun u : ℝ ↦ f (x * u)) :=
    hg.of_le (by exact_mod_cast hkn)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    hgk.contDiffAt (by simp)]
  rw [iteratedDeriv_comp_const_smul hfk]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- The factor n! is the native Banach-valued mean-remainder estimate. -/
theorem norm_taylor_remainder_le (f : ℝ → ℂ) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) (C x : ℝ)
    (hC : ∀ y, ‖iteratedDeriv (n + 1) f y‖ ≤ C) :
    ‖f x - taylorWithinEval f n univ 0 x‖ ≤
      C * |x| ^ (n + 1) / (n.factorial : ℝ) := by
  have hg : ContDiff ℝ (n + 1) (fun u : ℝ ↦ f (x * u)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hbound : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) (fun u : ℝ ↦ f (x * u)) (Icc 0 1) y‖ ≤
        |x| ^ (n + 1) * C := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      hg.contDiffAt hy, iteratedDeriv_comp_const_smul hf]
    simp only [norm_smul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_left (hC (x * y)) (by positivity)
  have h := taylor_mean_remainder_bound (f := fun u : ℝ ↦ f (x * u))
    (n := n) (show (0 : ℝ) ≤ 1 by norm_num) hg.contDiffOn
    (show (1 : ℝ) ∈ Icc 0 1 by simp) hbound
  simpa only [mul_one, sub_zero, one_pow, mul_one, taylor_comp_mul f n hf x,
    mul_comm (|x| ^ (n + 1)) C] using h

/-- Uniform derivative bounds use only the indicated absolute moment. -/
theorem norm_iteratedDeriv_charFun_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (k : ℕ) (hk : MemLp id k μ) (t : ℝ) :
    ‖iteratedDeriv k (charFun μ) t‖ ≤ ∫ x : ℝ, ‖x‖ ^ k ∂μ := by
  rw [iteratedDeriv_charFun hk, norm_mul]
  simp only [Complex.norm_pow, Complex.norm_I, one_pow, one_mul]
  calc
    ‖∫ x : ℝ, (x : ℂ) ^ k * Complex.exp (t * x * Complex.I) ∂μ‖ ≤
        ∫ x : ℝ, ‖(x : ℂ) ^ k * Complex.exp (t * x * Complex.I)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖x‖ ^ k ∂μ := by
      congr 1
      funext x
      simp [Complex.norm_exp]

/-- An all-real-argument remainder bound requiring no exponential moment. -/
theorem charFun_taylor_remainder_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hint : ∀ k : ℕ, MemLp id k μ) (n : ℕ) (t : ℝ) :
    ‖charFun μ t -
        ∑ k ∈ Finset.range (n + 1),
          (k.factorial : ℂ)⁻¹ * ((t : ℂ) * Complex.I) ^ k *
            (∫ x : ℝ, x ^ k ∂μ : ℝ)‖ ≤
      (∫ x : ℝ, ‖x‖ ^ (n + 1) ∂μ) * |t| ^ (n + 1) / (n.factorial : ℝ) := by
  rw [← taylorWithinEval_charFun_zero (hint n)]
  exact norm_taylor_remainder_le _ n (contDiff_charFun (hint (n + 1))) _ t
    (norm_iteratedDeriv_charFun_le (n + 1) (hint (n + 1)))

end Paper.Probability
