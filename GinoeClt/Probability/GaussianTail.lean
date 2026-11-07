/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import GinoeClt.Probability.Taylor

/-! # Exponential domination of target-law Taylor remainders -/

public section
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal

namespace Paper.Probability

theorem moment_taylor_bound_of_exp_integrable {μ : Measure ℝ}
    (n : ℕ) (s t : ℝ) (hs : 0 < s)
    (hm : Integrable (fun x : ℝ ↦ ‖x‖ ^ (n + 1)) μ)
    (he : Integrable (fun x : ℝ ↦ Real.exp (s * ‖x‖)) μ) :
    (∫ x : ℝ, ‖x‖ ^ (n + 1) ∂μ) * |t| ^ (n + 1) / (n.factorial : ℝ) ≤
      (∫ x : ℝ, Real.exp (s * ‖x‖) ∂μ) *
        ((n + 1 : ℕ) : ℝ) * (|t| / s) ^ (n + 1) := by
  have hi : (∫ x : ℝ, (s * ‖x‖) ^ (n + 1) /
      ((n + 1).factorial : ℝ) ∂μ) ≤
      ∫ x : ℝ, Real.exp (s * ‖x‖) ∂μ := by
    apply integral_mono
      (by simpa only [mul_pow] using
        (hm.const_mul (s ^ (n + 1))).div_const ((n + 1).factorial : ℝ)) he
    intro x
    exact Real.pow_div_factorial_le_exp _ (mul_nonneg hs.le (norm_nonneg _)) _
  simp_rw [mul_pow] at hi
  rw [integral_div, integral_const_mul] at hi
  calc
    _ = (s ^ (n + 1) * (∫ x : ℝ, ‖x‖ ^ (n + 1) ∂μ) /
        ((n + 1).factorial : ℝ)) * ((n + 1 : ℕ) : ℝ) *
        (|t| / s) ^ (n + 1) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)) (by positivity)

theorem gaussian_exp_norm_integrable (v : ℝ≥0) (s : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (s * ‖x‖)) (gaussianReal 0 v) := by
  simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) s)
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-s))

/-- The target Gaussian has a vanishing Taylor-moment remainder for every t. -/
theorem gaussian_taylor_moment_tendsto_zero (v : ℝ≥0) (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        (∫ x : ℝ, ‖x‖ ^ (n + 1) ∂gaussianReal 0 v) *
          |t| ^ (n + 1) / (n.factorial : ℝ))
      atTop (𝓝 0) := by
  let s : ℝ := |t| + 1
  let C : ℝ := ∫ x : ℝ, Real.exp (s * ‖x‖) ∂gaussianReal 0 v
  have hs : 0 < s := by dsimp [s]; positivity
  have hr0 : 0 ≤ |t| / s := div_nonneg (abs_nonneg _) hs.le
  have hr1 : |t| / s < 1 := (div_lt_one hs).mpr (by dsimp [s]; linarith)
  have hgeom := (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp
    (tendsto_add_atTop_nat 1)
  have hlim : Tendsto
      (fun n : ℕ ↦ C * ((n + 1 : ℕ) : ℝ) * (|t| / s) ^ (n + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, mul_assoc] using
      tendsto_const_nhds.mul hgeom
  apply squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hlim
  apply moment_taylor_bound_of_exp_integrable n s t hs
  · exact (memLp_id_gaussianReal' (p := (n + 1 : ℕ)) (by simp)).integrable_norm_pow'
  · exact gaussian_exp_norm_integrable v s

end Paper.Probability
