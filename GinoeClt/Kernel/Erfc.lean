/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The complementary Gaussian error function used in the manuscript -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Real

namespace Paper.Kernel

/-- The exact real Gaussian-tail integral convention from the manuscript. -/
def erfc (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in Ioi x, Real.exp (-(t ^ 2))

theorem integrable_gaussian : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
  simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (b := 1) zero_lt_one

theorem erfc_nonneg (x : ℝ) : 0 ≤ erfc x := by
  unfold erfc
  exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem continuous_erfc : Continuous erfc := by
  have htail (x : ℝ) :
      (∫ t in Ioi x, Real.exp (-(t ^ 2))) =
        (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2))) -
          ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
    have hh := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := (0 : ℝ)) (b := x) integrable_gaussian.integrableOn integrable_gaussian.integrableOn
    linarith
  have hc : Continuous (fun x : ℝ =>
      (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2))) -
        ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))) :=
    continuous_const.sub (integrable_gaussian.continuous_primitive 0)
  have he : erfc = fun x : ℝ => (2 / Real.sqrt Real.pi) *
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2))) -
        ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))) := by
    funext x
    rw [erfc, htail]
  rw [he]
  exact continuous_const.mul hc

end Paper.Kernel
