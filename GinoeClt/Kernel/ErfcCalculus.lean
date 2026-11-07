/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Erfc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # Elementary calculus of the exact complementary Gaussian tail -/

@[expose] public section
noncomputable section
open MeasureTheory Set

namespace Paper.Kernel

theorem erfc_zero : erfc 0 = 1 := by
  have hg : (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
    simpa only [neg_mul, one_mul, div_one] using integral_gaussian_Ioi (1 : ℝ)
  rw [erfc, hg]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']

theorem hasDerivAt_erfc (x : ℝ) :
    HasDerivAt erfc (-(2 / Real.sqrt Real.pi) * Real.exp (-(x ^ 2))) x := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2))
  have hc : Continuous g := by fun_prop
  have hprim : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : erfc = fun u : ℝ => (2 / Real.sqrt Real.pi) *
      ((∫ t in Ioi (0 : ℝ), g t) - ∫ t in (0 : ℝ)..u, g t) := by
    funext u
    have ht := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := (0 : ℝ)) (b := u) integrable_gaussian.integrableOn
      integrable_gaussian.integrableOn
    change (2 / Real.sqrt Real.pi) * (∫ t in Ioi u, g t) = _
    congr 1
    change (∫ t in Ioi (0 : ℝ), g t) - (∫ t in Ioi u, g t) = _ at ht
    linarith
  rw [he]
  simpa only [g, Pi.sub_apply, zero_sub, mul_neg, neg_mul] using
    ((hasDerivAt_const x (∫ t in Ioi (0 : ℝ), g t)).sub hprim).const_mul
      (2 / Real.sqrt Real.pi)

end Paper.Kernel
