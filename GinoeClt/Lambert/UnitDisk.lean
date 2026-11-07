/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.PrincipalW

/-! # The unit disk belongs to the genuine principal range -/

@[expose] public section
noncomputable section
open Set
open scoped Real

namespace Paper.Lambert

theorem mem_principalDomain_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    w ∈ principalDomain := by
  have hv : |w.im| < Real.pi := (Complex.abs_im_le_norm w).trans_lt
    (hw.trans (by linarith [Real.two_le_pi] : (1 : ℝ) < Real.pi))
  have hsq : ‖w‖ ^ 2 < (1 : ℝ) := by
    simpa only [one_pow] using (sq_lt_sq₀ (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1)).mpr hw
  have hparts : w.re ^ 2 + w.im ^ 2 < 1 := by
    nlinarith [Complex.sq_norm_sub_sq_re w]
  have hc : 1 - w.im ^ 2 / 2 ≤ Real.cos w.im := Real.one_sub_sq_div_two_le_cos
  have hs : 0 < Real.sinc w.im := Real.sinc_pos hv
  refine ⟨hv, ?_⟩
  unfold principalFactor
  rcases le_total 0 w.re with hu | hu
  · nlinarith [mul_nonneg hu hs.le, sq_nonneg w.re]
  · have hlow : w.re ≤ w.re * Real.sinc w.im := by
      simpa only [mul_one] using mul_le_mul_of_nonpos_left (Real.sinc_le_one w.im) hu
    nlinarith [sq_nonneg (w.re + 1)]

theorem W_expMul_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : W (expMul w) = w :=
  W_expMul (mem_principalDomain_of_norm_lt_one hw)

theorem expMul_mem_slitPlane_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : expMul w ∈ slitPlane :=
  expMul_mapsTo_slitPlane (mem_principalDomain_of_norm_lt_one hw)

end Paper.Lambert
