/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.PolarExistence
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Converse polar coordinates without argument-product branch manipulations -/

@[expose] public section
noncomputable section
open Set
open scoped Real

namespace Paper.Lambert

theorem rotated_expMul_sin (w : ℂ) :
    ‖expMul w‖ * Real.sin (Complex.arg (expMul w) - w.im) = Real.exp w.re * w.im := by
  have hs : ‖expMul w‖ * Real.sin (Complex.arg (expMul w)) =
      Real.exp w.re * (w.re * Real.sin w.im + w.im * Real.cos w.im) := by
    rw [Complex.norm_mul_sin_arg, expMul, Complex.mul_im, Complex.exp_re, Complex.exp_im]
    ring
  have hc : ‖expMul w‖ * Real.cos (Complex.arg (expMul w)) =
      Real.exp w.re * (w.re * Real.cos w.im - w.im * Real.sin w.im) := by
    rw [Complex.norm_mul_cos_arg, expMul_re]
  calc
    _ = (‖expMul w‖ * Real.sin (Complex.arg (expMul w))) * Real.cos w.im -
        (‖expMul w‖ * Real.cos (Complex.arg (expMul w))) * Real.sin w.im := by
      rw [Real.sin_sub]
      ring
    _ = _ := by
      rw [hs, hc]
      ring_nf
      rw [Real.cos_sq']
      ring

theorem rotated_expMul_cos (w : ℂ) :
    ‖expMul w‖ * Real.cos (Complex.arg (expMul w) - w.im) = Real.exp w.re * w.re := by
  have hs : ‖expMul w‖ * Real.sin (Complex.arg (expMul w)) =
      Real.exp w.re * (w.re * Real.sin w.im + w.im * Real.cos w.im) := by
    rw [Complex.norm_mul_sin_arg, expMul, Complex.mul_im, Complex.exp_re, Complex.exp_im]
    ring
  have hc : ‖expMul w‖ * Real.cos (Complex.arg (expMul w)) =
      Real.exp w.re * (w.re * Real.cos w.im - w.im * Real.sin w.im) := by
    rw [Complex.norm_mul_cos_arg, expMul_re]
  calc
    _ = (‖expMul w‖ * Real.cos (Complex.arg (expMul w))) * Real.cos w.im +
        (‖expMul w‖ * Real.sin (Complex.arg (expMul w))) * Real.sin w.im := by
      rw [Real.cos_sub]
      ring
    _ = _ := by
      rw [hc, hs]
      ring_nf
      rw [Real.cos_sq']
      ring

theorem upper_polar_coordinates {w : ℂ} (hw : w ∈ principalDomain) (hpos : 0 < (expMul w).im) :
    let θ := Complex.arg (expMul w)
    θ ∈ Ioo (0 : ℝ) Real.pi ∧ w.im ∈ Ioo (0 : ℝ) θ ∧
      w = polarPoint θ w.im ∧ polarRadius θ w.im = ‖expMul w‖ := by
  let θ := Complex.arg (expMul w)
  have hv : 0 < w.im := (expMul_im_pos_iff hw).mp hpos
  have hθ0 : 0 ≤ θ := Complex.arg_nonneg_iff.mpr hpos.le
  have hθπ : θ < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hpos.ne')
  have hr : 0 < ‖expMul w‖ := norm_pos_iff.mpr (by
    intro h
    simp [h] at hpos)
  have hsin : 0 < Real.sin (θ - w.im) := by
    apply (mul_pos_iff_of_pos_left hr).mp
    rw [rotated_expMul_sin]
    exact mul_pos (Real.exp_pos _) hv
  have hvθ : w.im < θ := by
    by_contra hh
    have hnon : Real.sin (θ - w.im) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [(abs_lt.mp hw.1).2])
    exact (not_le_of_gt hsin) hnon
  have hu : w.re = polarReal θ w.im := by
    unfold polarReal
    apply (eq_div_iff hsin.ne').mpr
    apply mul_left_cancel₀ (Real.exp_pos w.re).ne'
    calc
      Real.exp w.re * (w.re * Real.sin (θ - w.im)) =
          (‖expMul w‖ * Real.cos (θ - w.im)) * Real.sin (θ - w.im) := by
        rw [rotated_expMul_cos]
        ring
      _ = (‖expMul w‖ * Real.sin (θ - w.im)) * Real.cos (θ - w.im) := by ring
      _ = Real.exp w.re * (w.im * Real.cos (θ - w.im)) := by
        rw [rotated_expMul_sin]
        ring
  have hpoint : w = polarPoint θ w.im := Complex.ext hu rfl
  have hrad : polarRadius θ w.im = ‖expMul w‖ := by
    unfold polarRadius
    rw [← hu]
    calc
      w.im / Real.sin (θ - w.im) * Real.exp w.re =
          (Real.exp w.re * w.im) / Real.sin (θ - w.im) := by ring
      _ = ‖expMul w‖ := (div_eq_iff hsin.ne').mpr (rotated_expMul_sin w).symm
  exact ⟨⟨hv.trans hvθ, hθπ⟩, ⟨hv, hvθ⟩, hpoint, hrad⟩

end Paper.Lambert
