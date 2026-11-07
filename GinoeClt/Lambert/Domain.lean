/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # The open complex range domain for the principal Lambert branch

This file proves elementary geometry and noncriticality of w ↦ w exp(w).
No global inverse, branch, or continuation theorem is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped Real ComplexConjugate

namespace Paper.Lambert

def expMul (w : ℂ) : ℂ := w * Complex.exp w

def principalFactor (w : ℂ) : ℝ := w.re * Real.sinc w.im + Real.cos w.im

def principalDomain : Set ℂ :=
  {w | |w.im| < Real.pi ∧ 0 < principalFactor w}

def slitPlane : Set ℂ :=
  {z | ¬ (z.im = 0 ∧ z.re ≤ -Real.exp (-1))}

theorem continuous_principalFactor : Continuous principalFactor := by
  unfold principalFactor
  fun_prop

theorem isOpen_principalDomain : IsOpen principalDomain :=
  (isOpen_lt Complex.continuous_im.abs continuous_const).inter
    (isOpen_lt continuous_const continuous_principalFactor)

theorem zero_mem_principalDomain : (0 : ℂ) ∈ principalDomain := by
  simp [principalDomain, principalFactor, Real.pi_pos]

theorem neg_one_notMem_principalDomain : (-1 : ℂ) ∉ principalDomain := by
  simp [principalDomain, principalFactor]

theorem principalDomain_conj {w : ℂ} (hw : w ∈ principalDomain) :
    conj w ∈ principalDomain := by
  simpa only [principalDomain, Set.mem_ofPred_eq, principalFactor, Complex.conj_im, Complex.conj_re,
    abs_neg, Real.sinc_neg, Real.cos_neg] using hw

theorem sin_eq_mul_sinc (v : ℝ) : Real.sin v = v * Real.sinc v := by
  by_cases hv : v = 0
  · subst v
    simp
  · rw [Real.sinc_of_ne_zero hv]
    field_simp

theorem expMul_im (w : ℂ) :
    (expMul w).im = Real.exp w.re * w.im * principalFactor w := by
  rw [expMul, Complex.mul_im, Complex.exp_im, Complex.exp_re, sin_eq_mul_sinc w.im]
  unfold principalFactor
  ring

theorem expMul_re (w : ℂ) :
    (expMul w).re = Real.exp w.re * (w.re * Real.cos w.im - w.im * Real.sin w.im) := by
  rw [expMul, Complex.mul_re, Complex.exp_im, Complex.exp_re]
  ring

theorem expMul_im_pos_iff {w : ℂ} (hw : w ∈ principalDomain) :
    0 < (expMul w).im ↔ 0 < w.im := by
  rw [expMul_im]
  have hp : 0 < Real.exp w.re * principalFactor w := mul_pos (Real.exp_pos _) hw.2
  rw [show Real.exp w.re * w.im * principalFactor w =
    w.im * (Real.exp w.re * principalFactor w) by ring]
  exact mul_pos_iff_of_pos_right hp

theorem expMul_im_eq_zero_iff {w : ℂ} (hw : w ∈ principalDomain) :
    (expMul w).im = 0 ↔ w.im = 0 := by
  rw [expMul_im]
  simp only [mul_eq_zero, (Real.exp_pos w.re).ne', hw.2.ne', false_or, or_false]

theorem expMul_conj (w : ℂ) : expMul (conj w) = conj (expMul w) := by
  simp only [expMul, map_mul, Complex.exp_conj]

theorem hasDerivAt_expMul (w : ℂ) :
    HasDerivAt expMul (Complex.exp w * (1 + w)) w := by
  have hh := (hasDerivAt_id w).mul (Complex.hasDerivAt_exp w)
  have hc : (1 : ℂ) * Complex.exp w + w * Complex.exp w = Complex.exp w * (1 + w) := by ring
  have h := hh.congr_deriv hc
  unfold expMul
  simpa only [Pi.mul_def, id_eq] using h

theorem analyticAt_expMul (w : ℂ) : AnalyticAt ℂ expMul w := by
  exact analyticAt_id.mul analyticAt_cexp

theorem expMul_deriv_ne_zero {w : ℂ} (hw : w ∈ principalDomain) :
    Complex.exp w * (1 + w) ≠ 0 := by
  apply mul_ne_zero (Complex.exp_ne_zero w)
  intro hh
  have he : w = -1 := by linear_combination hh
  exact neg_one_notMem_principalDomain (he ▸ hw)


theorem isOpen_slitPlane : IsOpen slitPlane := by
  change IsOpen ({z : ℂ | z.im = 0} ∩ {z : ℂ | z.re ≤ -Real.exp (-1)})ᶜ
  exact ((isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le Complex.continuous_re continuous_const)).isOpen_compl

theorem ofReal_mem_principalDomain (u : ℝ) : (u : ℂ) ∈ principalDomain ↔ -1 < u := by
  simp only [principalDomain, Set.mem_ofPred_eq, principalFactor, Complex.ofReal_im,
    Complex.ofReal_re, abs_zero, Real.sinc_zero, Real.cos_zero, mul_one,
    Real.pi_pos, true_and]
  constructor <;> intro h <;> linarith

theorem expMul_ofReal (u : ℝ) : expMul (u : ℂ) = (u * Real.exp u : ℝ) := by
  simp only [expMul, ← Complex.ofReal_exp, Complex.ofReal_mul]

theorem real_expMul_gt_cut {u : ℝ} (hu : -1 < u) :
    -Real.exp (-1) < u * Real.exp u := by
  have hh := Real.one_sub_lt_exp_neg (x := u + 1) (by linarith : u + 1 ≠ 0)
  have hm := mul_lt_mul_of_pos_right hh (Real.exp_pos u)
  have he : Real.exp (-(u + 1)) * Real.exp u = Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  linarith

theorem expMul_mapsTo_slitPlane : Set.MapsTo expMul principalDomain slitPlane := by
  intro w hw hcut
  have hi : w.im = 0 := (expMul_im_eq_zero_iff hw).mp hcut.1
  have hu : -1 < w.re := by
    have hh := hw.2
    simp only [principalFactor, hi, Real.sinc_zero, Real.cos_zero, mul_one] at hh
    linarith
  have hr : (expMul w).re = w.re * Real.exp w.re := by
    simp only [expMul_re, hi, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero]
    ring
  rw [hr] at hcut
  exact (not_le_of_gt (real_expMul_gt_cut hu)) hcut.2

theorem expMul_im_neg_iff {w : ℂ} (hw : w ∈ principalDomain) :
    (expMul w).im < 0 ↔ w.im < 0 := by
  have hh := expMul_im_pos_iff (principalDomain_conj hw)
  simpa only [expMul_conj, Complex.conj_im, neg_pos] using hh

end Paper.Lambert
