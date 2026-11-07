/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Complex.MeanValue

/-! # Ordinary planar Gaussian mass, moments and angular averaging -/

@[expose] public section
noncomputable section
open MeasureTheory Set Complex
open scoped Real Topology

namespace Paper.GaussianIntegrals

private theorem gamma_two : Real.Gamma 2 = 1 := by
  simp

theorem gaussian_mass {a : ℝ} (ha : 0 < a) :
    (∫ z : ℂ, Real.exp (-a * ‖z‖ ^ 2)) = Real.pi / a := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 2) (b := a) (by norm_num) ha
  norm_num [Real.rpow_two, Real.rpow_neg_one, gamma_two] at h
  simpa only [neg_mul, div_eq_mul_inv, mul_comm] using h

theorem gaussian_second_moment {a : ℝ} (ha : 0 < a) :
    (∫ z : ℂ, ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2)) = Real.pi / a ^ 2 := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := a)
    (by norm_num) (by norm_num) ha
  norm_num [Real.rpow_two, Real.rpow_neg_natCast, gamma_two] at h
  simpa only [neg_mul, div_eq_mul_inv, mul_comm] using h

theorem gaussian_first_moment_unit :
    (∫ z : ℂ, ‖z‖ * Real.exp (-‖z‖ ^ 2)) = Real.pi * Real.sqrt Real.pi / 2 := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 1)
    (by norm_num) (by norm_num)
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have hh := Real.Gamma_nat_add_one_add_half 0
    norm_num at hh
    exact hh
  norm_num [Real.rpow_two, hg] at h
  simpa only [mul_div_assoc] using h


theorem integrable_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ => Real.exp (-a * ‖z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_mass ha]
  exact (div_pos Real.pi_pos ha).ne'

theorem integrable_gaussian_second_moment {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ => ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_second_moment ha]
  exact (div_pos Real.pi_pos (sq_pos_of_pos ha)).ne'

theorem integrable_gaussian_first_moment_unit :
    Integrable (fun z : ℂ => ‖z‖ * Real.exp (-‖z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_first_moment_unit]
  exact (div_pos (mul_pos Real.pi_pos (Real.sqrt_pos.mpr Real.pi_pos)) (by norm_num)).ne'

/-- The exact angular identity used to remove successive open-chain
interaction factors. The native mean-value theorem applies to the entire exponential. -/
theorem angular_exponential (α : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (α * Complex.exp ((θ : ℂ) * Complex.I))) = (2 * Real.pi : ℂ) := by
  have hd : Differentiable ℂ (fun z : ℂ => Complex.exp (α * z)) :=
    Complex.differentiable_exp.comp (differentiable_id.const_mul α)
  have hc : DiffContOnCl ℂ (fun z : ℂ => Complex.exp (α * z))
      (Metric.ball (0 : ℂ) |(1 : ℝ)|) :=
    ⟨hd.differentiableOn, hd.continuous.continuousOn⟩
  have hm : Real.circleAverage (fun z : ℂ => Complex.exp (α * z)) 0 1 = 1 := by
    simpa only [mul_zero, Complex.exp_zero] using hc.circleAverage
  rw [Real.circleAverage_def] at hm
  have hh := congrArg (fun z : ℂ => (2 * Real.pi : ℝ) • z) hm
  rw [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul] at hh
  simpa only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.real_smul,
    mul_one, Complex.ofReal_mul, Complex.ofReal_ofNat] using hh

theorem gaussian_first_moment {a : ℝ} (ha : 0 < a) :
    (∫ z : ℂ, ‖z‖ * Real.exp (-a * ‖z‖ ^ 2)) =
      Real.pi * Real.sqrt Real.pi / (2 * a * Real.sqrt a) := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := a)
    (by norm_num) (by norm_num) ha
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have hh := Real.Gamma_nat_add_one_add_half 0
    norm_num at hh
    exact hh
  have hp : a ^ (-(3 / 2) : ℝ) = (a * Real.sqrt a)⁻¹ := by
    rw [Real.rpow_neg ha.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add ha, Real.rpow_one, ← Real.sqrt_eq_rpow]
  norm_num [Real.rpow_two, hg] at h
  rw [hp] at h
  simpa only [neg_mul] using h.trans (by ring)

theorem integrable_gaussian_first_moment {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ => ‖z‖ * Real.exp (-a * ‖z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_first_moment ha]
  exact (div_pos (mul_pos Real.pi_pos (Real.sqrt_pos.mpr Real.pi_pos))
    (mul_pos (mul_pos (by norm_num) ha) (Real.sqrt_pos.mpr ha))).ne'

/-- The first normalized radial kernel in the variance calculation. -/
theorem unit_crossing_normalization :
    (∫ z : ℂ, ‖z‖ * (2 / Real.pi ^ (3 / 2 : ℝ) * Real.exp (-‖z‖ ^ 2))) = 1 := by
  have hp : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have heq : (fun z : ℂ => ‖z‖ * (2 / Real.pi ^ (3 / 2 : ℝ) *
      Real.exp (-‖z‖ ^ 2))) = (fun z : ℂ => (2 / Real.pi ^ (3 / 2 : ℝ)) *
      (‖z‖ * Real.exp (-‖z‖ ^ 2))) := funext fun z => by ring
  rw [heq, integral_const_mul, gaussian_first_moment_unit, hp]
  field_simp

/-- The second normalized radial kernel, used for the crossing trace error. -/
theorem half_crossing_normalization :
    (∫ z : ℂ, ‖z‖ * (1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ)) *
      Real.exp (-‖z‖ ^ 2 / 2))) = 1 := by
  have h := gaussian_first_moment (a := 1 / 2) (by norm_num)
  have hp : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt (1 / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.sqrt_inv]
  have heq : (fun z : ℂ => ‖z‖ * (1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ)) *
      Real.exp (-‖z‖ ^ 2 / 2))) = (fun z : ℂ =>
      (1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ))) *
        (‖z‖ * Real.exp (-(1 / 2) * ‖z‖ ^ 2))) := by
    funext z
    rw [show -‖z‖ ^ 2 / 2 = -(1 / 2) * ‖z‖ ^ 2 by ring]
    ring
  rw [heq, integral_const_mul, h, hp, hs]
  field_simp

end Paper.GaussianIntegrals
