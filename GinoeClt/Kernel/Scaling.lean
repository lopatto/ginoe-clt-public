/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Definitions
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-! # Exact planar-product Jacobian for the square-root matrix scaling -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Pointwise

namespace Paper.Kernel

theorem finrank_complex_product (k : ℕ) : Module.finrank ℝ (Fin k → ℂ) = 2 * k := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]

theorem integral_rescale (k N : ℕ) (f : (Fin k → ℂ) → ℂ) :
    (∫ x : Fin k → ℂ, f (fun i => rescale N (x i))) = ((N : ℝ) ^ k)⁻¹ • ∫ x, f x := by
  have h := Measure.integral_comp_smul (volume : Measure (Fin k → ℂ)) f
    (Real.sqrt (N : ℝ))
  rw [finrank_complex_product, pow_mul, Real.sq_sqrt (Nat.cast_nonneg N),
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg N) k))] at h
  calc
    (∫ x : Fin k → ℂ, f (fun i => rescale N (x i))) =
        ∫ x, f (Real.sqrt (N : ℝ) • x) := by
      apply integral_congr_ae
      filter_upwards with x
      apply congrArg f
      funext i
      change (Real.sqrt (N : ℝ) : ℂ) * x i = Real.sqrt (N : ℝ) • x i
      rw [Complex.real_smul]
    _ = _ := h

theorem rescale_product_domain (A : Set ℂ) (k N : ℕ) (hN : 0 < N) :
    (Real.sqrt (N : ℝ) : ℝ) • Set.univ.pi (fun _ : Fin k => A) =
      Set.univ.pi (fun _ : Fin k => rescale N '' A) := by
  have hR : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  rw [Set.smul_set_pi_of_isUnit (isUnit_iff_ne_zero.mpr hR)]
  congr 1

theorem setIntegral_rescale (A : Set ℂ) (k N : ℕ) (hN : 0 < N)
    (f : (Fin k → ℂ) → ℂ) :
    (∫ x in Set.univ.pi (fun _ : Fin k => A), f (fun i => rescale N (x i))) =
      ((N : ℝ) ^ k)⁻¹ •
        ∫ x in Set.univ.pi (fun _ : Fin k => rescale N '' A), f x := by
  have hR : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  have h := Measure.setIntegral_comp_smul (volume : Measure (Fin k → ℂ)) f
    (Set.univ.pi (fun _ : Fin k => A)) hR
  rw [finrank_complex_product, pow_mul, Real.sq_sqrt (Nat.cast_nonneg N),
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg N) k)),
    rescale_product_domain A k N hN] at h
  calc
    (∫ x in Set.univ.pi (fun _ : Fin k => A), f (fun i => rescale N (x i))) =
        ∫ x in Set.univ.pi (fun _ : Fin k => A), f (Real.sqrt (N : ℝ) • x) := by
      apply integral_congr_ae
      filter_upwards with x
      apply congrArg f
      funext i
      change (Real.sqrt (N : ℝ) : ℂ) * x i = Real.sqrt (N : ℝ) • x i
      rw [Complex.real_smul]
    _ = _ := h

/-- Source-facing product-area change of variables. No simple-root assumption occurs. -/
theorem pow_mul_setIntegral_rescale (A : Set ℂ) (k N : ℕ) (hN : 0 < N)
    (f : (Fin k → ℂ) → ℂ) :
    (N : ℂ) ^ k * (∫ x in Set.univ.pi (fun _ : Fin k => A),
      f (fun i => rescale N (x i))) =
        ∫ x in Set.univ.pi (fun _ : Fin k => rescale N '' A), f x := by
  rw [setIntegral_rescale A k N hN f, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_natCast, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero k (Nat.cast_ne_zero.mpr hN.ne')), one_mul]

end Paper.Kernel
