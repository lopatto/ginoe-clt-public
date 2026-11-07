/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.ComplexIBP

/-! # Algebraic identities of the actual Gaussian skew integrals -/
@[expose] public section
noncomputable section
open MeasureTheory Set

namespace Paper.SkewOrthogonal

theorem realSkew_antisymm (P Q : Polynomial ℂ) : realSkew Q P = -realSkew P Q := by
  rw [realSkew_eq_integral_prod, realSkew_eq_integral_prod]
  have h := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ ↦ (SignType.sign (p.2 - p.1) : ℂ) *
      ((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) : ℂ) * P.eval (p.1 : ℂ) * Q.eval (p.2 : ℂ)))
  rw [← Measure.volume_eq_prod] at h
  rw [← h, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with p
  have hs : (SignType.sign (p.2 - p.1) : ℂ) = -(SignType.sign (p.1 - p.2) : ℂ) := by
    rw [show p.2 - p.1 = -(p.1 - p.2) by ring, Left.sign_neg, SignType.coe_neg]
  have he : Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) =
      Real.exp (-(p.2 ^ 2 + p.1 ^ 2) / 2) := by rw [add_comm]
  dsimp only [Prod.swap]
  rw [hs, he]
  ring

theorem complexSkew_antisymm (P Q : Polynomial ℂ) : complexSkew Q P = -complexSkew P Q := by
  unfold complexSkew
  rw [← mul_neg, ← integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  ring

theorem skewForm_antisymm (P Q : Polynomial ℂ) : skewForm Q P = -skewForm P Q := by
  rw [skewForm, realSkew_antisymm, complexSkew_antisymm, skewForm]
  ring

theorem skewForm_self (P : Polynomial ℂ) : skewForm P P = 0 := by
  have h : skewForm P P + skewForm P P = 0 :=
    add_eq_zero_iff_eq_neg.mpr (skewForm_antisymm P P)
  have h₂ : (2 : ℂ) * skewForm P P = 0 := by simpa only [two_mul] using h
  exact (mul_eq_zero.mp h₂).resolve_left (by norm_num)

theorem integrableOn_complexSkew_integrand (P Q : Polynomial ℂ) :
    IntegrableOn (fun z : ℂ ↦ (complexWeight z : ℂ) *
      (P.eval z * Q.eval (starRingEnd ℂ z) - Q.eval z * P.eval (starRingEnd ℂ z)))
      {z : ℂ | 0 < z.im} := by
  have h := (integrableOn_complexWeight_polynomials P Q).sub
    (integrableOn_complexWeight_polynomials Q P)
  convert h using 1
  funext z
  dsimp only [Pi.sub_apply]
  ring

theorem realSkew_sub_right (P Q R : Polynomial ℂ) :
    realSkew P (Q - R) = realSkew P Q - realSkew P R := by
  rw [realSkew_eq_integral_prod, realSkew_eq_integral_prod, realSkew_eq_integral_prod,
    ← integral_sub (integrable_real_skew_polynomials P Q) (integrable_real_skew_polynomials P R)]
  congr 1
  funext p
  simp only [Polynomial.eval_sub]
  ring

theorem complexSkew_sub_right (P Q R : Polynomial ℂ) :
    complexSkew P (Q - R) = complexSkew P Q - complexSkew P R := by
  unfold complexSkew
  rw [← mul_sub]
  congr 1
  rw [← integral_sub (integrableOn_complexSkew_integrand P Q)
    (integrableOn_complexSkew_integrand P R)]
  congr 1
  funext z
  simp only [Polynomial.eval_sub]
  ring

theorem skewForm_sub_right (P Q R : Polynomial ℂ) :
    skewForm P (Q - R) = skewForm P Q - skewForm P R := by
  rw [skewForm, realSkew_sub_right, complexSkew_sub_right, skewForm, skewForm]
  ring

theorem realSkew_C_mul_right (P Q : Polynomial ℂ) (c : ℂ) :
    realSkew P (Polynomial.C c * Q) = c * realSkew P Q := by
  rw [realSkew_eq_integral_prod, realSkew_eq_integral_prod, ← integral_const_mul]
  congr 1
  funext p
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem complexSkew_C_mul_right (P Q : Polynomial ℂ) (c : ℂ) :
    complexSkew P (Polynomial.C c * Q) = c * complexSkew P Q := by
  calc
    _ = (2 * Complex.I) * ∫ z in {z : ℂ | 0 < z.im}, c * ((complexWeight z : ℂ) *
        (P.eval z * Q.eval (starRingEnd ℂ z) - Q.eval z * P.eval (starRingEnd ℂ z))) := by
      unfold complexSkew
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring
    _ = _ := by rw [integral_const_mul]; unfold complexSkew; ring

theorem skewForm_C_mul_right (P Q : Polynomial ℂ) (c : ℂ) :
    skewForm P (Polynomial.C c * Q) = c * skewForm P Q := by
  rw [skewForm, realSkew_C_mul_right, complexSkew_C_mul_right, skewForm]
  ring

end Paper.SkewOrthogonal
