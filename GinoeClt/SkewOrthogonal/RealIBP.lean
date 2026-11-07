/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.Weight
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Real Gaussian skew integration by parts

The raising operator and real weight are those of the tau = 0 skew form
in Forrester--Nagao, arXiv:0806.0055v1, equations (4.9)--(4.10).
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Paper.SkewOrthogonal

/-- The Gaussian raising operator, defined without negative monomial powers. -/
def raising (Q : Polynomial ℂ) : Polynomial ℂ := Polynomial.X * Q - Q.derivative

@[simp] theorem raising_eval (Q : Polynomial ℂ) (z : ℂ) :
    (raising Q).eval z = z * Q.eval z - Q.derivative.eval z := by
  simp [raising]

/-- A polynomial restricted to the real axis, with the literal real Gaussian weight. -/
def realGaussianPolynomial (Q : Polynomial ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-x ^ 2 / 2) : ℂ) * Q.eval (x : ℂ)

theorem integrable_realGaussianPolynomial (Q : Polynomial ℂ) :
    Integrable (realGaussianPolynomial Q) := by
  have h := integrable_real_gaussian_polynomial Q (a := 1 / 2) (by norm_num)
  convert h using 1
  funext x
  dsimp only [realGaussianPolynomial]
  rw [show -x ^ 2 / 2 = -(1 / 2) * x ^ 2 by ring]

theorem hasDerivAt_realGaussianPolynomial (Q : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (realGaussianPolynomial Q) (-realGaussianPolynomial (raising Q) x) x := by
  have hg : HasDerivAt (fun y : ℝ ↦ Real.exp (-y ^ 2 / 2))
      (-(x * Real.exp (-x ^ 2 / 2))) x := by
    have hi : HasDerivAt (fun y : ℝ ↦ -y ^ 2 / 2) (-x) x := by
      convert ((hasDerivAt_id x).pow 2).neg.div_const 2 using 1
      · rfl
      · simp only [id_eq]
        ring
    convert hi.exp using 1
    ring
  have h := hg.ofReal_comp.mul (Q.hasDerivAt (x : ℂ)).comp_ofReal
  convert h using 1
  · rfl
  · simp only [realGaussianPolynomial, raising_eval, Complex.ofReal_neg, Complex.ofReal_mul]
    ring

theorem integral_realGaussianPolynomial_raising (Q : Polynomial ℂ) :
    (∫ y : ℝ, realGaussianPolynomial (raising Q) y) = 0 := by
  have h := integral_eq_zero_of_hasDerivAt_of_integrable
    (hasDerivAt_realGaussianPolynomial Q)
    (integrable_realGaussianPolynomial (raising Q)).neg
    (integrable_realGaussianPolynomial Q)
  simpa only [integral_neg, neg_eq_zero] using h

theorem integral_Ioi_realGaussianPolynomial_raising (Q : Polynomial ℂ) (x : ℝ) :
    (∫ y in Ioi x, realGaussianPolynomial (raising Q) y) = realGaussianPolynomial Q x := by
  have ht : Tendsto (realGaussianPolynomial Q) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := x)
      (fun y _ ↦ hasDerivAt_realGaussianPolynomial Q y)
      (integrable_realGaussianPolynomial (raising Q)).neg.integrableOn
      (integrable_realGaussianPolynomial Q).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y (_ : y ∈ Ici x) ↦ hasDerivAt_realGaussianPolynomial Q y)
    (integrable_realGaussianPolynomial (raising Q)).neg.integrableOn ht
  simpa only [integral_neg, zero_sub, neg_inj] using h

/-- Multiplication by the standard sign splits a genuine integrable function at a point. -/
theorem integral_complex_sign_mul (F : ℝ → ℂ) (hF : Integrable F) (x : ℝ) :
    (∫ y : ℝ, (SignType.sign (y - x) : ℂ) * F y) =
      2 * (∫ y in Ioi x, F y) - ∫ y : ℝ, F y := by
  have heq : (fun y : ℝ ↦ (SignType.sign (y - x) : ℂ) * F y) =
      (Ioi x).indicator F - (Iio x).indicator F := by
    funext y
    by_cases hp : x < y
    · have hn : ¬ y < x := not_lt_of_ge hp.le
      simp [sub_pos, hp, hn, Set.indicator]
    · by_cases hn : y < x <;>
        simp [sign_apply, sub_pos, sub_neg, hp, hn, Set.indicator]
  rw [heq]
  change (∫ y : ℝ, (Ioi x).indicator F y - (Iio x).indicator F y) = _
  rw [integral_sub (hF.indicator measurableSet_Ioi) (hF.indicator measurableSet_Iio),
    integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iio]
  have hadd : (∫ y in Ioi x, F y) + (∫ y in Iio x, F y) = ∫ y : ℝ, F y := by
    simpa only [compl_Ioi, integral_Iic_eq_integral_Iio] using
      integral_add_compl (s := Ioi x) measurableSet_Ioi hF
  rw [← hadd]
  ring

/-- Exact real sign-Gaussian integration by parts, with no boundary term at infinity. -/
theorem integral_sign_realGaussian_raising (Q : Polynomial ℂ) (x : ℝ) :
    (∫ y : ℝ, (SignType.sign (y - x) : ℂ) *
      realGaussianPolynomial (raising Q) y) = 2 * realGaussianPolynomial Q x := by
  rw [integral_complex_sign_mul _ (integrable_realGaussianPolynomial (raising Q)),
    integral_Ioi_realGaussianPolynomial_raising, integral_realGaussianPolynomial_raising, sub_zero]

/-- The same identity with both the weight and raising operator expanded. -/
theorem integral_sign_gaussian_raising (Q : Polynomial ℂ) (x : ℝ) :
    (∫ y : ℝ, (SignType.sign (y - x) : ℂ) * (Real.exp (-y ^ 2 / 2) : ℂ) *
      ((y : ℂ) * Q.eval (y : ℂ) - Q.derivative.eval (y : ℂ))) =
        2 * (Real.exp (-x ^ 2 / 2) : ℂ) * Q.eval (x : ℂ) := by
  simpa only [realGaussianPolynomial, raising_eval, mul_assoc] using
    integral_sign_realGaussian_raising Q x

/-- The literal real part of the Gaussian skew form, including its sign convention. -/
def realSkew (P Q : Polynomial ℂ) : ℂ :=
  ∫ x : ℝ, ∫ y : ℝ, (SignType.sign (y - x) : ℂ) *
    ((Real.exp (-(x ^ 2 + y ^ 2) / 2) : ℂ) * P.eval (x : ℂ) * Q.eval (y : ℂ))

/-- Actual joint integrability justifies the real skew form's iterated-integral convention. -/
theorem realSkew_eq_integral_prod (P Q : Polynomial ℂ) :
    realSkew P Q = ∫ p : ℝ × ℝ, (SignType.sign (p.2 - p.1) : ℂ) *
      ((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) : ℂ) *
        P.eval (p.1 : ℂ) * Q.eval (p.2 : ℂ)) := by
  have h := integrable_real_skew_polynomials P Q
  rw [Measure.volume_eq_prod] at h
  simpa only [realSkew, Measure.volume_eq_prod] using (integral_prod _ h).symm

/-- Real skew integration by parts produces the exact Gaussian diagonal term. -/
theorem realSkew_raising (P Q : Polynomial ℂ) :
    realSkew P (raising Q) =
      2 * ∫ x : ℝ, (Real.exp (-x ^ 2) : ℂ) * P.eval (x : ℂ) * Q.eval (x : ℂ) := by
  have hpoint (x : ℝ) :
      (∫ y : ℝ, (SignType.sign (y - x) : ℂ) *
        ((Real.exp (-(x ^ 2 + y ^ 2) / 2) : ℂ) *
          P.eval (x : ℂ) * (raising Q).eval (y : ℂ))) =
        2 * ((Real.exp (-x ^ 2) : ℂ) * P.eval (x : ℂ) * Q.eval (x : ℂ)) := by
    have heq : (fun y : ℝ ↦ (SignType.sign (y - x) : ℂ) *
        ((Real.exp (-(x ^ 2 + y ^ 2) / 2) : ℂ) *
          P.eval (x : ℂ) * (raising Q).eval (y : ℂ))) =
        fun y ↦ ((Real.exp (-x ^ 2 / 2) : ℂ) * P.eval (x : ℂ)) *
          ((SignType.sign (y - x) : ℂ) * realGaussianPolynomial (raising Q) y) := by
      funext y
      have he : Real.exp (-(x ^ 2 + y ^ 2) / 2) =
          Real.exp (-x ^ 2 / 2) * Real.exp (-y ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [realGaussianPolynomial]
      rw [he, Complex.ofReal_mul]
      ring
    rw [heq, integral_const_mul, integral_sign_realGaussian_raising]
    have he : Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [realGaussianPolynomial]
    calc
      _ = 2 * ((Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) *
          P.eval (x : ℂ) * Q.eval (x : ℂ) := by
        rw [Complex.ofReal_mul]
        ring
      _ = _ := by rw [he]; ring
  unfold realSkew
  calc
    _ = ∫ x : ℝ, 2 * ((Real.exp (-x ^ 2) : ℂ) *
        P.eval (x : ℂ) * Q.eval (x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = _ := integral_const_mul _ _

end Paper.SkewOrthogonal
