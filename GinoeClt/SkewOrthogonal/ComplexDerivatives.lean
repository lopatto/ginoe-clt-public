/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.RealIBP

/-! # Derivatives for the exact complex Gaussian skew form

These are literal Cartesian derivatives of the tau = 0 weight and polynomial
expressions, before any integration by parts or boundary-limit argument.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set

namespace Paper.SkewOrthogonal

/-- Ordinary Cartesian complex coordinates, with their Euclidean meaning. -/
def point (x y : ℝ) : ℂ := ⟨x, y⟩

@[simp] theorem point_re (x y : ℝ) : (point x y).re = x := rfl
@[simp] theorem point_im (x y : ℝ) : (point x y).im = y := rfl
@[simp] theorem conj_point (x y : ℝ) : starRingEnd ℂ (point x y) = point x (-y) := rfl

/-- The exact weight in Cartesian coordinates. -/
def weightXY (x y : ℝ) : ℝ := complexWeight (point x y)

/-- The Gaussian factor created by differentiating the complementary tail. -/
def gaussianXY (x y : ℝ) : ℝ := Real.exp (-x ^ 2 - y ^ 2)

/-- The exact real coefficient in the differentiated tail. -/
def skewConstant : ℝ := 2 * Real.sqrt 2 / Real.sqrt Real.pi

theorem weightXY_eq (x y : ℝ) :
    weightXY x y = Real.exp (-x ^ 2 + y ^ 2) * Kernel.erfc (Real.sqrt 2 * y) := by
  unfold weightXY complexWeight
  simp only [pow_two, Complex.mul_re, point_re, point_im]
  congr 2
  ring

theorem hasDerivAt_weightXY_left (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ weightXY t y) (-2 * x * weightXY x y) x := by
  simp_rw [weightXY_eq]
  have hi : HasDerivAt (fun t : ℝ ↦ -t ^ 2 + y ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).neg.add_const (y ^ 2) using 1
    · rfl
    · simp only [id_eq]
      ring
  apply (hi.exp.mul_const (Kernel.erfc (Real.sqrt 2 * y))).congr_deriv
  ring

theorem hasDerivAt_weightXY_right (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ weightXY x t)
      (2 * y * weightXY x y - skewConstant * gaussianXY x y) y := by
  simp_rw [weightXY_eq]
  have hi : HasDerivAt (fun t : ℝ ↦ -x ^ 2 + t ^ 2) (2 * y) y := by
    convert ((hasDerivAt_id y).pow 2).const_add (-x ^ 2) using 1
    · rfl
    · simp only [id_eq]
      ring
  have ht : HasDerivAt (fun t : ℝ ↦ Kernel.erfc (Real.sqrt 2 * t))
      ((-(2 / Real.sqrt Real.pi) * Real.exp (-(Real.sqrt 2 * y) ^ 2)) * Real.sqrt 2) y := by
    simpa only [Function.comp_apply, mul_one] using!
      (Kernel.hasDerivAt_erfc (Real.sqrt 2 * y)).comp y
        ((hasDerivAt_id y).const_mul (Real.sqrt 2))
  have he : Real.exp (-x ^ 2 + y ^ 2) * Real.exp (-(Real.sqrt 2 * y) ^ 2) =
      gaussianXY x y := by
    rw [← Real.exp_add]
    unfold gaussianXY
    congr 1
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  apply (hi.exp.mul ht).congr_deriv
  calc
    _ = 2 * y * (Real.exp (-x ^ 2 + y ^ 2) * Kernel.erfc (Real.sqrt 2 * y)) -
        skewConstant * (Real.exp (-x ^ 2 + y ^ 2) * Real.exp (-(Real.sqrt 2 * y) ^ 2)) := by
      unfold skewConstant
      ring
    _ = _ := by rw [he]

theorem hasDerivAt_point_left (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ point t y) 1 x := by
  have h : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + (y : ℂ) * Complex.I) 1 x := by
    simpa using! (hasDerivAt_id x).ofReal_comp.add_const ((y : ℂ) * Complex.I)
  convert h using 1
  funext t
  apply Complex.ext <;> simp [point]

theorem hasDerivAt_point_right (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ point x t) Complex.I y := by
  have h : HasDerivAt (fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * Complex.I) Complex.I y := by
    simpa using! ((hasDerivAt_id y).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)
  convert h using 1
  funext t
  apply Complex.ext <;> simp [point]

theorem hasDerivAt_eval_point_left (P : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ P.eval (point t y)) (P.derivative.eval (point x y)) x := by
  simpa only [Function.comp_apply, mul_one] using!
    (P.hasDerivAt (point x y)).comp x (hasDerivAt_point_left x y)

theorem hasDerivAt_eval_point_right (P : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ P.eval (point x t))
      (P.derivative.eval (point x y) * Complex.I) y := by
  simpa only [Function.comp_apply] using!
    (P.hasDerivAt (point x y)).comp y (hasDerivAt_point_right x y)

theorem hasDerivAt_eval_conj_point_right (P : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ P.eval (point x (-t)))
      (-(P.derivative.eval (point x (-y)) * Complex.I)) y := by
  have hn : HasDerivAt (fun t : ℝ ↦ -t) (-1 : ℝ) y := by
    simpa using! (hasDerivAt_id y).neg
  simpa only [Function.comp_apply, neg_smul, one_smul] using!
    (hasDerivAt_eval_point_right P x (-y)).scomp y hn

/-- The antisymmetric polynomial-weight expression differentiated horizontally. -/
def skewMinus (P Q : Polynomial ℂ) (x y : ℝ) : ℂ :=
  (weightXY x y : ℂ) *
    (P.eval (point x y) * Q.eval (point x (-y)) -
      Q.eval (point x y) * P.eval (point x (-y)))

/-- The symmetric polynomial-weight expression differentiated vertically. -/
def skewPlus (P Q : Polynomial ℂ) (x y : ℝ) : ℂ :=
  (weightXY x y : ℂ) *
    (P.eval (point x y) * Q.eval (point x (-y)) +
      Q.eval (point x y) * P.eval (point x (-y)))

/-- The explicit horizontal derivative, with no derivative operator hidden in the definition. -/
def skewMinusDx (P Q : Polynomial ℂ) (x y : ℝ) : ℂ :=
  ((-2 * x * weightXY x y : ℝ) : ℂ) *
    (P.eval (point x y) * Q.eval (point x (-y)) -
      Q.eval (point x y) * P.eval (point x (-y))) +
  (weightXY x y : ℂ) *
    (P.derivative.eval (point x y) * Q.eval (point x (-y)) +
      P.eval (point x y) * Q.derivative.eval (point x (-y)) -
      Q.derivative.eval (point x y) * P.eval (point x (-y)) -
      Q.eval (point x y) * P.derivative.eval (point x (-y)))

/-- The explicit vertical derivative, including the Gaussian tail contribution. -/
def skewPlusDy (P Q : Polynomial ℂ) (x y : ℝ) : ℂ :=
  ((2 * y * weightXY x y - skewConstant * gaussianXY x y : ℝ) : ℂ) *
    (P.eval (point x y) * Q.eval (point x (-y)) +
      Q.eval (point x y) * P.eval (point x (-y))) +
  (weightXY x y : ℂ) * Complex.I *
    (P.derivative.eval (point x y) * Q.eval (point x (-y)) -
      P.eval (point x y) * Q.derivative.eval (point x (-y)) +
      Q.derivative.eval (point x y) * P.eval (point x (-y)) -
      Q.eval (point x y) * P.derivative.eval (point x (-y)))

theorem hasDerivAt_skewMinus_left (P Q : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ skewMinus P Q t y) (skewMinusDx P Q x y) x := by
  have h₁ := (hasDerivAt_eval_point_left P x y).mul
    (hasDerivAt_eval_point_left Q x (-y))
  have h₂ := (hasDerivAt_eval_point_left Q x y).mul
    (hasDerivAt_eval_point_left P x (-y))
  have h := (hasDerivAt_weightXY_left x y).ofReal_comp.mul (h₁.sub h₂)
  convert h using 1
  · rfl
  · dsimp only [skewMinusDx, Pi.mul_apply, Pi.sub_apply]
    ring

theorem hasDerivAt_skewPlus_right (P Q : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ skewPlus P Q x t) (skewPlusDy P Q x y) y := by
  have h₁ := (hasDerivAt_eval_point_right P x y).mul
    (hasDerivAt_eval_conj_point_right Q x y)
  have h₂ := (hasDerivAt_eval_point_right Q x y).mul
    (hasDerivAt_eval_conj_point_right P x y)
  have h := (hasDerivAt_weightXY_right x y).ofReal_comp.mul (h₁.add h₂)
  convert h using 1
  · rfl
  · dsimp only [skewPlusDy, Pi.mul_apply, Pi.add_apply]
    ring

/-- The exact pointwise derivative cancellation underlying the complex skew IBP.
The coefficients of the polynomials are not conjugated. -/
theorem complex_skew_derivative_identity (P Q : Polynomial ℂ) (x y : ℝ) :
    (2 * Complex.I) * (weightXY x y : ℂ) *
      (P.eval (point x y) * (raising Q).eval (point x (-y)) -
        (raising Q).eval (point x y) * P.eval (point x (-y))) =
      -Complex.I * skewMinusDx P Q x y + skewPlusDy P Q x y +
        (skewConstant : ℂ) * (gaussianXY x y : ℂ) *
          (P.eval (point x y) * Q.eval (point x (-y)) +
            Q.eval (point x y) * P.eval (point x (-y))) := by
  have hz : point x y = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [point]
  have ht : point x (-y) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [point]
  simp only [raising_eval, skewMinusDx, skewPlusDy, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  rw [hz, ht]
  ring_nf; simp [Complex.I_sq]

/-- The lower vertical endpoint is the actual real Gaussian diagonal expression. -/
theorem skewPlus_zero (P Q : Polynomial ℂ) (x : ℝ) :
    skewPlus P Q x 0 =
      2 * (Real.exp (-x ^ 2) : ℂ) * P.eval (x : ℂ) * Q.eval (x : ℂ) := by
  have hp : point x 0 = (x : ℂ) := by apply Complex.ext <;> simp [point]
  simp only [skewPlus, weightXY_eq, neg_zero, hp]
  norm_num [Kernel.erfc_zero]
  ring

end Paper.SkewOrthogonal
