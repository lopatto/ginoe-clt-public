/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.ComplexDerivatives
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Genuine Cartesian integrability for complex skew integration by parts -/
@[expose] public section
noncomputable section
open MeasureTheory Set

namespace Paper.SkewOrthogonal

/-- The actual upper half-plane in ordinary real product coordinates. -/
def upperXY : Set (ℝ × ℝ) := Set.univ ×ˢ Ioi 0

/-- The exact polynomial-weight product in Cartesian coordinates. -/
def weightedXY (P Q : Polynomial ℂ) (x y : ℝ) : ℂ :=
  (weightXY x y : ℂ) * P.eval (point x y) * Q.eval (point x (-y))

/-- The corresponding ordinary planar Gaussian polynomial product. -/
def gaussianWeightedXY (P Q : Polynomial ℂ) (x y : ℝ) : ℂ :=
  (gaussianXY x y : ℂ) * P.eval (point x y) * Q.eval (point x (-y))

theorem integrableOn_weightedXY (P Q : Polynomial ℂ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ weightedXY P Q p.1 p.2) upperXY := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).integrableOn_comp_preimage
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    |>.mpr (integrableOn_complexWeight_polynomials P Q)
  have he : Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | 0 < z.im} = upperXY := by
    ext p
    simp [upperXY]
  rw [he] at h
  simpa only [Function.comp_apply, Complex.measurableEquivRealProd_symm_apply,
    weightedXY, weightXY, point, map_neg, neg_neg] using! h

theorem integrable_gaussianWeightedXY (P Q : Polynomial ℂ) :
    Integrable (fun p : ℝ × ℝ ↦ gaussianWeightedXY P Q p.1 p.2) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    |>.mpr (integrable_gaussian_polynomials P Q (a := 1) (by norm_num))
  have he : (fun p : ℝ × ℝ ↦ gaussianWeightedXY P Q p.1 p.2) =
      (fun z : ℂ ↦ (Real.exp (-1 * ‖z‖ ^ 2) : ℂ) *
        P.eval z * Q.eval (starRingEnd ℂ z)) ∘ Complex.measurableEquivRealProd.symm := by
    funext p
    have hn : ‖point p.1 p.2‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [point, pow_two]
    dsimp only [gaussianWeightedXY, gaussianXY, Function.comp_apply]
    change (Real.exp (-p.1 ^ 2 - p.2 ^ 2) : ℂ) *
      P.eval (point p.1 p.2) * Q.eval (point p.1 (-p.2)) =
      (Real.exp (-1 * ‖point p.1 p.2‖ ^ 2) : ℂ) *
        P.eval (point p.1 p.2) * Q.eval (point p.1 (-p.2))
    rw [hn, show -p.1 ^ 2 - p.2 ^ 2 = -1 * (p.1 ^ 2 + p.2 ^ 2) by ring]
  rw [he]
  exact h

theorem integrableOn_x_mul_weightedXY (P Q : Polynomial ℂ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * weightedXY P Q p.1 p.2) upperXY := by
  change Integrable _ (volume.restrict upperXY)
  have h := ((integrableOn_weightedXY (Polynomial.X * P) Q).add
    (integrableOn_weightedXY P (Polynomial.X * Q))).const_mul (1 / 2 : ℂ)
  convert h using 1
  funext p
  have hx : (p.1 : ℂ) = (point p.1 p.2 + point p.1 (-p.2)) / 2 := by
    apply Complex.ext <;> simp [point]
  dsimp only [Pi.add_apply, weightedXY]
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  rw [hx]
  ring

theorem integrableOn_y_mul_weightedXY (P Q : Polynomial ℂ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ (p.2 : ℂ) * weightedXY P Q p.1 p.2) upperXY := by
  change Integrable _ (volume.restrict upperXY)
  have h := ((integrableOn_weightedXY (Polynomial.X * P) Q).sub
    (integrableOn_weightedXY P (Polynomial.X * Q))).const_mul (-Complex.I / 2)
  convert h using 1
  funext p
  have hy : (p.2 : ℂ) = (-Complex.I / 2) * (point p.1 p.2 - point p.1 (-p.2)) := by
    apply Complex.ext <;> simp [point]; ring
  dsimp only [Pi.sub_apply, weightedXY]
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  rw [hy]
  ring

theorem integrableOn_skewMinus (P Q : Polynomial ℂ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ skewMinus P Q p.1 p.2) upperXY := by
  have h := (integrableOn_weightedXY P Q).sub (integrableOn_weightedXY Q P)
  convert h using 1
  funext p
  dsimp only [Pi.sub_apply, skewMinus, weightedXY]
  ring

theorem integrableOn_skewPlus (P Q : Polynomial ℂ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ skewPlus P Q p.1 p.2) upperXY := by
  have h := (integrableOn_weightedXY P Q).add (integrableOn_weightedXY Q P)
  convert h using 1
  funext p
  dsimp only [Pi.add_apply, skewPlus, weightedXY]
  ring

theorem integrableOn_skewMinusDx (P Q : Polynomial ℂ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ skewMinusDx P Q p.1 p.2) upperXY := by
  change Integrable _ (volume.restrict upperXY)
  have h₀ := ((integrableOn_x_mul_weightedXY P Q).sub
    (integrableOn_x_mul_weightedXY Q P)).const_mul (-2 : ℂ)
  have h₁ := (((integrableOn_weightedXY P.derivative Q).add
    (integrableOn_weightedXY P Q.derivative)).sub
      (integrableOn_weightedXY Q.derivative P)).sub
        (integrableOn_weightedXY Q P.derivative)
  convert h₀.add h₁ using 1
  funext p
  dsimp only [Pi.add_apply, Pi.sub_apply, skewMinusDx, weightedXY]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

theorem integrableOn_skewPlusDy (P Q : Polynomial ℂ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ skewPlusDy P Q p.1 p.2) upperXY := by
  change Integrable _ (volume.restrict upperXY)
  have h₀ := ((integrableOn_y_mul_weightedXY P Q).add
    (integrableOn_y_mul_weightedXY Q P)).const_mul (2 : ℂ)
  have hG := ((integrable_gaussianWeightedXY P Q).integrableOn (s := upperXY) |>.add
    (integrable_gaussianWeightedXY Q P).integrableOn (s := upperXY)).const_mul (-(skewConstant : ℂ))
  have h₁ := ((((integrableOn_weightedXY P.derivative Q).sub
    (integrableOn_weightedXY P Q.derivative)).add
      (integrableOn_weightedXY Q.derivative P)).sub
        (integrableOn_weightedXY Q P.derivative)).const_mul Complex.I
  convert (h₀.add hG).add h₁ using 1
  funext p
  dsimp only [Pi.add_apply, Pi.sub_apply, skewPlusDy, weightedXY, gaussianWeightedXY]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat]
  ring

end Paper.SkewOrthogonal
