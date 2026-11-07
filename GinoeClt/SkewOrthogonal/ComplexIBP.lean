/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.ComplexIntegrability

/-! # Integrated complex Gaussian skew cancellation

Slice integrability is taken almost everywhere from the proved joint L1 statements.
The functions and their actual derivatives supply the vanishing limits at infinity.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Paper.SkewOrthogonal

theorem integrable_prod_upper {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F upperXY) :
    Integrable F ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  simpa only [IntegrableOn, upperXY, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ] using hF

theorem integral_upper_eq_iterated {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F upperXY) :
    (∫ p in upperXY, F p) = ∫ x : ℝ, ∫ y in Ioi (0 : ℝ), F (x, y) := by
  have h := integral_prod F (integrable_prod_upper hF)
  simpa only [upperXY, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ] using h

theorem integral_upper_eq_iterated_symm {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F upperXY) :
    (∫ p in upperXY, F p) = ∫ y in Ioi (0 : ℝ), ∫ x : ℝ, F (x, y) := by
  have h := integral_prod_symm F (integrable_prod_upper hF)
  simpa only [upperXY, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ] using h

/-- The horizontal derivative integrates to zero, using only true AE sliced L1. -/
theorem integral_upper_skewMinusDx (P Q : Polynomial ℂ) :
    (∫ p in upperXY, skewMinusDx P Q p.1 p.2) = 0 := by
  have hF := integrable_prod_upper (integrableOn_skewMinus P Q)
  have hD := integrable_prod_upper (integrableOn_skewMinusDx P Q)
  rw [integral_upper_eq_iterated_symm (integrableOn_skewMinusDx P Q)]
  have heq : (fun y : ℝ ↦ ∫ x : ℝ, skewMinusDx P Q x y) =ᵐ[
      (volume : Measure ℝ).restrict (Ioi 0)] 0 := by
    filter_upwards [hF.prod_left_ae, hD.prod_left_ae] with y hFy hDy
    exact integral_eq_zero_of_hasDerivAt_of_integrable
      (fun x ↦ hasDerivAt_skewMinus_left P Q x y) hDy hFy
  rw [integral_congr_ae heq]
  simp

/-- The vertical FTC boundary is obtained for almost every horizontal slice. -/
theorem integral_upper_skewPlusDy (P Q : Polynomial ℂ) :
    (∫ p in upperXY, skewPlusDy P Q p.1 p.2) =
      -(2 * ∫ x : ℝ, (Real.exp (-x ^ 2) : ℂ) * P.eval (x : ℂ) * Q.eval (x : ℂ)) := by
  have hF := integrable_prod_upper (integrableOn_skewPlus P Q)
  have hD := integrable_prod_upper (integrableOn_skewPlusDy P Q)
  rw [integral_upper_eq_iterated (integrableOn_skewPlusDy P Q)]
  have heq : (fun x : ℝ ↦ ∫ y in Ioi (0 : ℝ), skewPlusDy P Q x y) =ᵐ[volume]
      (fun x ↦ -skewPlus P Q x 0) := by
    filter_upwards [hF.prod_right_ae, hD.prod_right_ae] with x hFx hDx
    have ht : Tendsto (skewPlus P Q x) atTop (𝓝 0) :=
      tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
        (fun y _ ↦ hasDerivAt_skewPlus_right P Q x y) hDx hFx
    simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun y (_ : y ∈ Ici 0) ↦ hasDerivAt_skewPlus_right P Q x y) hDx ht
  rw [integral_congr_ae heq, integral_neg]
  simp_rw [skewPlus_zero]
  rw [← integral_const_mul]
  congr 2
  funext x
  ring

/-- Reflection exchanges the two polynomial factors without conjugating their coefficients. -/
theorem gaussianWeightedXY_reflection (P Q : Polynomial ℂ) (x y : ℝ) :
    gaussianWeightedXY Q P x y = gaussianWeightedXY P Q x (-y) := by
  dsimp only [gaussianWeightedXY, gaussianXY]
  simp only [neg_neg, neg_sq]
  ring

theorem integral_Ioi_add_reflection (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ y in Ioi (0 : ℝ), F y) + (∫ y in Ioi (0 : ℝ), F (-y)) = ∫ y : ℝ, F y := by
  have hn : (∫ y in Ioi (0 : ℝ), F (-y)) = ∫ y in Iio (0 : ℝ), F y := by
    simpa only [neg_preimage, neg_Iio, neg_zero] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
        (Homeomorph.neg ℝ).measurableEmbedding F (Iio 0)
  rw [hn]
  simpa only [compl_Ioi, integral_Iic_eq_integral_Iio] using
    integral_add_compl (s := Ioi 0) measurableSet_Ioi hF

/-- The upper-half-plane symmetric sum is the full ordinary planar Gaussian pairing. -/
theorem integral_upper_gaussian_sum (P Q : Polynomial ℂ) :
    (∫ p in upperXY, gaussianWeightedXY P Q p.1 p.2 +
      gaussianWeightedXY Q P p.1 p.2) =
        ∫ p : ℝ × ℝ, gaussianWeightedXY P Q p.1 p.2 := by
  have hP := (integrable_gaussianWeightedXY P Q).integrableOn (s := upperXY)
  have hQ := (integrable_gaussianWeightedXY Q P).integrableOn (s := upperXY)
  have hfull : Integrable (fun p : ℝ × ℝ ↦ gaussianWeightedXY P Q p.1 p.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using integrable_gaussianWeightedXY P Q
  rw [integral_add hP hQ, integral_upper_eq_iterated hP, integral_upper_eq_iterated hQ,
    Measure.volume_eq_prod, integral_prod _ hfull,
    ← integral_add (integrable_prod_upper hP).integral_prod_left
      (integrable_prod_upper hQ).integral_prod_left]
  apply integral_congr_ae
  filter_upwards [hfull.prod_right_ae] with x hx
  simp_rw [gaussianWeightedXY_reflection P Q]
  exact integral_Ioi_add_reflection _ hx

/-- Cartesian and complex Gaussian pairing use exactly the same Euclidean volume. -/
theorem integral_gaussianWeightedXY_eq_complex (P Q : Polynomial ℂ) :
    (∫ p : ℝ × ℝ, gaussianWeightedXY P Q p.1 p.2) =
      ∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) * P.eval z * Q.eval (starRingEnd ℂ z) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun z : ℂ ↦ (Real.exp (-‖z‖ ^ 2) : ℂ) * P.eval z * Q.eval (starRingEnd ℂ z))
  convert h using 1
  congr 1
  funext p
  have hn : ‖point p.1 p.2‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [point, pow_two]
  dsimp only [gaussianWeightedXY, gaussianXY]
  change (Real.exp (-p.1 ^ 2 - p.2 ^ 2) : ℂ) *
    P.eval (point p.1 p.2) * Q.eval (point p.1 (-p.2)) =
      (Real.exp (-‖point p.1 p.2‖ ^ 2) : ℂ) *
        P.eval (point p.1 p.2) * Q.eval (point p.1 (-p.2))
  rw [hn, show -p.1 ^ 2 - p.2 ^ 2 = -(p.1 ^ 2 + p.2 ^ 2) by ring]

/-- The literal complex part of the tau-zero real Ginibre skew form. -/
def complexSkew (P Q : Polynomial ℂ) : ℂ :=
  (2 * Complex.I) * ∫ z in {z : ℂ | 0 < z.im}, (complexWeight z : ℂ) *
    (P.eval z * Q.eval (starRingEnd ℂ z) - Q.eval z * P.eval (starRingEnd ℂ z))

theorem complexSkew_eq_xy (P Q : Polynomial ℂ) :
    complexSkew P Q = (2 * Complex.I) * ∫ p in upperXY, skewMinus P Q p.1 p.2 := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).setIntegral_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun z : ℂ ↦ (complexWeight z : ℂ) *
      (P.eval z * Q.eval (starRingEnd ℂ z) - Q.eval z * P.eval (starRingEnd ℂ z)))
    {z : ℂ | 0 < z.im}
  have he : Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | 0 < z.im} = upperXY := by
    ext p
    simp [upperXY]
  rw [he] at h
  unfold complexSkew
  congr 1
  simpa only [Complex.measurableEquivRealProd_symm_apply, skewMinus, weightXY, point]
    using! h.symm

/-- Integrated complex cancellation with the exact real boundary term and planar constant. -/
theorem complexSkew_raising (P Q : Polynomial ℂ) :
    complexSkew P (raising Q) =
      -(2 * ∫ x : ℝ, (Real.exp (-x ^ 2) : ℂ) * P.eval (x : ℂ) * Q.eval (x : ℂ)) +
        (skewConstant : ℂ) * ∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) *
          P.eval z * Q.eval (starRingEnd ℂ z) := by
  rw [complexSkew_eq_xy, ← integral_const_mul]
  have heq : (fun p : ℝ × ℝ ↦ (2 * Complex.I) * skewMinus P (raising Q) p.1 p.2) =
      fun p ↦ -Complex.I * skewMinusDx P Q p.1 p.2 + skewPlusDy P Q p.1 p.2 +
        (skewConstant : ℂ) *
          (gaussianWeightedXY P Q p.1 p.2 + gaussianWeightedXY Q P p.1 p.2) := by
    funext p
    simpa only [skewMinus, gaussianWeightedXY, mul_assoc, mul_add] using
      complex_skew_derivative_identity P Q p.1 p.2
  have hD := integrableOn_skewMinusDx P Q
  have hY := integrableOn_skewPlusDy P Q
  have hG : IntegrableOn (fun p : ℝ × ℝ ↦
      gaussianWeightedXY P Q p.1 p.2 + gaussianWeightedXY Q P p.1 p.2) upperXY :=
    ((integrable_gaussianWeightedXY P Q).integrableOn (s := upperXY)).add
      ((integrable_gaussianWeightedXY Q P).integrableOn (s := upperXY))
  have hDY : IntegrableOn (fun p : ℝ × ℝ ↦
      -Complex.I * skewMinusDx P Q p.1 p.2 + skewPlusDy P Q p.1 p.2) upperXY :=
    (hD.const_mul (-Complex.I)).add hY
  rw [heq, integral_add hDY (hG.const_mul (skewConstant : ℂ)),
    integral_add (hD.const_mul (-Complex.I)) hY,
    integral_const_mul, integral_const_mul,
    integral_upper_skewMinusDx, integral_upper_skewPlusDy,
    integral_upper_gaussian_sum, integral_gaussianWeightedXY_eq_complex]
  ring

/-- The full source skew form is the sum of its literal real and complex parts. -/
def skewForm (P Q : Polynomial ℂ) : ℂ := realSkew P Q + complexSkew P Q

/-- The real and complex boundary terms cancel exactly in the full skew form. -/
theorem skewForm_raising (P Q : Polynomial ℂ) :
    skewForm P (raising Q) = (skewConstant : ℂ) *
      ∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) * P.eval z * Q.eval (starRingEnd ℂ z) := by
  rw [skewForm, realSkew_raising, complexSkew_raising]
  ring

end Paper.SkewOrthogonal
