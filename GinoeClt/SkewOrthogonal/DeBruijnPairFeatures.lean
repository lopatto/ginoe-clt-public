/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.ContinuousWedgeDeterminant
public import GinoeClt.SkewOrthogonal.MixedDeterminantIntegrability
public import GinoeClt.SkewOrthogonal.Algebra
@[expose] public section
noncomputable section
open MeasureTheory Classical
open scoped ComplexConjugate NNReal
namespace Paper.SkewOrthogonal

/-- A real pair carries half the signed Gaussian weight in its first column. -/
def realPairFeature {κ : Type*} (P : κ → Polynomial ℂ) (xy : ℝ × ℝ)
    (p : κ) (side : Fin 2) : ℂ :=
  if side = 0 then (1/2 : ℂ) * (SignType.sign (xy.2-xy.1) : ℂ) *
    realGaussianPolynomial (P p) xy.1 else realGaussianPolynomial (P p) xy.2

theorem realPairFeature_product {κ : Type*} (P : κ → Polynomial ℂ)
    (p q : κ) (xy : ℝ × ℝ) :
    realPairFeature P xy p 0 * realPairFeature P xy q 1 =
      (1/2 : ℂ) * ((SignType.sign (xy.2-xy.1) : ℂ) *
        ((Real.exp (-(xy.1^2+xy.2^2)/2) : ℂ) *
          (P p).eval (xy.1 : ℂ) * (P q).eval (xy.2 : ℂ))) := by
  have he : Real.exp (-xy.1^2/2) * Real.exp (-xy.2^2/2) =
      Real.exp (-(xy.1^2+xy.2^2)/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [realPairFeature,
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),↓reduceIte,realGaussianPolynomial]
  rw [← he,Complex.ofReal_mul]
  ring

theorem integrable_realPairFeature_product {κ : Type*} (P : κ → Polynomial ℂ)
    (p q : κ) :
    Integrable (fun xy : ℝ × ℝ ↦ realPairFeature P xy p 0 * realPairFeature P xy q 1) := by
  simpa only [realPairFeature_product] using
    (integrable_real_skew_polynomials (P p) (P q)).const_mul (1/2 : ℂ)

theorem integral_realPairFeature_product {κ : Type*} (P : κ → Polynomial ℂ)
    (p q : κ) :
    (∫ xy : ℝ × ℝ, realPairFeature P xy p 0 * realPairFeature P xy q 1) =
      (1/2 : ℂ)*realSkew (P p) (P q) := by
  simp_rw [realPairFeature_product]
  rw [integral_const_mul,← realSkew_eq_integral_prod]

theorem integral_realPairFeature_wedge {κ : Type*} (P : κ → Polynomial ℂ)
    (p q : κ) :
    (∫ xy : ℝ × ℝ, realPairFeature P xy p 0 * realPairFeature P xy q 1 -
      realPairFeature P xy p 1 * realPairFeature P xy q 0) = realSkew (P p) (P q) := by
  have hq := (integrable_realPairFeature_product P q p).congr
    (Filter.Eventually.of_forall fun xy ↦ mul_comm _ _)
  rw [integral_sub (integrable_realPairFeature_product P p q) hq,
    integral_realPairFeature_product]
  have he : (fun xy : ℝ × ℝ ↦ realPairFeature P xy p 1 * realPairFeature P xy q 0) =
      (fun xy ↦ realPairFeature P xy q 0 * realPairFeature P xy p 1) := by
    funext xy
    ring
  rw [he,integral_realPairFeature_product,realSkew_antisymm]
  ring

/-- A complex pair carries exactly 2i times the actual W/count factor once. -/
def complexPairFeature {κ : Type*} (B : Set ℂ) (t : ℝ≥0) (P : κ → Polynomial ℂ)
    (z : ℂ) (p : κ) (side : Fin 2) : ℂ :=
  if side = 0 then (2*Complex.I) * (complexWeight z : ℂ) *
    (if z ∈ B then 1+(t : ℂ) else 1) * (P p).eval z else (P p).eval (conj z)

theorem complexPairFeature_product {κ : Type*} (B : Set ℂ) (t : ℝ≥0)
    (P : κ → Polynomial ℂ) (p q : κ) (z : ℂ) :
    complexPairFeature B t P z p 0 * complexPairFeature B t P z q 1 =
      (2*Complex.I)*complexCountPolynomial B t (P p) (P q) z := by
  simp only [complexPairFeature,
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),↓reduceIte,complexCountPolynomial]
  ring

theorem integrable_complexPairFeature_product {κ : Type*} (B : Set ℂ)
    (hB : MeasurableSet B) (t : ℝ≥0) (P : κ → Polynomial ℂ) (p q : κ) :
    Integrable (fun z : ℂ ↦ complexPairFeature B t P z p 0 * complexPairFeature B t P z q 1)
      (volume.restrict {z : ℂ | 0 < z.im}) := by
  simpa only [complexPairFeature_product] using
    (integrable_complexCountPolynomial B hB t (P p) (P q)).const_mul (2*Complex.I)

/-- The weighted complex wedge is the original skew form plus the actual count update. -/
theorem integral_complexPairFeature_wedge {κ : Type*} (B : Set ℂ) (hB : MeasurableSet B)
    (hupper : B ⊆ {z : ℂ | 0 < z.im}) (t : ℝ≥0) (P : κ → Polynomial ℂ) (p q : κ) :
    (∫ z in {z : ℂ | 0 < z.im},
      complexPairFeature B t P z p 0 * complexPairFeature B t P z q 1 -
        complexPairFeature B t P z p 1 * complexPairFeature B t P z q 0) =
      complexSkew (P p) (P q) + (t : ℂ) *
        ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
          ((P p).eval z * (P q).eval (conj z) - (P q).eval z * (P p).eval (conj z)) := by
  let F : ℂ → ℂ := fun z ↦ (2*Complex.I)*(complexWeight z : ℂ) *
    ((P p).eval z * (P q).eval (conj z) - (P q).eval z * (P p).eval (conj z))
  have hF : Integrable F (volume.restrict {z : ℂ | 0 < z.im}) := by
    apply ((integrableOn_complexSkew_integrand (P p) (P q)).const_mul (2*Complex.I)).congr
    filter_upwards [] with z
    dsimp only [F]
    ring
  have hw (z : ℂ) :
      complexPairFeature B t P z p 0 * complexPairFeature B t P z q 1 -
        complexPairFeature B t P z p 1 * complexPairFeature B t P z q 0 =
        F z + (t : ℂ) * B.indicator F z := by
    by_cases hz : z ∈ B <;>
      simp [complexPairFeature,F,hz,Set.indicator_of_mem,Set.indicator_of_notMem] <;> ring
  simp_rw [hw]
  rw [integral_add hF ((hF.indicator hB).const_mul (t : ℂ)),integral_const_mul,
    integral_indicator hB]
  have hr : (volume.restrict {z : ℂ | 0 < z.im}).restrict B = (volume : Measure ℂ).restrict B := by
    rw [Measure.restrict_restrict hB,Set.inter_eq_left.mpr hupper]
  rw [hr]
  have hb : (∫ z in {z : ℂ | 0 < z.im}, F z) = complexSkew (P p) (P q) := by
    rw [complexSkew,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp only [F]
    ring
  rw [hb]

end Paper.SkewOrthogonal
