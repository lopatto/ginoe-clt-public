/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnPairMeasure
public import GinoeClt.SkewOrthogonal.Border
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ComplexConjugate NNReal
namespace Paper.SkewOrthogonal

/-- A single real atom has its actual Gaussian polynomial column, followed by
ONE fixed border column. The first polynomial family is otherwise arbitrary. -/
def singleBorderFeature {κ : Type*} [DecidableEq κ] (P : κ → Polynomial ℂ) (b : κ)
    (x : ℝ) (p : κ) (side : Fin 2) : ℂ :=
  if side = 0 then realGaussianPolynomial (P p) x else if p = b then 1 else 0

theorem integrable_singleBorderFeature_product {κ : Type*} [DecidableEq κ]
    (P : κ → Polynomial ℂ) (b p q : κ) :
    Integrable (fun x : ℝ => singleBorderFeature P b x p 0 * singleBorderFeature P b x q 1) := by
  simpa only [singleBorderFeature,show (1 : Fin 2) ≠ 0 by decide,↓reduceIte] using
    (integrable_realGaussianPolynomial (P p)).mul_const (if q = b then (1 : ℂ) else 0)

theorem integrable_singleBorderFeature_wedge {κ : Type*} [DecidableEq κ]
    (P : κ → Polynomial ℂ) (b p q : κ) :
    Integrable (fun x : ℝ => singleBorderFeature P b x p 0 * singleBorderFeature P b x q 1 -
      singleBorderFeature P b x p 1 * singleBorderFeature P b x q 0) := by
  exact (integrable_singleBorderFeature_product P b p q).sub
    ((integrable_singleBorderFeature_product P b q p).congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _))

/-- The exact border sign convention: +νp in column b and -νq in row b. -/
theorem integral_singleBorderFeature_wedge {κ : Type*} [DecidableEq κ]
    (P : κ → Polynomial ℂ) (b p q : κ) :
    (∫ x : ℝ, singleBorderFeature P b x p 0 * singleBorderFeature P b x q 1 -
      singleBorderFeature P b x p 1 * singleBorderFeature P b x q 0) =
      realBorder (P p) * (if q = b then (1 : ℂ) else 0) -
        (if p = b then (1 : ℂ) else 0) * realBorder (P q) := by
  have h1 := integrable_singleBorderFeature_product P b p q
  have h2 := (integrable_singleBorderFeature_product P b q p).congr
    (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [integral_sub h1 h2]
  simp only [singleBorderFeature,show (1 : Fin 2) ≠ 0 by decide,↓reduceIte,integral_mul_const,integral_const_mul,realBorder]

/-- The literal border second column is independent of the sampled real atom. -/
@[simp] theorem singleBorderFeature_second {κ : Type*} [DecidableEq κ]
    (P : κ → Polynomial ℂ) (b : κ) (x : ℝ) (p : κ) :
    singleBorderFeature P b x p 1 = if p = b then (1 : ℂ) else 0 := by
  simp [singleBorderFeature]

theorem singleBorderFeature_second_eq {κ : Type*} [DecidableEq κ]
    (P : κ → Polynomial ℂ) (b : κ) (x y : ℝ) :
    (fun p => singleBorderFeature P b x p 1) = (fun p => singleBorderFeature P b y p 1) := by
  funext p
  rw [singleBorderFeature_second,singleBorderFeature_second]

/-- If the polynomial at b is zero, the ordinary pair source has a genuine zero
border row at BOTH columns. No radical assumption is used. -/
theorem deBruijnPairFeature_border_zero {κ : Type*} (B : Set ℂ) (t : ℝ≥0)
    (P : κ → Polynomial ℂ) (b : κ) (hb : P b = 0) (s : (ℝ × ℝ) ⊕ ℂ) (a : Fin 2) :
    deBruijnPairFeature B t P s b a = 0 := by
  cases s <;> fin_cases a <;>
    simp [deBruijnPairFeature,realPairFeature,complexPairFeature,realGaussianPolynomial,hb]

/-- Full source for the odd construction: original pair atoms OR one real singleton. -/
def deBruijnBorderMeasure : Measure (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ) :=
  deBruijnPairMeasure.map Sum.inl + (volume : Measure ℝ).map Sum.inr

private theorem borderInl_embedding : MeasurableEmbedding (@Sum.inl ((ℝ × ℝ) ⊕ ℂ) ℝ) :=
  ⟨Sum.inl_injective,measurable_inl,fun _s hs => hs.inl_image⟩
private theorem borderInr_embedding : MeasurableEmbedding (@Sum.inr ((ℝ × ℝ) ⊕ ℂ) ℝ) :=
  ⟨Sum.inr_injective,measurable_inr,fun _s hs => hs.inr_image⟩

instance : SigmaFinite deBruijnBorderMeasure := by
  have : SigmaFinite (deBruijnPairMeasure.map (@Sum.inl ((ℝ × ℝ) ⊕ ℂ) ℝ)) :=
    borderInl_embedding.sigmaFinite_map
  have : SigmaFinite ((volume : Measure ℝ).map (@Sum.inr ((ℝ × ℝ) ⊕ ℂ) ℝ)) :=
    borderInr_embedding.sigmaFinite_map
  unfold deBruijnBorderMeasure
  infer_instance

/-- Complete original-pair/single-border feature, with NO altered polynomial. -/
def deBruijnBorderFeature {κ : Type*} [DecidableEq κ] (B : Set ℂ) (t : ℝ≥0)
    (P : κ → Polynomial ℂ) (b : κ) : (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ) → κ → Fin 2 → ℂ :=
  Sum.elim (deBruijnPairFeature B t P) (singleBorderFeature P b)

theorem integrable_deBruijnBorderFeature_product {κ : Type*} [DecidableEq κ]
    (B : Set ℂ) (hB : MeasurableSet B) (t : ℝ≥0) (P : κ → Polynomial ℂ) (b p q : κ) :
    Integrable (fun s => deBruijnBorderFeature B t P b s p 0 *
      deBruijnBorderFeature B t P b s q 1) deBruijnBorderMeasure := by
  unfold deBruijnBorderMeasure
  apply integrable_add_measure.mpr
  constructor
  · apply borderInl_embedding.integrable_map_iff.mpr
    exact integrable_deBruijnPairFeature_product B hB t P p q
  · apply borderInr_embedding.integrable_map_iff.mpr
    exact integrable_singleBorderFeature_product P b p q

theorem integrable_deBruijnBorderFeature_wedge {κ : Type*} [DecidableEq κ]
    (B : Set ℂ) (hB : MeasurableSet B) (t : ℝ≥0) (P : κ → Polynomial ℂ) (b p q : κ) :
    Integrable (fun s => deBruijnBorderFeature B t P b s p 0 *
      deBruijnBorderFeature B t P b s q 1 - deBruijnBorderFeature B t P b s p 1 *
        deBruijnBorderFeature B t P b s q 0) deBruijnBorderMeasure := by
  exact (integrable_deBruijnBorderFeature_product B hB t P b p q).sub
    ((integrable_deBruijnBorderFeature_product B hB t P b q p).congr
      (Filter.Eventually.of_forall fun s => mul_comm _ _))

/-- The actual integrated Gram entry: original perturbed skew form PLUS the
single border. Correct applicability to a raw odd family is a separate substitution. -/
theorem integral_deBruijnBorderFeature_wedge {κ : Type*} [DecidableEq κ]
    (B : Set ℂ) (hB : MeasurableSet B) (hupper : B ⊆ {z : ℂ | 0 < z.im}) (t : ℝ≥0)
    (P : κ → Polynomial ℂ) (b p q : κ) :
    (∫ s, deBruijnBorderFeature B t P b s p 0 * deBruijnBorderFeature B t P b s q 1 -
      deBruijnBorderFeature B t P b s p 1 * deBruijnBorderFeature B t P b s q 0
        ∂deBruijnBorderMeasure) =
      skewForm (P p) (P q) + (t : ℂ) *
        (∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
          ((P p).eval z*(P q).eval (conj z) - (P q).eval z*(P p).eval (conj z))) +
      realBorder (P p) * (if q = b then (1 : ℂ) else 0) -
        (if p = b then (1 : ℂ) else 0) * realBorder (P q) := by
  have h := integrable_deBruijnBorderFeature_wedge B hB t P b p q
  unfold deBruijnBorderMeasure at h ⊢
  rw [integral_add_measure h.left_of_add_measure h.right_of_add_measure,
    borderInl_embedding.integral_map,borderInr_embedding.integral_map]
  change (∫ s, deBruijnPairFeature B t P s p 0 * deBruijnPairFeature B t P s q 1 -
      deBruijnPairFeature B t P s p 1 * deBruijnPairFeature B t P s q 0 ∂deBruijnPairMeasure) +
    (∫ x : ℝ, singleBorderFeature P b x p 0 * singleBorderFeature P b x q 1 -
      singleBorderFeature P b x p 1 * singleBorderFeature P b x q 0) = _
  rw [integral_deBruijnPairFeature_wedge B hB hupper t P p q,
    integral_singleBorderFeature_wedge P b p q]
  ring

/-- Repeated singleton atoms have IDENTICAL border columns, not just proportional ones. -/
theorem deBruijnBorderFeature_single_second_eq {κ : Type*} [DecidableEq κ]
    (B : Set ℂ) (t : ℝ≥0) (P : κ → Polynomial ℂ) (b : κ) (x y : ℝ) :
    (fun p => deBruijnBorderFeature B t P b (Sum.inr x) p 1) =
      (fun p => deBruijnBorderFeature B t P b (Sum.inr y) p 1) :=
  singleBorderFeature_second_eq P b x y

theorem deBruijnBorderFeature_pair_border_zero {κ : Type*} [DecidableEq κ]
    (B : Set ℂ) (t : ℝ≥0) (P : κ → Polynomial ℂ) (b : κ) (hb : P b = 0)
    (s : (ℝ × ℝ) ⊕ ℂ) (a : Fin 2) :
    deBruijnBorderFeature B t P b (Sum.inl s) b a = 0 :=
  deBruijnPairFeature_border_zero B t P b hb s a

end Paper.SkewOrthogonal
