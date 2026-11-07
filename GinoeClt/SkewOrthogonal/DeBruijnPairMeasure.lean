/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnPairFeatures
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal
namespace Paper.SkewOrthogonal

/-- Ordinary real-pair volume and ordinary upper-complex AREA, on a disjoint union. -/
def deBruijnPairMeasure : Measure ((ℝ × ℝ) ⊕ ℂ) :=
  (volume : Measure (ℝ × ℝ)).map Sum.inl +
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr

private theorem pairInl_embedding : MeasurableEmbedding (@Sum.inl (ℝ × ℝ) ℂ) :=
  ⟨Sum.inl_injective,measurable_inl,fun _ hs ↦ hs.inl_image⟩

private theorem pairInr_embedding : MeasurableEmbedding (@Sum.inr (ℝ × ℝ) ℂ) :=
  ⟨Sum.inr_injective,measurable_inr,fun _ hs ↦ hs.inr_image⟩

instance : SigmaFinite deBruijnPairMeasure := by
  have : SigmaFinite ((volume : Measure (ℝ × ℝ)).map (@Sum.inl (ℝ × ℝ) ℂ)) :=
    pairInl_embedding.sigmaFinite_map
  have : SigmaFinite (((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map
      (@Sum.inr (ℝ × ℝ) ℂ)) := pairInr_embedding.sigmaFinite_map
  unfold deBruijnPairMeasure
  infer_instance

/-- The actual real/complex features; neither individual column is presumed L1. -/
def deBruijnPairFeature {κ : Type*} (B : Set ℂ) (t : ℝ≥0) (P : κ → Polynomial ℂ) :
    ((ℝ × ℝ) ⊕ ℂ) → κ → Fin 2 → ℂ :=
  Sum.elim (realPairFeature P) (complexPairFeature B t P)

theorem integrable_deBruijnPairFeature_product {κ : Type*} (B : Set ℂ)
    (hB : MeasurableSet B) (t : ℝ≥0) (P : κ → Polynomial ℂ) (p q : κ) :
    Integrable (fun s ↦ deBruijnPairFeature B t P s p 0 * deBruijnPairFeature B t P s q 1)
      deBruijnPairMeasure := by
  unfold deBruijnPairMeasure
  apply integrable_add_measure.mpr
  constructor
  · apply pairInl_embedding.integrable_map_iff.mpr
    exact integrable_realPairFeature_product P p q
  · apply pairInr_embedding.integrable_map_iff.mpr
    exact integrable_complexPairFeature_product B hB t P p q

theorem integrable_deBruijnPairFeature_wedge {κ : Type*} (B : Set ℂ)
    (hB : MeasurableSet B) (t : ℝ≥0) (P : κ → Polynomial ℂ) (p q : κ) :
    Integrable (fun s ↦ deBruijnPairFeature B t P s p 0 * deBruijnPairFeature B t P s q 1 -
      deBruijnPairFeature B t P s p 1 * deBruijnPairFeature B t P s q 0) deBruijnPairMeasure := by
  exact (integrable_deBruijnPairFeature_product B hB t P p q).sub
    ((integrable_deBruijnPairFeature_product B hB t P q p).congr
      (Filter.Eventually.of_forall fun s ↦ mul_comm _ _))

/-- Integrated disjoint-pair entries are exactly the actual perturbed skew form. -/
theorem integral_deBruijnPairFeature_wedge {κ : Type*} (B : Set ℂ)
    (hB : MeasurableSet B) (hupper : B ⊆ {z : ℂ | 0 < z.im}) (t : ℝ≥0)
    (P : κ → Polynomial ℂ) (p q : κ) :
    (∫ s, deBruijnPairFeature B t P s p 0 * deBruijnPairFeature B t P s q 1 -
      deBruijnPairFeature B t P s p 1 * deBruijnPairFeature B t P s q 0 ∂deBruijnPairMeasure) =
      skewForm (P p) (P q) + (t : ℂ) *
        ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
          ((P p).eval z*(P q).eval (conj z) - (P q).eval z*(P p).eval (conj z)) := by
  have h := integrable_deBruijnPairFeature_wedge B hB t P p q
  unfold deBruijnPairMeasure at h ⊢
  rw [integral_add_measure h.left_of_add_measure h.right_of_add_measure,
    pairInl_embedding.integral_map,pairInr_embedding.integral_map]
  change (∫ xy : ℝ × ℝ, realPairFeature P xy p 0 * realPairFeature P xy q 1 -
      realPairFeature P xy p 1 * realPairFeature P xy q 0) +
    (∫ z in {z : ℂ | 0 < z.im},
      complexPairFeature B t P z p 0 * complexPairFeature B t P z q 1 -
        complexPairFeature B t P z p 1 * complexPairFeature B t P z q 0) = _
  rw [integral_realPairFeature_wedge,integral_complexPairFeature_wedge B hB hupper,skewForm]
  ring

/-- An actual perturbed skew-Gram Pfaffian as a genuine continuous determinant integral. -/
theorem integral_deBruijnPairFeature_determinant (B : Set ℂ) (hB : MeasurableSet B)
    (hupper : B ⊆ {z : ℂ | 0 < z.im}) (t : ℝ≥0) (m : ℕ)
    (P : PairedIndex m → Polynomial ℂ) :
    (∫ x : Fin m → ((ℝ × ℝ) ⊕ ℂ),
      (pairedFeatureMatrix (fun i ↦ deBruijnPairFeature B t P (x i))).det
        ∂Measure.pi (fun _ : Fin m ↦ deBruijnPairMeasure)) =
      (m.factorial : ℂ) * pfaffian (fun p q ↦ skewForm (P p) (P q) + (t : ℂ) *
        ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
          ((P p).eval z*(P q).eval (conj z) - (P q).eval z*(P p).eval (conj z))) := by
  have h := integral_pairedFeatureMatrix deBruijnPairMeasure (deBruijnPairFeature B t P)
    (integrable_deBruijnPairFeature_product B hB t P)
  have hg : (fun p q ↦ ∫ s, rankTwoEntry (deBruijnPairFeature B t P) s p q ∂deBruijnPairMeasure) =
      (Matrix.of (fun p q ↦ skewForm (P p) (P q) + (t : ℂ) *
        ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
          ((P p).eval z*(P q).eval (conj z) - (P q).eval z*(P p).eval (conj z)))) := by
    funext p q
    exact integral_deBruijnPairFeature_wedge B hB hupper t P p q
  exact h.trans (congrArg (fun M : Matrix (PairedIndex m) (PairedIndex m) ℂ ↦
    (m.factorial : ℂ)*pfaffian M) hg)

end Paper.SkewOrthogonal
