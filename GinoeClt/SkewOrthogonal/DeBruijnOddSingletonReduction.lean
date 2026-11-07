/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.RawOddBorderSpecialization
public import GinoeClt.SkewOrthogonal.PairDeterminantSymmetry
public import GinoeClt.MeasureTheory.SymmetricMixedSectors
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
open Equiv Set MeasureTheory
open scoped BigOperators ComplexConjugate NNReal
namespace Paper.SkewOrthogonal
local notation "Y" => ((ℝ × ℝ) ⊕ ℂ)
local notation "W" => (Y ⊕ ℝ)
local notation "μpair" => Measure.map (@Sum.inl Y ℝ) deBruijnPairMeasure
local notation "μsng" => Measure.map (@Sum.inr Y ℝ) (volume : Measure ℝ)

private theorem singletonPair_embedding : MeasurableEmbedding (@Sum.inl Y ℝ) :=
  ⟨Sum.inl_injective,measurable_inl,fun _s hs => hs.inl_image⟩
private theorem singletonReal_embedding : MeasurableEmbedding (@Sum.inr Y ℝ) :=
  ⟨Sum.inr_injective,measurable_inr,fun _s hs => hs.inr_image⟩
private instance : SigmaFinite μpair := singletonPair_embedding.sigmaFinite_map
private instance : SigmaFinite μsng := singletonReal_embedding.sigmaFinite_map

/-- The ACTUAL raw odd adjacent-pair determinant, without a conditional law or surrogate. -/
def rawOddSourceDeterminant (B : Set ℂ) (t : ℝ≥0) (m : ℕ) (y : Fin (m+1) → W) : ℂ :=
  (pairedFeatureMatrix (fun i => deBruijnBorderFeature B t (rawOddPolynomial m)
    (Fin.last m,1) (y i))).det

theorem integrable_rawOddSourceDeterminant (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (m : ℕ) :
    Integrable (rawOddSourceDeterminant B t m)
      (Measure.pi (fun _ : Fin (m+1) => deBruijnBorderMeasure)) :=
  integrable_pairedFeatureMatrix deBruijnBorderMeasure
    (deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1))
    (integrable_deBruijnBorderFeature_product B hB t (rawOddPolynomial m) (Fin.last m,1))

theorem rawOddSourceDeterminant_perm (B : Set ℂ) (t : ℝ≥0) (m : ℕ)
    (σ : Perm (Fin (m+1))) (y : Fin (m+1) → W) :
    rawOddSourceDeterminant B t m (y ∘ σ) = rawOddSourceDeterminant B t m y :=
  pairedFeatureMatrix_det_perm
    (deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)) y σ

/-- Actual range support of EACH selected coordinate, lifted simultaneously to
finite product measure. Non-singleton sectors therefore vanish genuinely AE. -/
theorem rawOddSourceDeterminant_selected_ae_zero (B : Set ℂ) (t : ℝ≥0) (m : ℕ)
    (S : Finset (Fin (m+1))) (hS : S.card ≠ 1) :
    ∀ᵐ y ∂Measure.pi (fun i : Fin (m+1) => if i ∈ S then μsng else μpair),
      rawOddSourceDeterminant B t m y = 0 := by
  classical
  let ρ : Fin (m+1) → Measure W := fun i => if i ∈ S then μsng else μpair
  have : ∀ i, SigmaFinite (ρ i) := fun i => by dsimp only [ρ]; split <;> infer_instance
  have hcoord (i : Fin (m+1)) : ∀ᵐ a ∂ρ i,
      if i ∈ S then (∃ x : ℝ, a = Sum.inr x) else (∃ s : Y, a = Sum.inl s) := by
    by_cases hi : i ∈ S
    · simp only [ρ,hi,ite_true]
      filter_upwards [ae_map_mem_range singletonReal_embedding.measurableSet_range
        singletonReal_embedding.measurable.aemeasurable] with a ha
      obtain ⟨x,hx⟩ := ha
      exact ⟨x,hx.symm⟩
    · simp only [ρ,hi,ite_false]
      filter_upwards [ae_map_mem_range singletonPair_embedding.measurableSet_range
        singletonPair_embedding.measurable.aemeasurable] with a ha
      obtain ⟨s,hs⟩ := ha
      exact ⟨s,hs.symm⟩
  have hAE : ∀ᵐ y ∂Measure.pi ρ, ∀ i : Fin (m+1),
      if i ∈ S then (∃ x : ℝ, y i = Sum.inr x) else (∃ s : Y, y i = Sum.inl s) :=
    Filter.eventually_all.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := ρ) (i := i)).eventually (hcoord i)
  filter_upwards [hAE] with y hy
  by_cases h0 : S.card = 0
  · have he : S = ∅ := Finset.card_eq_zero.mp h0
    apply det_deBruijnBorderFeature_no_single B t m y
    intro i
    simpa [he] using hy i
  · have hlarge : 1 < S.card := by omega
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hlarge
    obtain ⟨x,hx⟩ := (show ∃ x : ℝ, y i = Sum.inr x from by simpa only [hi,ite_true] using hy i)
    obtain ⟨z,hz⟩ := (show ∃ z : ℝ, y j = Sum.inr z from by simpa only [hj,ite_true] using hy j)
    exact det_deBruijnBorderFeature_two_singles B t m (rawOddPolynomial m)
      (Fin.last m,1) y i j hij x z hx hz

/-- Native first-coordinate decomposition plus the literal Sum injections. -/
theorem measurePreserving_firstBorderCons (m : ℕ) :
    MeasurePreserving (fun p : ℝ × (Fin m → Y) =>
      Fin.cons (α := fun _ => W) (Sum.inr p.1) (fun j => Sum.inl (p.2 j)))
      ((volume : Measure ℝ).prod (Measure.pi (fun _ : Fin m => deBruijnPairMeasure)))
      (Measure.pi (fun i : Fin (m+1) => if i ∈ ({0} : Finset (Fin (m+1))) then μsng else μpair)) := by
  let ρ : Fin (m+1) → Measure W := fun i => if i ∈ ({0} : Finset (Fin (m+1))) then μsng else μpair
  have : ∀ i, SigmaFinite (ρ i) := fun i => by dsimp only [ρ]; split <;> infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => W) 0
  have hn := (measurePreserving_piFinSuccAbove ρ (0 : Fin (m+1))).symm e
  have hn' : MeasurePreserving e.symm
      ((μsng).prod (Measure.pi (fun _ : Fin m => μpair))) (Measure.pi ρ) := by
    simpa [ρ,Fin.zero_succAbove] using hn
  have h1 : MeasurePreserving (@Sum.inr Y ℝ) (volume : Measure ℝ) μsng :=
    ⟨measurable_inr,rfl⟩
  have h2 : MeasurePreserving (@Sum.inl Y ℝ) deBruijnPairMeasure μpair :=
    ⟨measurable_inl,rfl⟩
  have hp := h1.prod (measurePreserving_pi (fun _ : Fin m => deBruijnPairMeasure)
    (fun _ : Fin m => μpair) (fun _ => h2))
  have he : e.symm ∘ Prod.map Sum.inr (fun s : Fin m → Y => fun i => Sum.inl (s i)) =
      (fun p : ℝ × (Fin m → Y) => Fin.cons (α := fun _ => W) (Sum.inr p.1) (fun i => Sum.inl (p.2 i))) := by
    funext p
    change Fin.insertNth (α := fun _ => W) (0 : Fin (m+1)) (Sum.inr p.1) (fun i => Sum.inl (p.2 i)) = _
    exact Fin.insertNth_zero' _ _
  simpa only [he] using hn'.comp hp

/-- The actual FIRST-single sector equals an ordinary real integral followed by
m original pair atoms. Its genuine product L1 is proved BEFORE Fubini. -/
theorem integral_firstBorderSector (m : ℕ) (F : (Fin (m+1) → W) → ℂ)
    (hF : Integrable F (Measure.pi (fun i : Fin (m+1) =>
      if i ∈ ({0} : Finset (Fin (m+1))) then μsng else μpair))) :
    (∫ y, F y ∂Measure.pi (fun i : Fin (m+1) =>
      if i ∈ ({0} : Finset (Fin (m+1))) then μsng else μpair)) =
      ∫ x : ℝ, ∫ s : Fin m → Y,
        F (Fin.cons (α := fun _ => W) (Sum.inr x) (fun i => Sum.inl (s i)))
          ∂Measure.pi (fun _ : Fin m => deBruijnPairMeasure) := by
  have hm := measurePreserving_firstBorderCons m
  have hL1 := hm.integrable_comp_of_integrable hF
  have hFM : AEStronglyMeasurable F
      (((volume : Measure ℝ).prod (Measure.pi (fun _ : Fin m => deBruijnPairMeasure))).map
        (fun p : ℝ × (Fin m → Y) => Fin.cons (α := fun _ => W) (Sum.inr p.1) (fun i => Sum.inl (p.2 i)))) := by
    rw [hm.map_eq]
    exact hF.aestronglyMeasurable
  calc
    _ = ∫ p : ℝ × (Fin m → Y), F (Fin.cons (α := fun _ => W) (Sum.inr p.1) (fun i => Sum.inl (p.2 i)))
        ∂((volume : Measure ℝ).prod (Measure.pi (fun _ : Fin m => deBruijnPairMeasure))) := by
      rw [← hm.map_eq]
      exact integral_map hm.measurable.aemeasurable hFM
    _ = _ := integral_prod _ hL1

/-- Complete singleton reduction of the ACTUAL odd source determinant. All sectors
other than cardinality one vanish; the surviving m+1 copies are genuinely identical.
This is a determinant integral identity, not an ensemble or generating-function law. -/
theorem integral_rawOddSourceDeterminant_singleton_reduction (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (m : ℕ) :
    (∫ y : Fin (m+1) → W, rawOddSourceDeterminant B t m y
      ∂Measure.pi (fun _ : Fin (m+1) => deBruijnBorderMeasure)) =
      (m+1 : ℂ) * ∫ x : ℝ, ∫ s : Fin m → Y,
        rawOddSourceDeterminant B t m (Fin.cons (α := fun _ => W) (Sum.inr x) (fun i => Sum.inl (s i)))
          ∂Measure.pi (fun _ : Fin m => deBruijnPairMeasure) := by
  classical
  let F := rawOddSourceDeterminant B t m
  let I (S : Finset (Fin (m+1))) := ∫ y, F y
    ∂Measure.pi (fun i : Fin (m+1) => if i ∈ S then μsng else μpair)
  have hWhole : Integrable F (Measure.pi (fun _ : Fin (m+1) => μpair+μsng)) := by
    simpa only [deBruijnBorderMeasure] using integrable_rawOddSourceDeterminant B hB t m
  have hSel (S : Finset (Fin (m+1))) := (integrable_pi_add_iff μpair μsng F).mp hWhole S
  have hSym : ∀ (σ : Perm (Fin (m+1))) y, F (y ∘ σ) = F y := rawOddSourceDeterminant_perm B t m
  have hI (S : Finset (Fin (m+1))) : I S = if S.card = 1 then I {0} else 0 := by
    by_cases hS : S.card = 1
    · rw [ite_eq_left hS]
      exact integral_selected_eq_of_card_eq μpair μsng F hSym S {0} (by simpa using hS)
    · rw [ite_eq_right hS]
      exact integral_eq_zero_of_ae (rawOddSourceDeterminant_selected_ae_zero B t m S hS)
  have hFilter : Finset.univ.filter (fun S : Finset (Fin (m+1)) => S.card = 1) =
      (Finset.univ : Finset (Fin (m+1))).powersetCard 1 := by
    ext S
    simp
  calc
    _ = ∑ S : Finset (Fin (m+1)), I S := by
      change (∫ y, F y ∂Measure.pi (fun _ : Fin (m+1) => μpair+μsng)) = _
      exact integral_pi_add_eq_sum_selected μpair μsng F hWhole
    _ = ((Finset.univ.filter (fun S : Finset (Fin (m+1)) => S.card = 1)).card : ℂ) * I {0} := by
      calc
        _ = ∑ S : Finset (Fin (m+1)), if S.card = 1 then I {0} else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hI S
        _ = _ := by
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const,nsmul_eq_mul]
    _ = (m+1 : ℂ) * I {0} := by
      rw [hFilter,Finset.card_powersetCard]
      simp
    _ = _ := by
      rw [show I {0} = ∫ x : ℝ, ∫ s : Fin m → Y,
        F (Fin.cons (α := fun _ => W) (Sum.inr x) (fun i => Sum.inl (s i)))
          ∂Measure.pi (fun _ : Fin m => deBruijnPairMeasure) from integral_firstBorderSector m F (hSel {0})]

end Paper.SkewOrthogonal
