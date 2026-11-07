/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.RealPairFlatten
@[expose] public section
noncomputable section
open MeasureTheory
namespace Paper.SkewOrthogonal

/-- Ordinary real coordinates with the unpaired real root FIRST. -/
def oddRealPairFlatten (r : ℕ) :
    (ℝ × (Fin r → ℝ × ℝ)) ≃ᵐ (Fin (2*r+1) → ℝ) :=
  ((MeasurableEquiv.refl ℝ).prodCongr (realPairFlatten r)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (2*r+1) ↦ ℝ) 0).symm

theorem oddRealPairFlatten_apply (r : ℕ) (p : ℝ × (Fin r → ℝ × ℝ)) :
    oddRealPairFlatten r p = Fin.cons p.1 (realPairFlatten r p.2) := by
  simp [oddRealPairFlatten,MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]
  exact ⟨rfl,rfl⟩

theorem volume_preserving_oddRealPairFlatten (r : ℕ) :
    MeasurePreserving (oddRealPairFlatten r) volume volume := by
  have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_realPairFlatten r)
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin (2*r+1) ↦ ℝ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (2*r+1) ↦ ℝ) 0)
  exact h2.comp h1

theorem integrable_oddRealPairFlatten_iff (r : ℕ) (F : (Fin (2*r+1) → ℝ) → ℂ) :
    Integrable (fun p : ℝ × (Fin r → ℝ × ℝ) ↦ F (Fin.cons p.1 (realPairFlatten r p.2))) ↔
      Integrable F := by
  simpa only [← oddRealPairFlatten_apply,Function.comp_def] using!
    (volume_preserving_oddRealPairFlatten r).integrable_comp_emb
      (oddRealPairFlatten r).measurableEmbedding

theorem integral_oddRealPairFlatten (r : ℕ) (F : (Fin (2*r+1) → ℝ) → ℂ) :
    (∫ p : ℝ × (Fin r → ℝ × ℝ), F (Fin.cons p.1 (realPairFlatten r p.2))) =
      ∫ u : Fin (2*r+1) → ℝ, F u := by
  simpa only [← oddRealPairFlatten_apply,Function.comp_def] using!
    (volume_preserving_oddRealPairFlatten r).integral_comp' F

theorem measurePreserving_oddRealPairFlatten_prod {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [SigmaFinite ν] (r : ℕ) :
    MeasurePreserving ((oddRealPairFlatten r).prodCongr (MeasurableEquiv.refl Z))
      ((volume : Measure (ℝ × (Fin r → ℝ × ℝ))).prod ν)
      ((volume : Measure (Fin (2*r+1) → ℝ)).prod ν) :=
  (volume_preserving_oddRealPairFlatten r).prod (MeasurePreserving.id ν)

theorem integral_oddRealPairFlatten_prod {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [SigmaFinite ν] (r : ℕ) (F : (Fin (2*r+1) → ℝ) × Z → ℂ) :
    (∫ p : (ℝ × (Fin r → ℝ × ℝ)) × Z,
      F (Fin.cons p.1.1 (realPairFlatten r p.1.2),p.2)
        ∂((volume : Measure (ℝ × (Fin r → ℝ × ℝ))).prod ν)) =
      ∫ p, F p ∂((volume : Measure (Fin (2*r+1) → ℝ)).prod ν) := by
  simpa only [← oddRealPairFlatten_apply,Function.comp_def] using!
    (measurePreserving_oddRealPairFlatten_prod ν r).integral_comp' F

end Paper.SkewOrthogonal
