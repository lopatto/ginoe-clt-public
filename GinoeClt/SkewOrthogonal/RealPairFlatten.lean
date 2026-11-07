/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Algebra.PfaffianMinorCoordinates
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace Paper.SkewOrthogonal

/-- Grouped first/second coordinate labels, sent to the ACTUAL interlaced positions. -/
def realPairColumnIndex (r : ℕ) : Fin r ⊕ Fin r ≃ Fin (2*r) :=
  ({ toFun := Sum.elim (fun j => (j,0)) (fun j => (j,1))
     invFun := fun p : Fin r × Fin 2 => if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
     left_inv := by rintro (j | j) <;> rfl
     right_inv := by rintro ⟨j,a⟩; fin_cases a <;> rfl } :
      Fin r ⊕ Fin r ≃ Fin r × Fin 2).trans (PfaffianMinor.pairColumnEquiv r)

@[simp] theorem realPairColumnIndex_inl (r : ℕ) (j : Fin r) :
    realPairColumnIndex r (Sum.inl j) = PfaffianMinor.pairColumnEquiv r (j,0) := rfl

@[simp] theorem realPairColumnIndex_inr (r : ℕ) (j : Fin r) :
    realPairColumnIndex r (Sum.inr j) = PfaffianMinor.pairColumnEquiv r (j,1) := rfl

/-- Three native measurable equivalences: split each pair, join the two finite
arrays, and permute their literal cell labels into interlaced order. -/
def realPairFlatten (r : ℕ) : (Fin r → ℝ × ℝ) ≃ᵐ (Fin (2*r) → ℝ) :=
  ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin r)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin r => ℝ)).symm).trans
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2*r) => ℝ) (realPairColumnIndex r))

/-- The exact first coordinate of EVERY physical pair. -/
theorem realPairFlatten_apply_zero (r : ℕ) (xy : Fin r → ℝ × ℝ) (j : Fin r) :
    realPairFlatten r xy (PfaffianMinor.pairColumnEquiv r (j,0)) = (xy j).1 := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (realPairColumnIndex r)
    (β := fun _ : Fin (2*r) => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin r => ℝ)).symm
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin r)) xy)) (Sum.inl j)
  exact h

/-- The exact second coordinate of EVERY physical pair. -/
theorem realPairFlatten_apply_one (r : ℕ) (xy : Fin r → ℝ × ℝ) (j : Fin r) :
    realPairFlatten r xy (PfaffianMinor.pairColumnEquiv r (j,1)) = (xy j).2 := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (realPairColumnIndex r)
    (β := fun _ : Fin (2*r) => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin r => ℝ)).symm
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin r)) xy)) (Sum.inr j)
  exact h

/-- The inverse reconstructs the ACTUAL real pair from its interlaced coordinates. -/
theorem realPairFlatten_symm_apply (r : ℕ) (u : Fin (2*r) → ℝ) (j : Fin r) :
    (realPairFlatten r).symm u j =
      (u (PfaffianMinor.pairColumnEquiv r (j,0)),u (PfaffianMinor.pairColumnEquiv r (j,1))) := by
  apply Prod.ext
  · have h := realPairFlatten_apply_zero r ((realPairFlatten r).symm u) j
    simpa only [MeasurableEquiv.apply_symm_apply] using h.symm
  · have h := realPairFlatten_apply_one r ((realPairFlatten r).symm u) j
    simpa only [MeasurableEquiv.apply_symm_apply] using h.symm

/-- Ordinary Π Lebesgue volume, EXACTLY preserved with scalar one, also r=0. -/
theorem volume_preserving_realPairFlatten (r : ℕ) :
    MeasurePreserving (realPairFlatten r) volume volume := by
  have h1 := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin r)
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin r ⊕ Fin r => ℝ)
  have h3 := volume_measurePreserving_piCongrLeft (fun _ : Fin (2*r) => ℝ) (realPairColumnIndex r)
  exact h3.comp (h2.comp h1)

/-- Genuine L1 equivalence under the measurable bijection, no extra hypothesis on F. -/
theorem integrable_realPairFlatten_iff (r : ℕ) (F : (Fin (2*r) → ℝ) → ℂ) :
    Integrable (fun xy => F (realPairFlatten r xy)) ↔ Integrable F :=
  (volume_preserving_realPairFlatten r).integrable_comp_emb (realPairFlatten r).measurableEmbedding

/-- Unconditional totalized Bochner equality under the true measure-preserving bijection. -/
theorem integral_realPairFlatten (r : ℕ) (F : (Fin (2*r) → ℝ) → ℂ) :
    (∫ xy : Fin r → ℝ × ℝ, F (realPairFlatten r xy)) = ∫ u : Fin (2*r) → ℝ, F u :=
  (volume_preserving_realPairFlatten r).integral_comp' F

/-- Carry an independent upper-complex coordinate vector, or any other measure,
along unchanged. The first factor is ordinary real volume on both sides. -/
theorem measurePreserving_realPairFlatten_prod {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [SigmaFinite ν] (r : ℕ) :
    MeasurePreserving ((realPairFlatten r).prodCongr (MeasurableEquiv.refl Z))
      ((volume : Measure (Fin r → ℝ × ℝ)).prod ν)
      ((volume : Measure (Fin (2*r) → ℝ)).prod ν) :=
  (volume_preserving_realPairFlatten r).prod (MeasurePreserving.id ν)

theorem integrable_realPairFlatten_prod_iff {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [SigmaFinite ν] (r : ℕ) (F : (Fin (2*r) → ℝ) × Z → ℂ) :
    Integrable (fun p : (Fin r → ℝ × ℝ) × Z => F (realPairFlatten r p.1,p.2))
      ((volume : Measure (Fin r → ℝ × ℝ)).prod ν) ↔
    Integrable F ((volume : Measure (Fin (2*r) → ℝ)).prod ν) :=
  (measurePreserving_realPairFlatten_prod ν r).integrable_comp_emb
    ((realPairFlatten r).prodCongr (MeasurableEquiv.refl Z)).measurableEmbedding

theorem integral_realPairFlatten_prod {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [SigmaFinite ν] (r : ℕ) (F : (Fin (2*r) → ℝ) × Z → ℂ) :
    (∫ p : (Fin r → ℝ × ℝ) × Z, F (realPairFlatten r p.1,p.2)
      ∂((volume : Measure (Fin r → ℝ × ℝ)).prod ν)) =
    ∫ p, F p ∂((volume : Measure (Fin (2*r) → ℝ)).prod ν) :=
  (measurePreserving_realPairFlatten_prod ν r).integral_comp' F

end Paper.SkewOrthogonal
