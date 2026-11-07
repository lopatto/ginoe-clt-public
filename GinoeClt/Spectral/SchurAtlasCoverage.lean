/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasIntegration
public import GinoeClt.Spectral.SchurWordMeasure
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix
namespace Paper.Spectral

/-- Actual critical OUTPUTS of all translated charts; no parameter nullity shortcut. -/
def schurAtlasCriticalImage (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ) :
    Set (SchurWordCells w) :=
  ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
    {x | LinearMap.det (schurWordDifferential w x) = 0}

theorem volume_schurAtlasCriticalImage (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ) :
    volume (schurAtlasCriticalImage w centers) = 0 := by
  apply measure_iUnion_null_iff.mpr
  intro i
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (f' := schurAtlasCellsDerivative w centers i) volume
  · intro x _
    exact (hasStrictFDerivAt_schurAtlasCells w centers i x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    change LinearMap.det (schurAtlasCellsDerivative w centers i x).toLinearMap = 0
    rw [det_schurAtlasCellsDerivative,det_schurWordChartCellsDerivative,hx,zero_mul]

/-- Arbitrary positive ordered physical parameters and an arbitrary frame are
covered by the actual regular assigned source outside the proved null critical image.
No input regularity or strict-pair assumption is imposed. -/
theorem exists_schurAtlasSimpleSource_of_not_critical (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (p : SchurWordCells w) (hp : SchurWordPositive w p) (ho : SchurWordOrdered w p)
    (R : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (y : SchurWordCells w)
    (hy : y = Matrix.vec ((R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) *
      schurWordParameter w p * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ))
    (hn : y ∉ schurAtlasCriticalImage w centers)
    (hs : y ∈ simpleSpectrumCells (schurWordSize w)) :
    ∃ z : Fin (m+1) × SchurWordCells w,
      schurAtlasSimpleSource w centers z ∧ schurAtlasCells w centers z = y := by
  obtain ⟨b,hb,_⟩ := existsUnique_boundedAngularPair centers hcover
    (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)
    ((Matrix.mem_orthogonalGroup_iff _ _).mp R.property)
  obtain ⟨q,hangle,hK⟩ := exists_schurWord_angle_parameter w p b.2
  have hsem := schurWord_source_congr_parameter w q p hK
  have hR : schurAtlasFrame w centers (b.1,q) = R := by
    change boundedAngularFrame (schurWordSize w) (centers b.1) (schurWordAngleMap w q) = R
    rw [hangle]
    exact hb.2
  have hout : schurAtlasCells w centers (b.1,q) = y := by
    rw [hy]
    simp only [schurAtlasCells,schurAtlasMatrix,hR,hK]
  have hd : LinearMap.det (schurWordDifferential w q) ≠ 0 := by
    intro he
    apply hn
    exact Set.mem_iUnion.mpr ⟨b.1,q,he,hout⟩
  refine ⟨(b.1,q),⟨⟨?_,hsem.1.mpr hp,hsem.2.1.mpr ho,hd⟩,?_⟩,hout⟩
  · change schurWordAngleMap w q ∈ boundedAngularPiece centers b.1
    rw [hangle]
    exact hb.1
  · rw [hout]
    exact hs

end Paper.Spectral
