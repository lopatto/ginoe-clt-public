/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasCoverage
public import GinoeClt.Spectral.CoordinatePolynomialNull
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix
namespace Paper.Spectral

/-- The actual column-major simple-spectrum set has full ordinary Pi volume,
not just full probability under the Gaussian matrix law. -/
theorem ae_mem_simpleSpectrumCells_volume (N : ℕ) :
    ∀ᵐ y ∂(volume : Measure ((Fin N × Fin N) → ℝ)), y ∈ simpleSpectrumCells N := by
  have h := realMvPolynomial_eval_precompose_ne_zero_ae (volume : Measure ℝ)
    (Equiv.prodComm (Fin N) (Fin N)) (matrixCharacteristicResultant N)
    (matrixCharacteristicResultant_ne_zero N)
  filter_upwards [h] with y hy
  exact hy

theorem ae_not_mem_schurAtlasCriticalImage (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ) :
    ∀ᵐ y ∂(volume : Measure (SchurWordCells w)), y ∉ schurAtlasCriticalImage w centers := by
  rw [ae_iff]
  simpa only [not_not, Set.ofPred_mem_eq] using volume_schurAtlasCriticalImage w centers

/-- A single full-volume set covers EVERY positive ordered representation of
each output, not merely almost every output separately for a chosen parameter. -/
theorem ae_schurAtlasSimpleSource_coverage (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i)) :
    ∀ᵐ y ∂(volume : Measure (SchurWordCells w)),
      ∀ p : SchurWordCells w, SchurWordPositive w p → SchurWordOrdered w p →
      ∀ R : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ,
      y = Matrix.vec ((R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) *
        schurWordParameter w p *
        (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ) →
      ∃ z : Fin (m+1) × SchurWordCells w,
        schurAtlasSimpleSource w centers z ∧ schurAtlasCells w centers z = y := by
  filter_upwards [ae_mem_simpleSpectrumCells_volume (schurWordSize w),
    ae_not_mem_schurAtlasCriticalImage w centers] with y hs hn
  intro p hp ho R hy
  exact exists_schurAtlasSimpleSource_of_not_critical w centers hcover p hp ho R y hy hn hs

end Paper.Spectral
