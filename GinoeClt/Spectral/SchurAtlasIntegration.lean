/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasSimpleSpectrum
public import GinoeClt.Spectral.SchurWordMeasurability
public import GinoeClt.Spectral.SchurAtlasDifferential
public import GinoeClt.MeasureTheory.FiniteFamilyFiber
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix ENNReal BigOperators
namespace Paper.Spectral

theorem continuous_schurAtlasCells (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) :
    Continuous (fun x => schurAtlasCells w centers (i,x)) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasStrictFDerivAt_schurAtlasCells w centers i x).continuousAt

theorem measurableSet_schurAtlasSimpleSource (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) :
    MeasurableSet {x : SchurWordCells w | schurAtlasSimpleSource w centers (i,x)} := by
  exact (measurableSet_schurAtlasSource w centers i).inter
    ((measurableSet_simpleSpectrumCells (schurWordSize w)).preimage
      (continuous_schurAtlasCells w centers i).measurable)

/-- Actual finite-family Schur change of variables on the explicitly restricted
regular simple-spectrum image, with the exact physical Jacobian and total multiplicity.
This does not yet identify that image with an entire spectral sector. -/
theorem schurAtlasSimpleSource_lintegral (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (g : SchurWordCells w → ℝ≥0∞) (hg : Measurable g) :
    (∑ i : Fin (m+1), ∫⁻ x in {x | schurAtlasSimpleSource w centers (i,x)},
      ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (schurWordOmegaSkew w x) *
        |LinearMap.det (schurWordDifferential w x)|) *
          g (schurAtlasCells w centers (i,x))) =
      ((2^w.length : ℕ) : ℝ≥0∞) *
        ∫⁻ y in ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
          {x | schurAtlasSimpleSource w centers (i,x)}, g y := by
  have h := Paper.MeasureTheory.sum_lintegral_abs_det_mul_eq_constant_total_fiber
    (volume : Measure (SchurWordCells w))
    (fun i x => schurAtlasCells w centers (i,x))
    (schurAtlasCellsDerivative w centers)
    (fun i => {x | schurAtlasSimpleSource w centers (i,x)})
    (measurableSet_schurAtlasSimpleSource w centers)
    (fun i x _ => hasStrictFDerivAt_schurAtlasCells w centers i x)
    (fun i x hx => schurAtlasCellsDerivative_det_ne_zero w centers i x hx.1)
    (2^w.length)
    (fun y hy => by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using!
        schurAtlasSimpleSource_total_fiber w centers hcover y hy) g hg
  simpa only [abs_det_schurAtlasCellsDerivative] using h

end Paper.Spectral
