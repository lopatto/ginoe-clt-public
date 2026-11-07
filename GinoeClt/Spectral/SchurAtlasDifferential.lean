/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasRepresentation
@[expose] public section
noncomputable section
open scoped Matrix Kronecker
namespace Paper.Spectral

/-- Actual derivative of each fixed-label translated Schur map. -/
def schurAtlasCellsDerivative (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) (x : SchurWordCells w) :
    SchurWordCells w →L[ℝ] SchurWordCells w :=
  (Matrix.toLin' ((centers i : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) ⊗ₖ
    (centers i : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))).toContinuousLinearMap.comp
      (schurWordChartCellsDerivative w x)

theorem hasStrictFDerivAt_schurAtlasCells (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) (x : SchurWordCells w) :
    HasStrictFDerivAt (fun y => schurAtlasCells w centers (i,y))
      (schurAtlasCellsDerivative w centers i x) x := by
  let L : SchurWordCells w →L[ℝ] SchurWordCells w :=
    (Matrix.toLin' ((centers i : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) ⊗ₖ
      (centers i : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))).toContinuousLinearMap
  have h := L.hasStrictFDerivAt.comp x (hasStrictFDerivAt_schurWordChartCells w x)
  have he : (fun y => schurAtlasCells w centers (i,y)) = L ∘ schurWordChartCells w := by
    funext y
    exact schurAtlasCells_eq_translatedChart w centers (i,y)
  rw [he]
  exact h

theorem det_schurAtlasCellsDerivative (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) (x : SchurWordCells w) :
    LinearMap.det (schurAtlasCellsDerivative w centers i x).toLinearMap =
      LinearMap.det (schurWordChartCellsDerivative w x).toLinearMap := by
  change LinearMap.det ((Matrix.toLin'
    ((centers i : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) ⊗ₖ
      (centers i : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))).comp
        (schurWordChartCellsDerivative w x).toLinearMap) = _
  rw [LinearMap.det_comp,LinearMap.det_toLin',
    det_orthogonalConjugation_kronecker (schurWordSize w) (centers i),one_mul]

theorem abs_det_schurAtlasCellsDerivative (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) (x : SchurWordCells w) :
    |LinearMap.det (schurAtlasCellsDerivative w centers i x).toLinearMap| =
      cayleyAngularJacobian (schurWordSize w) (schurWordOmegaSkew w x) *
        |LinearMap.det (schurWordDifferential w x)| := by
  rw [det_schurAtlasCellsDerivative,abs_det_schurWordChartCellsDerivative]

theorem schurAtlasCellsDerivative_det_ne_zero (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) (x : SchurWordCells w) (hx : schurAtlasSource w centers (i,x)) :
    LinearMap.det (schurAtlasCellsDerivative w centers i x).toLinearMap ≠ 0 := by
  rw [det_schurAtlasCellsDerivative]
  exact schurWordChartCellsDerivative_det_ne_zero w x hx.2.2.2

end Paper.Spectral
