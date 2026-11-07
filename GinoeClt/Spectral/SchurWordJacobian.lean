/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurAngularLift
public import GinoeClt.Spectral.ConjugationDeterminant

/-! The genuine full nonlinear Schur-word Jacobian in physical column-row coordinates. -/
@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise Kronecker

namespace Paper.Spectral

/-- The actual nonlinear matrix map in ordinary physical cells. -/
def schurWordChartCells (w : List Bool) (x : SchurWordCells w) : SchurWordCells w :=
  Matrix.vec (schurWordChart w x)

/-- The continuous derivative of the actual cell-valued map. -/
def schurWordChartCellsDerivative (w : List Bool) (x : SchurWordCells w) :
    SchurWordCells w →L[ℝ] SchurWordCells w :=
  ((matrixColumnLinearEquiv ℝ (Fin (schurWordSize w)) (Fin (schurWordSize w))).toLinearMap.toContinuousLinearMap).comp (schurWordChartDerivative w x)

theorem hasStrictFDerivAt_schurWordChartCells (w : List Bool) (x : SchurWordCells w) :
    HasStrictFDerivAt (schurWordChartCells w) (schurWordChartCellsDerivative w x) x :=
  ((matrixColumnLinearEquiv ℝ (Fin (schurWordSize w)) (Fin (schurWordSize w))).toLinearMap.toContinuousLinearMap).hasStrictFDerivAt.comp x (hasStrictFDerivAt_schurWordChart w x)

/-- The exact derivative factors through orthogonal conjugation, the physical
commutator and the honest angular lift. -/
theorem schurWordChartCellsDerivative_decomposition (w : List Bool) (x : SchurWordCells w) :
    (schurWordChartCellsDerivative w x).toLinearMap =
      (Matrix.toLin'
        (cayleyMatrix (schurWordSize w) (schurWordOmega w x) ⊗ₖ
          cayleyMatrix (schurWordSize w) (schurWordOmega w x))) ∘ₗ
        schurWordDifferential w x ∘ₗ
          (schurWordAngularLift w
            (cayleyAngularEquiv (schurWordSize w) (schurWordOmegaSkew w x))).toLinearMap := by
  apply LinearMap.ext
  intro h
  change Matrix.vec (schurWordChartDerivative w x h) =
    (cayleyMatrix (schurWordSize w) (schurWordOmega w x) ⊗ₖ
      cayleyMatrix (schurWordSize w) (schurWordOmega w x)) *ᵥ
        Matrix.vec
          (schurWordParameter w
            (schurWordAngularLift w
              (cayleyAngularEquiv (schurWordSize w) (schurWordOmegaSkew w x)) h) +
            schurWordOmega w
              (schurWordAngularLift w
                (cayleyAngularEquiv (schurWordSize w) (schurWordOmegaSkew w x)) h) *
                  schurWordParameter w x -
            schurWordParameter w x *
              schurWordOmega w
                (schurWordAngularLift w
                  (cayleyAngularEquiv (schurWordSize w) (schurWordOmegaSkew w x)) h))
  rw [Matrix.kronecker_mulVec_vec, schurWordParameter_angularLift, schurWordOmega_angularLift]
  have ha : schurWordAngleMap w h =
      skewCoordinates (schurWordSize w) (schurWordOmegaSkew w h) := rfl
  rw [ha]
  simpa only [schurWordOmegaSkew_val] using
    congrArg (fun M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ => Matrix.vec M)
      (schurWordChartDerivative_apply w x h)

/-- Signed determinant of the actual nonlinear derivative, before sector restriction. -/
theorem det_schurWordChartCellsDerivative (w : List Bool) (x : SchurWordCells w) :
    LinearMap.det (schurWordChartCellsDerivative w x).toLinearMap =
      LinearMap.det (schurWordDifferential w x) *
        LinearMap.det (cayleyAngularEquiv (schurWordSize w) (schurWordOmegaSkew w x)).toLinearMap := by
  let Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ :=
    ⟨cayleyMatrix (schurWordSize w) (schurWordOmega w x),
      (Matrix.mem_orthogonalGroup_iff _ _).mpr
        (cayleyMatrix_orthogonal _ _ (schurWordOmega_skew w x))⟩
  rw [schurWordChartCellsDerivative_decomposition, LinearMap.det_comp,
    LinearMap.det_comp, LinearMap.det_toLin', det_schurWordAngularLift]
  change ((Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) ⊗ₖ
    (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)).det * (_ * _) = _
  rw [det_orthogonalConjugation_kronecker, one_mul]

/-- The actual absolute Jacobian is the angular density times the physical
commutator determinant. No invertibility of that commutator is assumed. -/
theorem abs_det_schurWordChartCellsDerivative (w : List Bool) (x : SchurWordCells w) :
    |LinearMap.det (schurWordChartCellsDerivative w x).toLinearMap| =
      cayleyAngularJacobian (schurWordSize w) (schurWordOmegaSkew w x) *
        |LinearMap.det (schurWordDifferential w x)| := by
  rw [det_schurWordChartCellsDerivative, abs_mul, mul_comm]
  rfl

end Paper.Spectral
