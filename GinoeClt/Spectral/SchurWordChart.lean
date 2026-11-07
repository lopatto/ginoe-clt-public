/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurPhysicalDifferential
public import GinoeClt.Spectral.CayleyAngular

/-! The actual nonlinear Cayley-conjugation map for a fixed scalar/pair word. -/
@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise

namespace Paper.Spectral

/-- The word angular map takes values in the native skew-adjoint module. -/
def schurWordOmegaSkew (w : List Bool) :
    (Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) →ₗ[ℝ]
      SkewMatrix (schurWordSize w) where
  toFun x := ⟨schurWordOmega w x, by
    rw [skewAdjoint.mem_iff]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using schurWordOmega_skew w x⟩
  map_add' x y := Subtype.ext ((schurWordOmega w).map_add x y)
  map_smul' r x := Subtype.ext ((schurWordOmega w).map_smul r x)

@[simp] theorem schurWordOmegaSkew_val (w : List Bool)
    (x : Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) :
    (schurWordOmegaSkew w x : Matrix _ _ ℝ) = schurWordOmega w x := rfl

/-- Literal matrix-valued Schur map, before any sector restriction or fiber assertion. -/
def schurWordChart (w : List Bool)
    (x : Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) :
    Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ :=
  let C := cayleyMatrix (schurWordSize w) (schurWordOmega w x)
  C * schurWordParameter w x * Cᵀ

/-- The ordinary continuous derivative of the actual nonlinear word map. -/
def schurWordChartDerivative (w : List Bool)
    (x : Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) :
    (Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) →L[ℝ]
      Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ :=
  let N := schurWordSize w
  let I := ((1 : Matrix (Fin N) (Fin N) ℝ) - (1 / 2 : ℝ) • schurWordOmega w x)⁻¹
  (conjugationDerivative N (cayleyMatrix N (schurWordOmega w x)) (schurWordParameter w x)).comp
    (((matrixSandwichCLM N I I).comp (schurWordOmega w).toContinuousLinearMap).prod
      (schurWordParameter w).toContinuousLinearMap)

theorem hasStrictFDerivAt_schurWordChart (w : List Bool)
    (x : Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) :
    HasStrictFDerivAt (schurWordChart w) (schurWordChartDerivative w x) x := by
  have hC := (hasStrictFDerivAt_cayleyMatrix_of_skew (schurWordSize w)
    (schurWordOmega w x) (schurWordOmega_skew w x)).comp x
      (schurWordOmega w).toContinuousLinearMap.hasStrictFDerivAt
  have hT := (schurWordParameter w).toContinuousLinearMap.hasStrictFDerivAt (x := x)
  exact (hasStrictFDerivAt_conjugation (schurWordSize w)
    (cayleyMatrix (schurWordSize w) (schurWordOmega w x)) (schurWordParameter w x)).comp x
      (hC.prodMk hT)

/-- The derivative is the actual conjugated commutator, with the honest angular map. -/
theorem schurWordChartDerivative_apply (w : List Bool)
    (x h : Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) :
    let Ω := schurWordOmegaSkew w x
    let g := skewFromCoordinates (schurWordSize w)
      (cayleyAngularEquiv (schurWordSize w) Ω
        (skewCoordinates (schurWordSize w) (schurWordOmegaSkew w h)))
    schurWordChartDerivative w x h =
      cayleyMatrix (schurWordSize w) Ω *
        (schurWordParameter w h + (g : Matrix _ _ ℝ) * schurWordParameter w x -
          schurWordParameter w x * (g : Matrix _ _ ℝ)) *
            (cayleyMatrix (schurWordSize w) Ω)ᵀ := by
  simpa only [schurWordChartDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, LinearMap.coe_toContinuousLinearMap',
    skewFromCoordinates_coordinates, schurWordOmegaSkew_val] using
    cayley_conjugationDerivative_coordinates (schurWordSize w) (schurWordOmegaSkew w x)
      (schurWordParameter w x) (schurWordParameter w h)
      (skewCoordinates (schurWordSize w) (schurWordOmegaSkew w h))

end Paper.Spectral
