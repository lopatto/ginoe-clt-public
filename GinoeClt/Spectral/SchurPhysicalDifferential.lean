/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurWord

/-! Determinants of the genuine commutator in ordinary physical matrix cells. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

variable {d m : ℕ}

def schurPhysicalBlock (B : Matrix (Fin d) (Fin d) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (U : Matrix (Fin d) (Fin m) ℝ) :
    Matrix (Fin (d + m)) (Fin (d + m)) ℝ :=
  (Matrix.fromBlocks B U 0 D).reindex finSumFinEquiv finSumFinEquiv

@[simp] theorem schurPhysicalBlock_submatrix
    (B : Matrix (Fin d) (Fin d) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) :
    (schurPhysicalBlock B D U).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks B U 0 D := by
  ext i j
  simp [schurPhysicalBlock, Matrix.reindex_apply]

@[simp] theorem schurOmegaPhysical_submatrix
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (x : Fin (d + m) × Fin (d + m) → ℝ) :
    (schurOmegaPhysical d m ω η x).submatrix finSumFinEquiv finSumFinEquiv =
      schurOmegaStep ω η (schurCellCoordinateEquiv ℝ d m x) := by
  ext i j
  simp [schurOmegaPhysical, Matrix.reindex_apply]

@[simp] theorem schurParameterPhysical_submatrix
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (x : Fin (d + m) × Fin (d + m) → ℝ) :
    (schurParameterPhysical d m K L x).submatrix finSumFinEquiv finSumFinEquiv =
      schurParameterStep K L (schurCellCoordinateEquiv ℝ d m x) := by
  ext i j
  simp [schurParameterPhysical, Matrix.reindex_apply]

variable (B : Matrix (Fin d) (Fin d) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
variable (U : Matrix (Fin d) (Fin m) ℝ)
variable (ω K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
variable (η L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)

theorem schurPhysicalLinearMap_conj :
    (schurCellCoordinateEquiv ℝ d m).toLinearMap ∘ₗ
      schurDiagonalLinearMap (schurPhysicalBlock B D U)
        (schurOmegaPhysical d m ω η) (schurParameterPhysical d m K L) ∘ₗ
          (schurCellCoordinateEquiv ℝ d m).symm.toLinearMap =
      schurStepLinearMap B D U ω K η L := by
  apply LinearMap.ext
  intro x
  change schurCellCoordinateEquiv ℝ d m (Matrix.vec
    (schurParameterPhysical d m K L ((schurCellCoordinateEquiv ℝ d m).symm x) +
      schurOmegaPhysical d m ω η ((schurCellCoordinateEquiv ℝ d m).symm x) *
        schurPhysicalBlock B D U - schurPhysicalBlock B D U *
          schurOmegaPhysical d m ω η ((schurCellCoordinateEquiv ℝ d m).symm x))) =
    schurStepMap B D U ω K η L x
  rw [← schurBlockCoordinates_physicalCells]
  let ρ := Matrix.reindexRingEquiv ℝ (finSumFinEquiv.symm : Fin (d + m) ≃ Fin d ⊕ Fin m)
  have hρ (M : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) :
      M.submatrix finSumFinEquiv finSumFinEquiv = ρ M := rfl
  rw [hρ, map_sub, map_add, map_mul, map_mul]
  change schurBlockCoordinates
    (((schurParameterPhysical d m K L ((schurCellCoordinateEquiv ℝ d m).symm x)).submatrix
      finSumFinEquiv finSumFinEquiv) +
      ((schurOmegaPhysical d m ω η ((schurCellCoordinateEquiv ℝ d m).symm x)).submatrix
        finSumFinEquiv finSumFinEquiv) *
          ((schurPhysicalBlock B D U).submatrix finSumFinEquiv finSumFinEquiv) -
      ((schurPhysicalBlock B D U).submatrix finSumFinEquiv finSumFinEquiv) *
        ((schurOmegaPhysical d m ω η ((schurCellCoordinateEquiv ℝ d m).symm x)).submatrix
          finSumFinEquiv finSumFinEquiv)) = _
  simp only [schurParameterPhysical_submatrix, schurOmegaPhysical_submatrix,
    schurPhysicalBlock_submatrix, LinearEquiv.apply_symm_apply]
  rfl

/-- Signed determinant of the actual physical-cell commutator. -/
theorem det_schurPhysicalLinearMap :
    LinearMap.det (schurDiagonalLinearMap (schurPhysicalBlock B D U)
      (schurOmegaPhysical d m ω η) (schurParameterPhysical d m K L)) =
      (sylvesterMatrix D B).det *
        LinearMap.det (schurDiagonalLinearMap B ω K) *
          LinearMap.det (schurDiagonalLinearMap D η L) := by
  have h := congrArg LinearMap.det (schurPhysicalLinearMap_conj B D U ω K η L)
  rw [det_schurCellCoordinate_conj] at h
  rw [h]
  simpa only [schurStepCoefficientMatrix, LinearMap.det_toMatrix'] using
    det_schurStepLinearMap B D U ω K η L

/-- The physical block parameter is the actual assembled block matrix. -/
theorem schurParameterPhysical_eq (x : Fin (d + m) × Fin (d + m) → ℝ) :
    schurParameterPhysical d m K L x =
      schurPhysicalBlock
        (K (schurHeadInput (schurCellCoordinateEquiv ℝ d m x)))
        (L (schurTailInput (schurCellCoordinateEquiv ℝ d m x)))
        (schurUpperInput (schurCellCoordinateEquiv ℝ d m x)) := rfl

/-- The signed factorization at an actual free-parameter point. -/
theorem det_schurParameterPhysicalLinearMap
    (x : Fin (d + m) × Fin (d + m) → ℝ) :
    LinearMap.det (schurDiagonalLinearMap (schurParameterPhysical d m K L x)
      (schurOmegaPhysical d m ω η) (schurParameterPhysical d m K L)) =
      (sylvesterMatrix
        (L (schurTailInput (schurCellCoordinateEquiv ℝ d m x)))
        (K (schurHeadInput (schurCellCoordinateEquiv ℝ d m x)))).det *
        LinearMap.det (schurDiagonalLinearMap
          (K (schurHeadInput (schurCellCoordinateEquiv ℝ d m x))) ω K) *
          LinearMap.det (schurDiagonalLinearMap
            (L (schurTailInput (schurCellCoordinateEquiv ℝ d m x))) η L) := by
  rw [schurParameterPhysical_eq K L x]
  exact det_schurPhysicalLinearMap _ _ _ ω K η L

/-- Genuine commutator at the free matrix specified by a fixed block word. -/
def schurWordDifferential (w : List Bool)
    (p : Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) :=
  schurDiagonalLinearMap (schurWordParameter w p)
    (schurWordOmega w) (schurWordParameter w)

theorem det_schurWordDifferential_nil (p : Fin 0 × Fin 0 → ℝ) :
    LinearMap.det (schurWordDifferential [] p) = 1 := by
  rw [← LinearMap.det_toMatrix']
  let : IsEmpty (Fin (schurWordSize []) × Fin (schurWordSize [])) :=
    inferInstanceAs (IsEmpty (Fin 0 × Fin 0))
  exact Matrix.det_isEmpty

theorem det_schurWordDifferential_false (w : List Bool)
    (p : Fin (1 + schurWordSize w) × Fin (1 + schurWordSize w) → ℝ) :
    let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
    let h := schurHeadInput x
    let t := schurTailInput x
    LinearMap.det (schurWordDifferential (false :: w) p) =
      (sylvesterMatrix (schurWordParameter w t) (scalarBlock (h (0, 0)))).det *
        LinearMap.det (schurWordDifferential w t) := by
  dsimp only
  change LinearMap.det (schurDiagonalLinearMap
    (schurParameterPhysical 1 (schurWordSize w) scalarHeadParameter (schurWordParameter w) p)
    (schurOmegaPhysical 1 (schurWordSize w) 0 (schurWordOmega w))
    (schurParameterPhysical 1 (schurWordSize w) scalarHeadParameter (schurWordParameter w))) = _
  rw [det_schurParameterPhysicalLinearMap]
  change _ * LinearMap.det (schurDiagonalLinearMap (scalarBlock (R := ℝ) _) 0 scalarHeadParameter) * _ = _
  rw [← LinearMap.det_toMatrix', det_scalarHead, mul_one]
  rfl

theorem det_schurWordDifferential_true (w : List Bool)
    (p : Fin (2 + schurWordSize w) × Fin (2 + schurWordSize w) → ℝ) :
    let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
    let h := schurHeadInput x
    let t := schurTailInput x
    LinearMap.det (schurWordDifferential (true :: w) p) =
      (sylvesterMatrix (schurWordParameter w t)
        (schurBlock (h (0, 0)) (h (0, 1)) (h (1, 0)))).det *
          (2 * (h (0, 1) - h (1, 0))) *
            LinearMap.det (schurWordDifferential w t) := by
  dsimp only
  change LinearMap.det (schurDiagonalLinearMap
    (schurParameterPhysical 2 (schurWordSize w) pairHeadParameter (schurWordParameter w) p)
    (schurOmegaPhysical 2 (schurWordSize w) pairHeadOmega (schurWordOmega w))
    (schurParameterPhysical 2 (schurWordSize w) pairHeadParameter (schurWordParameter w))) = _
  rw [det_schurParameterPhysicalLinearMap]
  change _ * LinearMap.det (schurDiagonalLinearMap (schurBlock _ _ _) pairHeadOmega pairHeadParameter) * _ = _
  rw [← LinearMap.det_toMatrix', det_pairHead]
  rfl

end Paper.Spectral
