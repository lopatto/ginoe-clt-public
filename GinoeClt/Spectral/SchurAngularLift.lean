/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurAngularSection

/-! Lift an honest angular automorphism while leaving the free Schur matrix fixed. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

abbrev SchurWordCells (w : List Bool) :=
  Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ
abbrev SchurWordAngles (w : List Bool) := SkewIndex (schurWordSize w) → ℝ

/-- Ordinary independent lower coordinates of the actual word skew matrix. -/
def schurWordAngleMap (w : List Bool) : SchurWordCells w →ₗ[ℝ] SchurWordAngles w :=
  (skewCoordinateEquiv (schurWordSize w)).symm.toLinearMap.comp (schurWordOmegaSkew w)

/-- The concrete section of the actual angular-coordinate map. -/
def schurWordAngleSection (w : List Bool) : SchurWordAngles w →ₗ[ℝ] SchurWordCells w :=
  (schurWordAngularRightInverse w).comp (skewCoordinateEquiv (schurWordSize w)).toLinearMap

@[simp] theorem schurWordAngleMap_section (w : List Bool) (a : SchurWordAngles w) :
    schurWordAngleMap w (schurWordAngleSection w a) = a := by
  change (skewCoordinateEquiv (schurWordSize w)).symm
    (schurWordOmegaSkew w (schurWordAngularRightInverse w
      (skewCoordinateEquiv (schurWordSize w) a))) = a
  rw [schurWordOmegaSkew_rightInverse, LinearEquiv.symm_apply_apply]

@[simp] theorem schurWordParameter_angleSection (w : List Bool) (a : SchurWordAngles w) :
    schurWordParameter w (schurWordAngleSection w a) = 0 :=
  schurWordParameter_rightInverse w (skewCoordinateEquiv (schurWordSize w) a)

/-- An exact direct-product decomposition from the proved section. -/
def schurWordSplitEquiv (w : List Bool) : SchurWordCells w ≃ₗ[ℝ]
    (SchurWordAngles w × LinearMap.ker (schurWordAngleMap w)) where
  toFun x := (schurWordAngleMap w x,
    ⟨x - schurWordAngleSection w (schurWordAngleMap w x), by
      change schurWordAngleMap w (x - schurWordAngleSection w (schurWordAngleMap w x)) = 0
      rw [map_sub, schurWordAngleMap_section, sub_self]⟩)
  invFun p := schurWordAngleSection w p.1 + p.2
  left_inv x := by
    change schurWordAngleSection w (schurWordAngleMap w x) +
      (x - schurWordAngleSection w (schurWordAngleMap w x)) = x
    abel
  right_inv p := by
    rcases p with ⟨a, ⟨k, hk⟩⟩
    have hk' : schurWordAngleMap w k = 0 := hk
    apply Prod.ext
    · change schurWordAngleMap w (schurWordAngleSection w a + k) = a
      rw [map_add, schurWordAngleMap_section, hk', add_zero]
    · apply Subtype.ext
      change (schurWordAngleSection w a + k) -
        schurWordAngleSection w (schurWordAngleMap w (schurWordAngleSection w a + k)) = k
      rw [map_add, schurWordAngleMap_section, hk', add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact (schurWordAngleMap w).map_add x y
    · apply Subtype.ext
      change (x + y) - schurWordAngleSection w (schurWordAngleMap w (x + y)) =
        (x - schurWordAngleSection w (schurWordAngleMap w x)) +
          (y - schurWordAngleSection w (schurWordAngleMap w y))
      rw [map_add, map_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · exact (schurWordAngleMap w).map_smul r x
    · apply Subtype.ext
      change r • x - schurWordAngleSection w (schurWordAngleMap w (r • x)) =
        r • (x - schurWordAngleSection w (schurWordAngleMap w x))
      rw [map_smul, map_smul, smul_sub]

/-- A genuine full-coordinate automorphism, defined by exact product conjugation. -/
def schurWordAngularLift (w : List Bool) (G : SchurWordAngles w ≃ₗ[ℝ] SchurWordAngles w) :
    SchurWordCells w ≃ₗ[ℝ] SchurWordCells w :=
  (schurWordSplitEquiv w).trans
    ((G.prodCongr (LinearEquiv.refl ℝ (LinearMap.ker (schurWordAngleMap w)))).trans
      (schurWordSplitEquiv w).symm)

theorem schurWordAngularLift_apply (w : List Bool)
    (G : SchurWordAngles w ≃ₗ[ℝ] SchurWordAngles w) (x : SchurWordCells w) :
    schurWordAngularLift w G x =
      schurWordAngleSection w (G (schurWordAngleMap w x)) +
        (x - schurWordAngleSection w (schurWordAngleMap w x)) := rfl

@[simp] theorem schurWordAngleMap_angularLift (w : List Bool)
    (G : SchurWordAngles w ≃ₗ[ℝ] SchurWordAngles w) (x : SchurWordCells w) :
    schurWordAngleMap w (schurWordAngularLift w G x) = G (schurWordAngleMap w x) := by
  rw [schurWordAngularLift_apply, map_add, map_sub,
    schurWordAngleMap_section, schurWordAngleMap_section, sub_self, add_zero]

@[simp] theorem schurWordParameter_angularLift (w : List Bool)
    (G : SchurWordAngles w ≃ₗ[ℝ] SchurWordAngles w) (x : SchurWordCells w) :
    schurWordParameter w (schurWordAngularLift w G x) = schurWordParameter w x := by
  rw [schurWordAngularLift_apply, map_add, map_sub,
    schurWordParameter_angleSection, schurWordParameter_angleSection, zero_add, sub_zero]

/-- The angular lift has exactly the angular signed determinant; the complement is identity. -/
theorem det_schurWordAngularLift (w : List Bool)
    (G : SchurWordAngles w ≃ₗ[ℝ] SchurWordAngles w) :
    LinearMap.det (schurWordAngularLift w G).toLinearMap = LinearMap.det G.toLinearMap := by
  have h : (schurWordAngularLift w G).toLinearMap =
      (schurWordSplitEquiv w).symm.toLinearMap ∘ₗ
        LinearMap.prodMap G.toLinearMap
          (LinearMap.id : LinearMap.ker (schurWordAngleMap w) →ₗ[ℝ]
            LinearMap.ker (schurWordAngleMap w)) ∘ₗ
          (schurWordSplitEquiv w).symm.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  rw [h, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-- The lift transforms the actual skew matrix by the actual angular coordinates. -/
theorem schurWordOmegaSkew_angularLift (w : List Bool)
    (G : SchurWordAngles w ≃ₗ[ℝ] SchurWordAngles w) (x : SchurWordCells w) :
    schurWordOmegaSkew w (schurWordAngularLift w G x) =
      skewCoordinateEquiv (schurWordSize w) (G (schurWordAngleMap w x)) := by
  apply (skewCoordinateEquiv (schurWordSize w)).symm.injective
  change schurWordAngleMap w (schurWordAngularLift w G x) =
    (skewCoordinateEquiv (schurWordSize w)).symm
      (skewCoordinateEquiv (schurWordSize w) (G (schurWordAngleMap w x)))
  rw [schurWordAngleMap_angularLift, LinearEquiv.symm_apply_apply]

theorem schurWordOmega_angularLift (w : List Bool)
    (G : SchurWordAngles w ≃ₗ[ℝ] SchurWordAngles w) (x : SchurWordCells w) :
    schurWordOmega w (schurWordAngularLift w G x) =
      (skewFromCoordinates (schurWordSize w) (G (schurWordAngleMap w x)) : Matrix _ _ ℝ) := by
  have hc (a : SchurWordAngles w) :
      (skewCoordinateEquiv (schurWordSize w) a :
        Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) =
      (skewFromCoordinates (schurWordSize w) a :
        Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) := rfl
  simpa only [schurWordOmegaSkew_val, hc] using
    congrArg (fun M : SkewMatrix (schurWordSize w) =>
      (M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))
      (schurWordOmegaSkew_angularLift w G x)

end Paper.Spectral
