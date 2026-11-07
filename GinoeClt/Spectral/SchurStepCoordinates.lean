/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurBlockDifferential

/-! # Actual square coordinates for a recursive Schur differential step

Input and output order: lower-left, head, tail, upper-right. The map below is
defined by the genuine commutator K + Omega T - T Omega, not by a triangular surrogate.
-/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

abbrev SchurStepIndex (ι κ : Type*) := (ι × κ) ⊕ ((ι × ι) ⊕ ((κ × κ) ⊕ (κ × ι)))

def schurLowerInput {R ι κ : Type*} [Semiring R] :
    (SchurStepIndex ι κ → R) →ₗ[R] Matrix κ ι R where
  toFun x := Matrix.of (fun i j => x (.inl (j, i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def schurHeadInput {R ι κ : Type*} [Semiring R] :
    (SchurStepIndex ι κ → R) →ₗ[R] (ι × ι → R) where
  toFun x p := x (.inr (.inl p))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def schurTailInput {R ι κ : Type*} [Semiring R] :
    (SchurStepIndex ι κ → R) →ₗ[R] (κ × κ → R) where
  toFun x p := x (.inr (.inr (.inl p)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def schurUpperInput {R ι κ : Type*} [Semiring R] :
    (SchurStepIndex ι κ → R) →ₗ[R] Matrix ι κ R where
  toFun x := Matrix.of (fun i j => x (.inr (.inr (.inr (j, i)))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def schurBlockCoordinates {R ι κ : Type*} (M : Matrix (ι ⊕ κ) (ι ⊕ κ) R) :
    SchurStepIndex ι κ → R
  | .inl (j, i) => M (.inr i) (.inl j)
  | .inr (.inl (j, i)) => M (.inl i) (.inl j)
  | .inr (.inr (.inl (j, i))) => M (.inr i) (.inr j)
  | .inr (.inr (.inr (j, i))) => M (.inl i) (.inr j)

def schurStepMap {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (B : Matrix ι ι R) (D : Matrix κ κ R) (U : Matrix ι κ R)
    (omega KB : (ι × ι → R) →ₗ[R] Matrix ι ι R)
    (eta KD : (κ × κ → R) →ₗ[R] Matrix κ κ R)
    (x : SchurStepIndex ι κ → R) : SchurStepIndex ι κ → R :=
  let X : Matrix κ ι R := schurLowerInput x
  let h : ι × ι → R := schurHeadInput x
  let t : κ × κ → R := schurTailInput x
  let KU : Matrix ι κ R := schurUpperInput x
  let T := Matrix.fromBlocks B U 0 D
  let Omega := Matrix.fromBlocks (omega h) (-Xᵀ) X (eta t)
  let K := Matrix.fromBlocks (KB h) KU 0 (KD t)
  schurBlockCoordinates (K + Omega * T - T * Omega)

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
variable (B : Matrix ι ι R) (D : Matrix κ κ R) (U : Matrix ι κ R)
variable (omega KB : (ι × ι → R) →ₗ[R] Matrix ι ι R)
variable (eta KD : (κ × κ → R) →ₗ[R] Matrix κ κ R)

theorem schurStepMap_components (x : SchurStepIndex ι κ → R) :
    schurStepMap B D U omega KB eta KD x =
      let X : Matrix κ ι R := schurLowerInput x
      let h : ι × ι → R := schurHeadInput x
      let t : κ × κ → R := schurTailInput x
      let KU : Matrix ι κ R := schurUpperInput x
      schurBlockCoordinates (Matrix.fromBlocks
        (KB h + omega h * B - B * omega h - U * X)
        (KU + omega h * U - Xᵀ * D + B * Xᵀ - U * eta t)
        (X * B - D * X)
        (KD t + X * U + eta t * D - D * eta t)) := by
  simp only [schurStepMap, schur_commutator_fromBlocks]

def schurStepLinearMap : (SchurStepIndex ι κ → R) →ₗ[R] (SchurStepIndex ι κ → R) where
  toFun := schurStepMap B D U omega KB eta KD
  map_add' x y := by
    rw [schurStepMap_components, schurStepMap_components, schurStepMap_components]
    funext p
    rcases p with p | p | p | p <;>
      simp [schurBlockCoordinates, map_add, Matrix.add_mul, Matrix.mul_add,
        Matrix.transpose_add, Matrix.add_apply, Matrix.sub_apply] <;> abel
  map_smul' r x := by
    rw [schurStepMap_components, schurStepMap_components]
    funext p
    rcases p with p | p | p | p <;>
      simp [schurBlockCoordinates, map_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.transpose_smul, Matrix.smul_apply, smul_eq_mul, mul_add, mul_sub,
        Matrix.add_apply, Matrix.sub_apply]

end Paper.Spectral
